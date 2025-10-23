//! Procedural Macro Parser

use quote::quote;
use syn::{
    Expr, Ident, Lit, LitStr, Path, Token,
    parse::{Parse, ParseStream, Result},
};

// ———————————————————————— Macro Syntax Definition ————————————————————————— //

pub struct AsmInput {
    pub template: Vec<LitStr>,
    pub operands: Vec<AsmOperand>,
    #[allow(dead_code)]
    pub options: Vec<String>,
}

#[derive(Clone)]
pub enum AsmOperand {
    Register(RegisterOperand),
    Options(Expr),
    /// A function that expose the core to operate on
    Softcore(Expr),
}

#[derive(Clone)]
pub struct RegisterOperand {
    pub ident: Option<Ident>,
    pub kind: OperandKind,
}

#[derive(Clone)]
pub enum OperandKind {
    Register(KindRegister),
    Symbol { path: Path },
    Const(Expr),
}

#[derive(Clone)]
pub struct KindRegister {
    #[allow(unused)]
    pub reg: RegisterKind,
    pub expr: Expr,
    pub is_input: bool,
    pub is_output: bool,
}

#[derive(Clone)]
pub enum RegisterKind {
    Ident(Ident),
    String(String),
}

pub enum Direction {
    In,
    Out,
    InOut,
}

// —————————————————————————————— Macro Parser —————————————————————————————— //

impl Parse for RegisterOperand {
    fn parse(input: ParseStream) -> Result<Self> {
        let ident;

        // Check if this operand is given an identifier:
        // ident = in(reg) expr
        if input.peek(Ident) && input.peek2(Token![=]) {
            ident = Some(input.parse::<Ident>()?);
            input.parse::<Token![=]>()?;
        } else {
            ident = None;
        }

        // Check which kind of operand that is and forward to the appropriate parser
        let kind = if input.peek(Token![in]) {
            input.parse::<Token![in]>()?;
            parse_operand_kind_register(Direction::In, &input)?
        } else if input.peek(Token![const]) {
            input.parse::<Token![const]>()?;
            parse_operand_kind_const(&input)?
        } else if input.peek(Ident) {
            let ident = input.parse::<Ident>()?;
            match ident.to_string().as_str() {
                "out" => parse_operand_kind_register(Direction::Out, &input)?,
                "inout" => parse_operand_kind_register(Direction::InOut, &input)?,
                "sym" => parse_operand_kind_symbol(&input)?,
                _ => return Err(input.error("Expected operand specification after name =")),
            }
        } else {
            return Err(input.error("Expected direction specification after name ="));
        };

        Ok(RegisterOperand { ident, kind })
    }
}

fn parse_operand_kind_register(direction: Direction, input: &ParseStream) -> Result<OperandKind> {
    let (is_input, is_output) = match direction {
        Direction::In => (true, false),
        Direction::Out => (false, true),
        Direction::InOut => (true, true),
    };
    let content;
    syn::parenthesized!(content in input);
    let reg = if content.peek(Ident) {
        RegisterKind::Ident(content.parse::<Ident>()?)
    } else if content.peek(Lit) {
        let reg = content.parse::<Lit>()?;
        match reg {
            Lit::Str(lit_str) => RegisterKind::String(lit_str.value()),
            _ => {
                return Err(content.error("Expected a valid register"));
            }
        }
    } else {
        return Err(input.error("Invalid register name"));
    };
    let expr = input.parse::<Expr>()?;

    Ok(OperandKind::Register(KindRegister {
        reg,
        expr,
        is_input,
        is_output,
    }))
}

fn parse_operand_kind_symbol(input: &ParseStream) -> Result<OperandKind> {
    let path = input.parse::<Path>()?;
    Ok(OperandKind::Symbol { path })
}

fn parse_operand_kind_const(input: &ParseStream) -> Result<OperandKind> {
    let expr = input.parse::<Expr>()?;
    Ok(OperandKind::Const(expr))
}

impl Parse for AsmOperand {
    fn parse(input: ParseStream) -> Result<Self> {
        if input.peek(Ident) && input.fork().parse::<Ident>().unwrap() == "options" {
            input.parse::<Ident>()?; // consume "options"
            let content;
            syn::parenthesized!(content in input);
            // Parse the entire content as a single expression (handles comma-separated,values)
            let remaining_tokens = content.parse::<proc_macro2::TokenStream>()?;
            let expr: Expr = syn::parse2(quote! { (#remaining_tokens) })?;
            Ok(AsmOperand::Options(expr))
        } else if input.peek(Ident) && input.fork().parse::<Ident>().unwrap() == "softcore" {
            input.parse::<Ident>()?; // consume "options"
            let content;
            syn::parenthesized!(content in input);
            Ok(AsmOperand::Softcore(content.parse::<Expr>()?))
        } else {
            Ok(AsmOperand::Register(input.parse::<RegisterOperand>()?))
        }
    }
}

impl Parse for AsmInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let mut template = Vec::new();
        template.push(input.parse::<LitStr>()?);
        while input.peek(Token![,]) && input.peek2(LitStr) {
            input.parse::<Token![,]>()?;
            template.push(input.parse::<LitStr>()?);
        }

        let mut operands = Vec::new();
        let mut options = Vec::new();

        while !input.is_empty() {
            // We parse at least one column, but more if needed
            input.parse::<Token![,]>()?;
            while !input.is_empty() && input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            }
            if input.is_empty() {
                break;
            }

            // Now we can process the next operand
            let operand = input.parse::<AsmOperand>()?;
            if let AsmOperand::Options(Expr::Tuple(tuple)) = &operand {
                for elem in &tuple.elems {
                    if let Expr::Path(path) = elem
                        && let Some(ident) = path.path.get_ident()
                    {
                        options.push(ident.to_string());
                    }
                }
            }
            operands.push(operand);
        }

        Ok(AsmInput {
            template,
            operands,
            options,
        })
    }
}

// ————————————————————————————————— Tests —————————————————————————————————— //

#[cfg(test)]
mod tests {
    use super::*;

    // Some small helpers
    impl RegisterOperand {
        fn into_register(self) -> Option<KindRegister> {
            match self.kind {
                OperandKind::Register(reg) => Some(reg),
                _ => None,
            }
        }
    }

    #[test]
    fn register_operand_direction() {
        // Testing input direction
        let tokens = quote! {in(reg) foo};
        let parsed = syn::parse2::<RegisterOperand>(tokens)
            .unwrap()
            .into_register()
            .unwrap();
        assert!(parsed.is_input);
        assert!(!parsed.is_output);

        // Testing output direction
        let tokens = quote! {out(reg) foo};
        let parsed = syn::parse2::<RegisterOperand>(tokens)
            .unwrap()
            .into_register()
            .unwrap();
        assert!(!parsed.is_input);
        assert!(parsed.is_output);

        // Testing inout direction
        let tokens = quote! {inout(reg) foo};
        let parsed = syn::parse2::<RegisterOperand>(tokens)
            .unwrap()
            .into_register()
            .unwrap();
        assert!(parsed.is_input);
        assert!(parsed.is_output);
    }

    #[test]
    fn register_operand_ident() {
        let tokens = quote! {in(reg) foo};
        let parsed = syn::parse2::<RegisterOperand>(tokens).unwrap();
        assert_eq!(parsed.ident, None);

        let tokens = quote! {bar = in(reg) foo};
        let parsed = syn::parse2::<RegisterOperand>(tokens).unwrap();
        assert!(parsed.ident.is_some());
        assert_eq!(parsed.ident.unwrap().to_string(), "bar");
    }

    #[test]
    fn register_operand_expr() {
        let tokens = quote! {in(reg) foo};
        let parsed = syn::parse2::<RegisterOperand>(tokens)
            .unwrap()
            .into_register()
            .unwrap();
        match parsed.expr {
            Expr::Path(path) => {
                let ident = path.path.get_ident().unwrap();
                assert_eq!(ident.to_string(), "foo");
            }
            _ => panic!("Expected an identifier (path of lenght 1)"),
        }

        let tokens = quote! {in(reg) 0xbeef};
        let parsed = syn::parse2::<RegisterOperand>(tokens)
            .unwrap()
            .into_register()
            .unwrap();
        match parsed.expr {
            Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Int(_),
                ..
            }) => {}
            _ => panic!("Expected an integer literal"),
        }
    }

    #[test]
    fn asm_operand() {
        let tokens = quote! {in(reg) 0xbeef};
        syn::parse2::<AsmOperand>(tokens).unwrap();

        let tokens = quote! {options(nomem)};
        syn::parse2::<AsmOperand>(tokens).unwrap();

        let tokens = quote! {softcore(path::to::function)};
        syn::parse2::<AsmOperand>(tokens).unwrap();
    }

    #[test]
    fn asm_input() {
        let tokens = quote! { "wfi" };
        syn::parse2::<AsmInput>(tokens).unwrap();

        let tokens = quote! {
            "csrrw {prev}, mscratch, {x}
            csrrw {final_val}, mscratch, x0",
            x = in(reg) value,
            prev = out(reg) prev_value,
            final_val = out(reg) final_value,
            options(nomem)
        };
        syn::parse2::<AsmInput>(tokens).unwrap();
    }
}
