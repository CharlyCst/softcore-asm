//! Procedural Macro Parser

use quote::quote;
use syn::{
    Expr, ExprMacro, Ident, Lit, LitStr, Path, Token,
    parse::{Parse, ParseStream, Parser, Result},
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
    pub input_expr: Option<Expr>,
    pub output_expr: Option<Expr>,
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

    // Parse the first expression
    let first_expr = input.parse::<Expr>()?;

    // Check for => (fat arrow) - only valid for inout
    let (input_expr, output_expr) = if input.peek(Token![=>]) {
        if !matches!(direction, Direction::InOut) {
            return Err(input.error("=> syntax only valid for inout operands"));
        }
        input.parse::<Token![=>]>()?;
        let second_expr = input.parse::<Expr>()?;
        (Some(first_expr), Some(second_expr))
    } else {
        // Single expression - use based on direction
        match direction {
            Direction::In => (Some(first_expr), None),
            Direction::Out => (None, Some(first_expr)),
            Direction::InOut => (Some(first_expr.clone()), Some(first_expr)),
        }
    };

    Ok(OperandKind::Register(KindRegister {
        reg,
        input_expr,
        output_expr,
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

        // Parse template items (either LitStr or concat!)
        loop {
            // Try to parse a template item
            if input.peek(LitStr) {
                template.push(input.parse::<LitStr>()?);
            } else if input.peek(Ident) && input.fork().parse::<Ident>().unwrap() == "concat" {
                let mac: ExprMacro = input.parse()?;
                let concatenated = evaluate_concat(&mac)?;
                template.push(LitStr::new(&concatenated, mac.mac.bang_token.span));
            } else {
                // Not a template item, exit loop
                break;
            }

            // If there's a comma, consume it and continue to next iteration
            // (the next iteration will check if it's another template item)
            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            } else {
                break;
            }
        }

        let mut operands = Vec::new();
        let mut options = Vec::new();

        while !input.is_empty() {
            // Skip any leading commas
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

// —————————————————————————— Nested Macro Support —————————————————————————— //

/// Evaluates a single literal expression to a string
fn evaluate_literal_expr(expr: &Expr) -> Result<String> {
    match expr {
        Expr::Lit(lit) => match &lit.lit {
            Lit::Str(s) => Ok(s.value()),
            Lit::Int(i) => Ok(i.base10_digits().to_string()),
            Lit::Char(c) => Ok(c.value().to_string()),
            Lit::Bool(b) => Ok(b.value.to_string()),
            _ => Err(syn::Error::new_spanned(
                lit,
                format!(
                    "concat! only supports string, integer, char, and boolean literals, found: {}",
                    quote::quote!(#lit)
                ),
            )),
        },
        Expr::Group(group) => {
            // Handle grouped expressions from macro_rules! substitution
            evaluate_literal_expr(&group.expr)
        }
        Expr::Path(path) => Err(syn::Error::new_spanned(
            path,
            format!(
                "concat! in proc macros requires all arguments to be literals, found variable: {}",
                quote::quote!(#path)
            ),
        )),
        _ => Err(syn::Error::new_spanned(
            expr,
            format!(
                "concat! only supports literals in proc macros, found: {}",
                quote::quote!(#expr)
            ),
        )),
    }
}

/// Evaluates a `concat!` macro call at proc macro expansion time
fn evaluate_concat(mac: &ExprMacro) -> Result<String> {
    // Verify this is actually a concat! macro
    if !mac.mac.path.is_ident("concat") {
        return Err(syn::Error::new_spanned(
            &mac.mac.path,
            "Expected `concat!` macro",
        ));
    }

    let tokens = mac.mac.tokens.clone();
    let parser = syn::punctuated::Punctuated::<Expr, Token![,]>::parse_terminated;
    let exprs = parser.parse2(tokens)?;

    let mut result = String::new();
    for expr in exprs {
        let part = evaluate_literal_expr(&expr)?;
        result.push_str(&part);
    }

    Ok(result)
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
        assert!(parsed.input_expr.is_some());
        assert!(parsed.output_expr.is_none());

        // Testing output direction
        let tokens = quote! {out(reg) foo};
        let parsed = syn::parse2::<RegisterOperand>(tokens)
            .unwrap()
            .into_register()
            .unwrap();
        assert!(parsed.input_expr.is_none());
        assert!(parsed.output_expr.is_some());

        // Testing inout direction
        let tokens = quote! {inout(reg) foo};
        let parsed = syn::parse2::<RegisterOperand>(tokens)
            .unwrap()
            .into_register()
            .unwrap();
        assert!(parsed.input_expr.is_some());
        assert!(parsed.output_expr.is_some());
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
        assert!(parsed.input_expr.is_some());
        assert!(parsed.output_expr.is_none());
        match parsed.input_expr.unwrap() {
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
        assert!(parsed.input_expr.is_some());
        assert!(parsed.output_expr.is_none());
        match parsed.input_expr.unwrap() {
            Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Int(_),
                ..
            }) => {}
            _ => panic!("Expected an integer literal"),
        }
    }

    #[test]
    fn register_operand_inout_with_arrow() {
        // Test inout with separate input and output variables
        let tokens = quote! {inout(reg) input_var => output_var};
        let parsed = syn::parse2::<RegisterOperand>(tokens)
            .unwrap()
            .into_register()
            .unwrap();

        assert!(parsed.input_expr.is_some());
        assert!(parsed.output_expr.is_some());

        // Check input expression
        match parsed.input_expr.as_ref().unwrap() {
            Expr::Path(path) => {
                let ident = path.path.get_ident().unwrap();
                assert_eq!(ident.to_string(), "input_var");
            }
            _ => panic!("Expected input_var identifier"),
        }

        // Check output expression
        match parsed.output_expr.as_ref().unwrap() {
            Expr::Path(path) => {
                let ident = path.path.get_ident().unwrap();
                assert_eq!(ident.to_string(), "output_var");
            }
            _ => panic!("Expected output_var identifier"),
        }

        // Test that => is only valid for inout
        let tokens = quote! {in(reg) input_var => output_var};
        assert!(syn::parse2::<RegisterOperand>(tokens).is_err());

        let tokens = quote! {out(reg) input_var => output_var};
        assert!(syn::parse2::<RegisterOperand>(tokens).is_err());
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

    #[test]
    fn concat_evaluation() {
        // Test simple string concatenation
        let tokens = quote! { concat!("hello", " ", "world") };
        let mac = syn::parse2::<ExprMacro>(tokens).unwrap();
        let result = evaluate_concat(&mac).unwrap();
        assert_eq!(result, "hello world");

        // Test concatenation with integers
        let tokens = quote! { concat!("csrw pmpaddr", 0, ", {addr}") };
        let mac = syn::parse2::<ExprMacro>(tokens).unwrap();
        let result = evaluate_concat(&mac).unwrap();
        assert_eq!(result, "csrw pmpaddr0, {addr}");

        // Test concatenation with multiple integers
        let tokens = quote! { concat!("test", 1, 2, 3) };
        let mac = syn::parse2::<ExprMacro>(tokens).unwrap();
        let result = evaluate_concat(&mac).unwrap();
        assert_eq!(result, "test123");

        // Test concatenation with char
        let tokens = quote! { concat!("value: ", 'x') };
        let mac = syn::parse2::<ExprMacro>(tokens).unwrap();
        let result = evaluate_concat(&mac).unwrap();
        assert_eq!(result, "value: x");
    }

    #[test]
    fn concat_in_asm_input() {
        // Test concat! as template
        let tokens = quote! {
            concat!("csrw pmpaddr", 0, ", {addr}"),
            addr = in(reg) pmpaddr,
            options(nomem)
        };
        let parsed = syn::parse2::<AsmInput>(tokens).unwrap();
        assert_eq!(parsed.template.len(), 1);
        assert_eq!(parsed.template[0].value(), "csrw pmpaddr0, {addr}");
        assert_eq!(parsed.operands.len(), 2);

        // Test multiple template strings, some with concat!
        let tokens = quote! {
            "li {tmp}, 0x80",
            concat!("csrw pmpaddr", 1, ", {addr}"),
            addr = in(reg) pmpaddr,
            tmp = out(reg) _,
            options(nomem)
        };
        let parsed = syn::parse2::<AsmInput>(tokens).unwrap();
        assert_eq!(parsed.template.len(), 2);
        assert_eq!(parsed.template[0].value(), "li {tmp}, 0x80");
        assert_eq!(parsed.template[1].value(), "csrw pmpaddr1, {addr}");
    }
}
