use quote::quote;
use syn::{
    Expr, Ident, LitStr, Token,
    parse::{Parse, ParseStream, Result},
};

// ———————————————————————— Macro Syntax Definition ————————————————————————— //

pub struct AsmInput {
    pub template: LitStr,
    pub operands: Vec<AsmOperand>,
    pub options: Vec<String>,
}

#[derive(Clone)]
pub enum AsmOperand {
    Register(RegisterOperand),
    Options(Expr),
}

#[derive(Clone)]
pub struct RegisterOperand {
    pub ident: Option<Ident>,
    pub reg: Ident,
    pub expr: Expr,
    pub is_input: bool,
    pub is_output: bool,
}

// —————————————————————————————— Macro Parser —————————————————————————————— //

impl Parse for RegisterOperand {
    fn parse(input: ParseStream) -> Result<Self> {
        let ident;
        let is_input;
        let is_output;

        // Check if this operand is given an identifier:
        // ident = in(reg) expr
        if input.peek(Ident) && input.peek2(Token![=]) {
            ident = Some(input.parse::<Ident>()?);
            input.parse::<Token![=]>()?;
        } else {
            ident = None;
        }

        // Now parse the `[in|out|inout](reg)` part
        if input.peek(Token![in]) {
            input.parse::<Token![in]>()?;
            is_input = true;
            is_output = false;
        } else if input.peek(Ident) && input.peek2(syn::token::Paren) {
            let ident = input.parse::<Ident>()?;
            match ident.to_string().as_str() {
                "out" => {
                    is_input = false;
                    is_output = true;
                }
                "inout" => {
                    is_input = true;
                    is_output = true;
                }
                _ => return Err(input.error("Expected operand specification after name =")),
            }
        } else {
            return Err(input.error("Expected direction specification after name ="));
        };

        // And finally parse the target register and expression
        let content;
        syn::parenthesized!(content in input);
        let reg = content.parse::<Ident>()?;
        let expr = input.parse::<Expr>()?;

        Ok(RegisterOperand {
            ident,
            reg,
            expr,
            is_input,
            is_output,
        })
    }
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
        } else {
            Ok(AsmOperand::Register(input.parse::<RegisterOperand>()?))
        }
    }
}

impl Parse for AsmInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let template = input.parse::<LitStr>()?;

        let mut operands = Vec::new();
        let mut options = Vec::new();

        while !input.is_empty() {
            input.parse::<Token![,]>()?;
            if input.is_empty() {
                break;
            }
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

    #[test]
    fn register_operand() {
        todo!()
    }
}
