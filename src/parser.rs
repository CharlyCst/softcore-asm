use quote::quote;
use syn::{
    Expr, Ident, LitStr, Token,
    parse::{Parse, ParseStream, Result},
};

#[derive(Clone)]
pub enum AsmOperand {
    Input {
        name: Option<Ident>,
        reg: Ident,
        expr: Expr,
    },
    Output {
        name: Option<Ident>,
        reg: Ident,
        expr: Expr,
    },
    InOut {
        name: Option<Ident>,
        reg: Ident,
        expr: Expr,
    },
    Options(Expr),
    Raw(Expr),
}

pub struct AsmInput {
    pub template: LitStr,
    pub operands: Vec<AsmOperand>,
    pub options: Vec<String>,
}

impl Parse for AsmOperand {
    fn parse(input: ParseStream) -> Result<Self> {
        // Check for named operand: "name = direction(reg) expr"
        if input.peek(Ident) && input.peek2(Token![=]) {
            let name = input.parse::<Ident>()?;
            input.parse::<Token![=]>()?;

            // Now parse the direction(reg) expr part
            if input.peek(Token![in]) {
                input.parse::<Token![in]>()?;
                let content;
                syn::parenthesized!(content in input);
                let reg = content.parse::<Ident>()?;
                let expr = input.parse::<Expr>()?;
                Ok(AsmOperand::Input {
                    name: Some(name),
                    reg,
                    expr,
                })
            } else if input.peek(Ident) && input.peek2(syn::token::Paren) {
                let ident = input.parse::<Ident>()?;
                match ident.to_string().as_str() {
                    "out" => {
                        let content;
                        syn::parenthesized!(content in input);
                        let reg = content.parse::<Ident>()?;
                        let expr = input.parse::<Expr>()?;
                        Ok(AsmOperand::Output {
                            name: Some(name),
                            reg,
                            expr,
                        })
                    }
                    "inout" => {
                        let content;
                        syn::parenthesized!(content in input);
                        let reg = content.parse::<Ident>()?;
                        let expr = input.parse::<Expr>()?;
                        Ok(AsmOperand::InOut {
                            name: Some(name),
                            reg,
                            expr,
                        })
                    }
                    _ => Err(input.error("Expected operand specification after name =")),
                }
            } else {
                Err(input.error("Expected direction specification after name ="))
            }
        }
        // Check for options(...)
        else if input.peek(Ident) {
            let ident = input.fork().parse::<Ident>()?;
            if ident == "options" && input.peek2(syn::token::Paren) {
                input.parse::<Ident>()?; // consume "options"
                let content;
                syn::parenthesized!(content in input);
                // Parse the entire content as a single expression (handles comma-separated values)
                let remaining_tokens = content.parse::<proc_macro2::TokenStream>()?;
                let expr: Expr = syn::parse2(quote! { (#remaining_tokens) })?;
                Ok(AsmOperand::Options(expr))
            } else if input.peek2(syn::token::Paren) {
                // Handle non-named operand specifications (out/inout)
                let ident = input.parse::<Ident>()?;
                match ident.to_string().as_str() {
                    "out" => {
                        let content;
                        syn::parenthesized!(content in input);
                        let reg = content.parse::<Ident>()?;
                        let expr = input.parse::<Expr>()?;
                        Ok(AsmOperand::Output {
                            name: None,
                            reg,
                            expr,
                        })
                    }
                    "inout" => {
                        let content;
                        syn::parenthesized!(content in input);
                        let reg = content.parse::<Ident>()?;
                        let expr = input.parse::<Expr>()?;
                        Ok(AsmOperand::InOut {
                            name: None,
                            reg,
                            expr,
                        })
                    }
                    _ => {
                        // Parse as raw expression
                        let expr = input.parse::<Expr>()?;
                        Ok(AsmOperand::Raw(expr))
                    }
                }
            } else {
                // Parse as raw expression
                let expr = input.parse::<Expr>()?;
                Ok(AsmOperand::Raw(expr))
            }
        }
        // Try to parse 'in' keyword specifically (since 'in' is a keyword in Rust)
        else if input.peek(Token![in]) {
            input.parse::<Token![in]>()?;
            let content;
            syn::parenthesized!(content in input);
            let reg = content.parse::<Ident>()?;
            let expr = input.parse::<Expr>()?;
            Ok(AsmOperand::Input {
                name: None,
                reg,
                expr,
            })
        } else {
            // Parse as raw expression
            let expr = input.parse::<Expr>()?;
            Ok(AsmOperand::Raw(expr))
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
            if let AsmOperand::Options(expr) = &operand
                && let Expr::Tuple(tuple) = expr
            {
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
