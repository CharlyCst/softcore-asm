use quote::quote;
use std::fmt::Display;

use crate::{AsmOperand, RegisterOperand};

impl Display for AsmOperand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AsmOperand::Register(RegisterOperand {
                ident,
                reg,
                expr,
                is_input,
                is_output,
            }) => {
                let kind = match (is_input, is_output) {
                    (true, true) => "InOut",
                    (true, false) => "Input",
                    (false, true) => "Output",
                    (false, false) => "???", // Not supported
                };
                if let Some(name) = ident {
                    write!(
                        f,
                        "Named {} {}={} reg={}, expr={}",
                        kind,
                        name,
                        reg,
                        reg,
                        quote!(#expr)
                    )
                } else {
                    write!(f, "{} reg={}, expr={}", kind, reg, quote!(#expr))
                }
            }
            AsmOperand::Options(expr) => {
                write!(f, "Options expr={}", quote!(#expr))
            }
        }
    }
}
