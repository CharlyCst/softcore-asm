use quote::quote;
use std::fmt::Display;

use crate::AsmOperand;

impl Display for AsmOperand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AsmOperand::Input { name, reg, expr } => {
                if let Some(name) = name {
                    write!(
                        f,
                        "Named Input {}={} reg={}, expr={}",
                        name,
                        reg,
                        reg,
                        quote!(#expr)
                    )
                } else {
                    write!(f, "Input reg={}, expr={}", reg, quote!(#expr))
                }
            }
            AsmOperand::Output { name, reg, expr } => {
                if let Some(name) = name {
                    write!(
                        f,
                        "Named Output {}={} reg={}, expr={}",
                        name,
                        reg,
                        reg,
                        quote!(#expr)
                    )
                } else {
                    write!(f, "Output reg={}, expr={}", reg, quote!(#expr))
                }
            }
            AsmOperand::InOut { name, reg, expr } => {
                if let Some(name) = name {
                    write!(
                        f,
                        "Named InOut {}={} reg={}, expr={}",
                        name,
                        reg,
                        reg,
                        quote!(#expr)
                    )
                } else {
                    write!(f, "InOut reg={}, expr={}", reg, quote!(#expr))
                }
            }
            AsmOperand::Options(expr) => {
                write!(f, "Options expr={}", quote!(#expr))
            }
            AsmOperand::Raw(expr) => {
                write!(f, "Raw expr={}", quote!(#expr))
            }
        }
    }
}
