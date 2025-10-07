//! Abstraction over the assembly architecture

use crate::Conditional;
use crate::asm_parser::Instr;
use crate::relooper::LabelTerminator;
use proc_macro2::TokenStream;
use syn::Error;

pub trait Arch {
    /// If the instruction is a control flow instruction, returns the corresponding condition and
    /// destination.
    fn as_control_flow(instr: &Instr) -> Result<Option<LabelTerminator>, Error>;

    fn emit_cond(cond: &Conditional) -> TokenStream;
}
