//! Abstraction over the assembly architecture

use crate::asm_parser::Instr;
use crate::relooper::LabelTerminator;
use proc_macro2::TokenStream;
use std::collections::HashMap;
use syn::Error;
use syn::Path;

pub trait Arch {
    /// If the instruction is a control flow instruction, returns the corresponding condition and
    /// destination.
    fn as_control_flow(
        instr: &Instr,
        symbols: &HashMap<String, Path>,
    ) -> Result<Option<LabelTerminator>, Error>;

    fn emit_reg(reg: &str) -> TokenStream;

    /// Returns the registers used for passing arguments, as a function of the ABI and the number
    /// of arguments.
    //
    //  TODO: return a result here to allow for proper error handling.
    fn abi_registers(abi: &str, nb_args: u64) -> &[&str];
}
