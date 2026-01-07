//! Abstraction over the assembly architecture

use crate::ReturnType;
use crate::asm_parser::Instr;
use crate::relooper::LabelTerminator;
use proc_macro2::TokenStream;
use std::collections::HashMap;
use syn::Error;
use syn::Path;

/// Tokens to emulate an instruction in pure Rust code.
pub enum InstrToken {
    /// This instruction may cause a trap, which must be checked for.
    MayTrap(TokenStream),
    /// This instruction never traps.
    Infallible(TokenStream),
}

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

    /// Update the registers by inserting the return values of a Rust function into the core's
    /// registers.
    /// Returns a token stream for the function call, which create new variables as appropriate,
    /// and a second token steam of registers to update in the next softwcore block.
    fn update_register_from_fn_call(
        abi: &str,
        return_type: ReturnType,
        call: TokenStream,
    ) -> (TokenStream, TokenStream);
}
