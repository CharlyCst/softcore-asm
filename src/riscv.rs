use crate::InstructionInfo;
use proc_macro2::TokenStream;
use quote::quote;

pub fn emit_softcore_instr(instr: &InstructionInfo) -> TokenStream {
    eprintln!("## {:?}", instr);

    quote! {
      core.csrrw(reg::X0).unwrap();
    }
}
