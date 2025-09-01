use crate::InstructionInfo;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::Error;

pub fn emit_softcore_instr(instr: &InstructionInfo) -> Result<TokenStream, Error> {
    let ops = &instr.operands;
    match instr.instr.as_str() {
        "csrrw" => {
            check_nb_op(instr, 3)?;
            let rd = emit_reg(&ops[0]);
            let csr = emit_csr(&ops[1]);
            let rs1 = emit_reg(&ops[2]);
            Ok(quote! { core.csrrw(#rd, #csr, #rs1).unwrap(); })
        }
        "csrrs" => {
            check_nb_op(instr, 3)?;
            let rd = emit_reg(&ops[0]);
            let csr = emit_csr(&ops[1]);
            let rs1 = emit_reg(&ops[2]);
            Ok(quote! { core.csrrs(#rd, #csr, #rs1).unwrap(); })
        }
        "csrrc" => {
            check_nb_op(instr, 3)?;
            let rd = emit_reg(&ops[0]);
            let csr = emit_csr(&ops[1]);
            let rs1 = emit_reg(&ops[2]);
            Ok(quote! { core.csrrc(#rd, #csr, #rs1).unwrap(); })
        }
        "csrw" => {
            check_nb_op(instr, 2)?;
            let rd = emit_reg("x0");
            let csr = emit_csr(&ops[0]);
            let rs1 = emit_reg(&ops[1]);
            Ok(quote! { core.csrrw(#rd, #csr, #rs1).unwrap(); })
        }
        "csrs" => {
            check_nb_op(instr, 2)?;
            let rd = emit_reg("x0");
            let csr = emit_csr(&ops[0]);
            let rs1 = emit_reg(&ops[1]);
            Ok(quote! { core.csrrs(#rd, #csr, #rs1).unwrap(); })
        }
        "csrc" => {
            check_nb_op(instr, 2)?;
            let rd = emit_reg("x0");
            let csr = emit_csr(&ops[0]);
            let rs1 = emit_reg(&ops[1]);
            Ok(quote! { core.csrrc(#rd, #csr, #rs1).unwrap(); })
        }
        _ => Err(Error::new(
            Span::call_site(),
            format!("Unknown instruction: {}", instr.instr),
        )),
    }
}

/// Returns an error if the number of operands is not `n`.
fn check_nb_op(instr: &InstructionInfo, n: usize) -> Result<(), Error> {
    let m = instr.operands.len();
    if m == n {
        Ok(())
    } else {
        let s = if n > 1 { "s" } else { "" };
        Err(Error::new(
            Span::call_site(),
            format!("Expected {n} operand{s}, got {m}"),
        ))
    }
}

/// Create tokens corresponding to the provided register.
pub fn emit_reg(reg: &str) -> TokenStream {
    match reg {
        "x0" | "zero" => quote! {reg::X0},
        "x1" | "ra" => quote! {reg::X1},
        "x2" | "sp" => quote! {reg::X2},
        "x3" | "gp" => quote! {reg::X3},
        "x4" | "tp" => quote! {reg::X4},
        "x5" | "t0" => quote! {reg::X5},
        "x6" | "t1" => quote! {reg::X6},
        "x7" | "t2" => quote! {reg::X7},
        "x8" | "s0" | "fp" => quote! {reg::X8},
        "x9" | "s1" => quote! {reg::X9},
        "x10" | "a0" => quote! {reg::X10},
        "x11" | "a1" => quote! {reg::X11},
        "x12" | "a2" => quote! {reg::X12},
        "x13" | "a3" => quote! {reg::X13},
        "x14" | "a4" => quote! {reg::X14},
        "x15" | "a5" => quote! {reg::X15},
        "x16" | "a6" => quote! {reg::X16},
        "x17" | "a7" => quote! {reg::X17},
        "x18" | "s2" => quote! {reg::X18},
        "x19" | "s3" => quote! {reg::X19},
        "x20" | "s4" => quote! {reg::X20},
        "x21" | "s5" => quote! {reg::X21},
        "x22" | "s6" => quote! {reg::X22},
        "x23" | "s7" => quote! {reg::X23},
        "x24" | "s8" => quote! {reg::X24},
        "x25" | "s9" => quote! {reg::X25},
        "x26" | "s10" => quote! {reg::X26},
        "x27" | "s11" => quote! {reg::X27},
        "x28" | "t3" => quote! {reg::X28},
        "x29" | "t4" => quote! {reg::X29},
        "x30" | "t5" => quote! {reg::X30},
        "x31" | "t6" => quote! {reg::X31},
        _ => Error::new(Span::call_site(), format!("Unknown register: {reg}")).to_compile_error(),
    }
}

/// Creates tokens corresponding to the provided CSR register name.
fn emit_csr(csr: &str) -> TokenStream {
    quote! {csr_name_map_backwards(#csr).bits()}
}
