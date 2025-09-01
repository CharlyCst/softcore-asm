use crate::InstructionInfo;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use regex::Regex;
use std::sync::LazyLock;
use syn::Error;

pub fn emit_softcore_instr(instr: &InstructionInfo) -> Result<TokenStream, Error> {
    let ops = &instr.operands;
    match instr.instr.as_str() {
        // CSR operations
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

        // Loads and Stores
        "li" => {
            check_nb_op(instr, 2)?;
            let rd = emit_reg(&ops[0]);
            let value = emit_integer(&ops[1]);
            Ok(quote! {core.set(#rd, (#value as u64))})
        }
        "sd" => {
            check_nb_op(instr, 2)?;
            let rs2 = emit_reg(&ops[0]);
            let (imm, rs1) = emit_immediate_offset(&ops[1])?;
            Ok(quote! {
                let val = core.get(#rs2);
                let addr = (#imm + core.get(#rs1) as i128) as usize as *mut u64;
                core::ptr::write((addr) as *mut u64, val as u64);
            })
        }

        // Unknown instructions
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

fn emit_integer(n: &str) -> TokenStream {
    static RE: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"^(-)?(0x)?([0-9A-Fa-f]+)").unwrap());

    // Seach for a match
    let Some(caps) = RE.captures(n) else {
        return Error::new(Span::call_site(), format!("Invalid integer: '{n}'")).to_compile_error();
    };

    // Get the content of the capture groups
    let Some(num) = caps.get(3) else {
        return Error::new(Span::call_site(), format!("Invalid integer: '{n}'")).to_compile_error();
    };
    let is_negative = caps.get(1).is_some();
    let base = if caps.get(2).is_some() { 16 } else { 10 };

    // Parse the constant
    let Ok(mut n) = i128::from_str_radix(num.as_str(), base) else {
        return Error::new(Span::call_site(), format!("Invalid constant '{n}'")).to_compile_error();
    };
    if is_negative {
        n = -n;
    }
    quote! {#n}
}

/// Parse operands of the shape `imm(reg)`, as used in loads and stores.
fn emit_immediate_offset(imm_off: &str) -> Result<(TokenStream, TokenStream), Error> {
    static RE: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"^(-?(0x)?[0-9A-Fa-f]+)\(([A-Za-z0-9]+)\)").unwrap());

    // Seach for a match
    let Some(caps) = RE.captures(imm_off) else {
        return Err(Error::new(
            Span::call_site(),
            format!("Invalid immediate offset: '{imm_off}'"),
        ));
    };

    // Get the content of the capture groups
    let (Some(imm), Some(reg)) = (caps.get(1), caps.get(3)) else {
        return Err(Error::new(
            Span::call_site(),
            format!("Invalid immediate or offset: '{imm_off}'"),
        ));
    };

    Ok((emit_integer(imm.as_str()), emit_reg(reg.as_str())))
}

// ————————————————————————————————— Tests —————————————————————————————————— //

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_emit_integer() {
        // Test positive decimal
        let result = emit_integer("123");
        assert_eq!(result.to_string(), "123i128");

        // Test negative decimal
        let result = emit_integer("-456");
        assert_eq!(result.to_string(), "- 456i128");

        // Test zero
        let result = emit_integer("0");
        assert_eq!(result.to_string(), "0i128");

        // Test positive hexadecimal
        let result = emit_integer("0x10");
        assert_eq!(result.to_string(), "16i128");

        // Test negative hexadecimal
        let result = emit_integer("-0xFF");
        assert_eq!(result.to_string(), "- 255i128");

        // Test hexadecimal with mixed case
        let result = emit_integer("0xAbC");
        assert_eq!(result.to_string(), "2748i128");

        // Test negative zero
        let result = emit_integer("-0");
        assert_eq!(result.to_string(), "0i128");

        // Test large hexadecimal value
        let result = emit_integer("0x1234");
        assert_eq!(result.to_string(), "4660i128");

        // Test negative large hexadecimal
        let result = emit_integer("-0x1000");
        assert_eq!(result.to_string(), "- 4096i128");

        // Test single digit hex
        let result = emit_integer("0x5");
        assert_eq!(result.to_string(), "5i128");
    }

    #[test]
    fn immediate_offset() {
        // Test valid decimal immediate with register
        let result = emit_immediate_offset("123(x1)").unwrap();
        assert_eq!(result.0.to_string(), "123i128");
        assert_eq!(result.1.to_string(), "reg :: X1");

        // Test valid negative decimal immediate
        let result = emit_immediate_offset("-456(sp)").unwrap();
        assert_eq!(result.0.to_string(), "- 456i128");
        assert_eq!(result.1.to_string(), "reg :: X2");

        // Test valid hexadecimal immediate
        let result = emit_immediate_offset("0x10(a0)").unwrap();
        assert_eq!(result.0.to_string(), "16i128");
        assert_eq!(result.1.to_string(), "reg :: X10");

        // Test valid negative hexadecimal immediate
        let result = emit_immediate_offset("-0xFF(t0)").unwrap();
        assert_eq!(result.0.to_string(), "- 255i128");
        assert_eq!(result.1.to_string(), "reg :: X5");

        // Test zero immediate
        let result = emit_immediate_offset("0(zero)").unwrap();
        assert_eq!(result.0.to_string(), "0i128");
        assert_eq!(result.1.to_string(), "reg :: X0");

        // Test register aliases
        let result = emit_immediate_offset("8(fp)").unwrap();
        assert_eq!(result.0.to_string(), "8i128");
        assert_eq!(result.1.to_string(), "reg :: X8");

        // Test invalid formats - missing parentheses
        assert!(emit_immediate_offset("123x1").is_err());

        // Test invalid formats - missing immediate
        assert!(emit_immediate_offset("(x1)").is_err());

        // Test invalid formats - missing register
        assert!(emit_immediate_offset("123()").is_err());

        // Test invalid formats - no closing parenthesis
        assert!(emit_immediate_offset("123(x1").is_err());

        // Test invalid immediate value
        assert!(emit_immediate_offset("invalid(x1)").is_err());

        // Test invalid register
        assert!(emit_immediate_offset("123(invalid_reg)").is_err());
    }
}
