use crate::arch::Arch;
use crate::asm_parser::{Attribute, Expr as NumExpr, ReturnType};
use crate::relooper::{Conditional, FnCall, LabelTerminator};
use crate::{Context, Instr, asm_parser};
use proc_macro2::{Span, TokenStream};
use quote::quote;
use std::collections::HashMap;
use syn::{Error, Expr, Path};

// ————————————————————————————— Helper Macros —————————————————————————————— //

/// Emit the tokens for an RTYPE instruction
macro_rules! rtype {
    ($instr: ident, $op:path) => {{
        check_nb_op($instr, 3)?;
        let rd = Riscv::emit_reg(&$instr.operands[0]);
        let rs1 = Riscv::emit_reg(&$instr.operands[1]);
        let rs2 = Riscv::emit_reg(&$instr.operands[2]);
        Ok(quote! {
            core.execute(ast::RTYPE((#rs2, #rs1, #rd, rop::$op)));
        })
    }};
}

/// Emit the tokens for an ITYPE instruction
macro_rules! itype {
    ($instr: ident, $op:path, $consts: ident) => {{
        check_nb_op($instr, 3)?;
        let rd = Riscv::emit_reg(&$instr.operands[0]);
        let rs1 = Riscv::emit_reg(&$instr.operands[1]);
        let imm = emit_integer(&$instr.operands[2], $consts);
        Ok(quote! {
            core.execute(ast::ITYPE((bv(#imm), #rs1, #rd, iop::$op)));
        })
    }};
}

/// Emit the tokens for an SHIFTIOP instruction
macro_rules! shiftiop {
    ($instr: ident, $op:path, $consts: ident) => {{
        check_nb_op($instr, 3)?;
        let rd = Riscv::emit_reg(&$instr.operands[0]);
        let rs1 = Riscv::emit_reg(&$instr.operands[1]);
        let imm = emit_integer(&$instr.operands[2], $consts);
        Ok(quote! {
            core.execute(ast::SHIFTIOP((bv(#imm), #rs1, #rd, sop::$op)));
        })
    }};
}

/// Emit the tokens for MUL type instructions
macro_rules! mul {
    ($instr: ident, $op_bits: literal) => {{
        check_nb_op($instr, 3)?;
        let rd = Riscv::emit_reg(&$instr.operands[0]);
        let rs1 = Riscv::emit_reg(&$instr.operands[1]);
        let rs2 = Riscv::emit_reg(&$instr.operands[2]);
        Ok(quote! {
            core.execute(ast::MUL((#rs2, #rs1, #rd, raw::encdec_mul_op_backwards(bv::<3>($op_bits)))));
        })
    }};
}

// ————————————————————————— Instruction to Tokens —————————————————————————— //

pub struct Riscv {}

impl Arch for Riscv {
    fn as_control_flow(
        instr: &Instr,
        symbols: &HashMap<String, Path>,
    ) -> Result<Option<LabelTerminator>, Error> {
        let ops = &instr.operands;
        match instr.mnemonic.as_str() {
            "beq" => {
                check_nb_op(instr, 3)?;
                Ok(Some(LabelTerminator::Branch {
                    cond: Conditional::Eq(ops[0].to_string(), ops[1].to_string()),
                    if_true: ops[2].to_string(),
                }))
            }
            "bne" => {
                check_nb_op(instr, 3)?;
                Ok(Some(LabelTerminator::Branch {
                    cond: Conditional::Ne(ops[0].to_string(), ops[1].to_string()),
                    if_true: ops[2].to_string(),
                }))
            }
            "blt" => {
                check_nb_op(instr, 3)?;
                Ok(Some(LabelTerminator::Branch {
                    cond: Conditional::Lt(ops[0].to_string(), ops[1].to_string()),
                    if_true: ops[2].to_string(),
                }))
            }
            "bge" => {
                check_nb_op(instr, 3)?;
                Ok(Some(LabelTerminator::Branch {
                    cond: Conditional::Ge(ops[0].to_string(), ops[1].to_string()),
                    if_true: ops[2].to_string(),
                }))
            }
            "bltu" => {
                check_nb_op(instr, 3)?;
                Ok(Some(LabelTerminator::Branch {
                    cond: Conditional::Ltu(ops[0].to_string(), ops[1].to_string()),
                    if_true: ops[2].to_string(),
                }))
            }
            "bgeu" => {
                check_nb_op(instr, 3)?;
                Ok(Some(LabelTerminator::Branch {
                    cond: Conditional::Geu(ops[0].to_string(), ops[1].to_string()),
                    if_true: ops[2].to_string(),
                }))
            }
            // Pseudo-instructions with implicit x0
            "beqz" => {
                check_nb_op(instr, 2)?;
                Ok(Some(LabelTerminator::Branch {
                    cond: Conditional::Eq(ops[0].to_string(), "x0".to_string()),
                    if_true: ops[1].to_string(),
                }))
            }
            "bnez" => {
                check_nb_op(instr, 2)?;
                Ok(Some(LabelTerminator::Branch {
                    cond: Conditional::Ne(ops[0].to_string(), "x0".to_string()),
                    if_true: ops[1].to_string(),
                }))
            }
            "blez" => {
                check_nb_op(instr, 2)?;
                Ok(Some(LabelTerminator::Branch {
                    cond: Conditional::Ge("x0".to_string(), ops[0].to_string()),
                    if_true: ops[1].to_string(),
                }))
            }
            "bgez" => {
                check_nb_op(instr, 2)?;
                Ok(Some(LabelTerminator::Branch {
                    cond: Conditional::Ge(ops[0].to_string(), "x0".to_string()),
                    if_true: ops[1].to_string(),
                }))
            }
            "bltz" => {
                check_nb_op(instr, 2)?;
                Ok(Some(LabelTerminator::Branch {
                    cond: Conditional::Lt(ops[0].to_string(), "x0".to_string()),
                    if_true: ops[1].to_string(),
                }))
            }
            "bgtz" => {
                check_nb_op(instr, 2)?;
                Ok(Some(LabelTerminator::Branch {
                    cond: Conditional::Lt("x0".to_string(), ops[0].to_string()),
                    if_true: ops[1].to_string(),
                }))
            }
            "j" => {
                check_nb_op(instr, 1)?;
                Ok(Some(LabelTerminator::Jump(ops[0].to_string())))
            }
            "call" => {
                check_nb_op(instr, 1)?;

                // Get the function to call from the list of symbols
                let sym = &ops[0];
                let Some(path) = symbols.get(sym) else {
                    return Err(Error::new(
                        Span::call_site(),
                        format!("Could not find function a symbol named '{sym}'"),
                    ));
                };

                // Look for an ABI annotation (required for now as Rust can't infer the number of
                // arguments (the arity) of the function when doing a cast.
                let Some((abi_name, num_args, return_type)) =
                    instr.attributes.iter().find_map(|attr| match attr {
                        Attribute::Abi {
                            name,
                            num_args,
                            return_type,
                        } => Some((name, num_args, return_type)),
                        _ => None,
                    })
                else {
                    return Err(Error::new(
                    Span::call_site(),
                    "Function calls ABI must be specified with the `abi` attribute. For instance: `// #[abi(\\\"C\\\", 4)]`.".to_string(),
                ));
                };
                Ok(Some(LabelTerminator::FnCall(FnCall {
                    fn_path: path.clone(),
                    abi: abi_name.clone(),
                    num_args: *num_args,
                    return_type: *return_type,
                })))
            }
            _ => Ok(None),
        }
    }

    /// Create tokens corresponding to the provided register.
    fn emit_reg(reg: &str) -> TokenStream {
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
            _ => {
                Error::new(Span::call_site(), format!("Unknown register: {reg}")).to_compile_error()
            }
        }
    }

    fn abi_registers(abi: &str, nb_args: u64) -> &[&str] {
        static ARGS_ABI: [&str; 8] = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"];

        assert!(abi == "C" || abi == "C-unwind", "Unsupported ABI: '{abi}'");
        assert!(nb_args <= 8, "Support at most 8 arguments");

        let nb_args = nb_args as usize;
        &ARGS_ABI[0..nb_args]
    }

    fn update_register_from_fn_call(
        abi: &str,
        return_type: ReturnType,
        call: TokenStream,
    ) -> (TokenStream, TokenStream) {
        assert!(abi == "C" || abi == "C-unwind", "Unsupported ABI: '{abi}'");
        match return_type {
            // Nothing to do, just inline the call
            ReturnType::Never | ReturnType::Unit => (call, quote! {}),
            // We need to put the return value into a0
            ReturnType::U64 | ReturnType::U32 | ReturnType::I64 | ReturnType::I32 => {
                let ret_reg = Self::emit_reg("a0");
                let call = quote! { let ret_val = #call; };
                let update = quote! { core.set(#ret_reg, ret_val as u64); };
                (call, update)
            }
        }
    }
}

pub fn emit_softcore_instr<A>(instr: &Instr, ctx: &Context<A>) -> Result<TokenStream, Error> {
    let syms = &ctx.symbols;
    let consts = &ctx.consts;
    let ops = &instr.operands;
    match instr.mnemonic.as_str() {
        // CSR operations
        "csrrw" => {
            check_nb_op(instr, 3)?;
            let rd = Riscv::emit_reg(&ops[0]);
            let csr = emit_csr(&ops[1]);
            let rs1 = Riscv::emit_reg(&ops[2]);
            Ok(quote! { core.csrrw(#rd, #csr, #rs1).unwrap(); })
        }
        "csrrs" => {
            check_nb_op(instr, 3)?;
            let rd = Riscv::emit_reg(&ops[0]);
            let csr = emit_csr(&ops[1]);
            let rs1 = Riscv::emit_reg(&ops[2]);
            Ok(quote! { core.csrrs(#rd, #csr, #rs1).unwrap(); })
        }
        "csrrc" => {
            check_nb_op(instr, 3)?;
            let rd = Riscv::emit_reg(&ops[0]);
            let csr = emit_csr(&ops[1]);
            let rs1 = Riscv::emit_reg(&ops[2]);
            Ok(quote! { core.csrrc(#rd, #csr, #rs1).unwrap(); })
        }
        "csrr" => {
            check_nb_op(instr, 2)?;
            let rd = Riscv::emit_reg(&ops[0]);
            let csr = emit_csr(&ops[1]);
            let rs1 = Riscv::emit_reg("x0");
            Ok(quote! { core.csrrs(#rd, #csr, #rs1).unwrap(); })
        }
        "csrw" => {
            check_nb_op(instr, 2)?;
            let rd = Riscv::emit_reg("x0");
            let csr = emit_csr(&ops[0]);
            let rs1 = Riscv::emit_reg(&ops[1]);
            Ok(quote! { core.csrrw(#rd, #csr, #rs1).unwrap(); })
        }
        "csrs" => {
            check_nb_op(instr, 2)?;
            let rd = Riscv::emit_reg("x0");
            let csr = emit_csr(&ops[0]);
            let rs1 = Riscv::emit_reg(&ops[1]);
            Ok(quote! { core.csrrs(#rd, #csr, #rs1).unwrap(); })
        }
        "csrc" => {
            check_nb_op(instr, 2)?;
            let rd = Riscv::emit_reg("x0");
            let csr = emit_csr(&ops[0]);
            let rs1 = Riscv::emit_reg(&ops[1]);
            Ok(quote! { core.csrrc(#rd, #csr, #rs1).unwrap(); })
        }

        // Loads and Stores
        "li" => {
            // Load immediate is a pseudo-instruction.
            // Here we implement it in Rust directly, rather than as a combination of lui and addi.
            check_nb_op(instr, 2)?;
            let rd = Riscv::emit_reg(&ops[0]);
            let value = emit_integer(&ops[1], consts);
            Ok(quote! { core.set(#rd, #value as u64); })
        }
        "la" => {
            // Load address is a pseudo-instruction, it relies on relocations to find the address
            // of a symbol.
            // We can't use the same trick here, because we don't want to rely on the linker for
            // that. Instead, we use Rust to find the address of the symbol directly.
            check_nb_op(instr, 2)?;
            let rd = Riscv::emit_reg(&ops[0]);
            let sym_addr = emit_symbol_addr(&ops[1], syms);
            Ok(quote! { core.set(#rd, #sym_addr as u64); })
        }
        "ld" => {
            check_nb_op(instr, 2)?;
            let rd = Riscv::emit_reg(&ops[0]);
            let (imm, rs1) = emit_immediate_offset(&ops[1], consts)?;
            Ok(quote! {
                let addr = core::ptr::with_exposed_provenance::<u64>(
                    #imm.wrapping_add(core.get(#rs1)) as usize);
                let val = core::ptr::read(addr);
                core.set(#rd, val as u64);
            })
        }
        "lwu" => {
            check_nb_op(instr, 2)?;
            let rd = Riscv::emit_reg(&ops[0]);
            let (imm, rs1) = emit_immediate_offset(&ops[1], consts)?;
            Ok(quote! {
                let addr = core::ptr::with_exposed_provenance::<u32>(
                    #imm.wrapping_add(core.get(#rs1)) as usize);
                let val = core::ptr::read(addr);
                core.set(#rd, val as u64);
            })
        }
        "lw" => {
            check_nb_op(instr, 2)?;
            let rd = Riscv::emit_reg(&ops[0]);
            let (imm, rs1) = emit_immediate_offset(&ops[1], consts)?;
            Ok(quote! {
                let addr = core::ptr::with_exposed_provenance::<i32>(
                    #imm.wrapping_add(core.get(#rs1)) as usize);
                let val = core::ptr::read(addr);
                core.set(#rd, val as i64 as u64);
            })
        }
        "lhu" => {
            check_nb_op(instr, 2)?;
            let rd = Riscv::emit_reg(&ops[0]);
            let (imm, rs1) = emit_immediate_offset(&ops[1], consts)?;
            Ok(quote! {
                let addr = core::ptr::with_exposed_provenance::<u16>(
                    #imm.wrapping_add(core.get(#rs1)) as usize);
                let val = core::ptr::read(addr);
                core.set(#rd, val as u64);
            })
        }
        "lh" => {
            check_nb_op(instr, 2)?;
            let rd = Riscv::emit_reg(&ops[0]);
            let (imm, rs1) = emit_immediate_offset(&ops[1], consts)?;
            Ok(quote! {
                let addr = core::ptr::with_exposed_provenance::<i16>(
                    #imm.wrapping_add(core.get(#rs1)) as usize);
                let val = core::ptr::read(addr);
                core.set(#rd, val as i64 as u64);
            })
        }
        "lbu" => {
            check_nb_op(instr, 2)?;
            let rd = Riscv::emit_reg(&ops[0]);
            let (imm, rs1) = emit_immediate_offset(&ops[1], consts)?;
            Ok(quote! {
                let addr = core::ptr::with_exposed_provenance::<u8>(
                    #imm.wrapping_add(core.get(#rs1)) as usize);
                let val = core::ptr::read(addr);
                core.set(#rd, val as u64);
            })
        }
        "lb" => {
            check_nb_op(instr, 2)?;
            let rd = Riscv::emit_reg(&ops[0]);
            let (imm, rs1) = emit_immediate_offset(&ops[1], consts)?;
            Ok(quote! {
                let addr = core::ptr::with_exposed_provenance::<i8>(
                    #imm.wrapping_add(core.get(#rs1)) as usize);
                let val = core::ptr::read(addr);
                core.set(#rd, val as i64 as u64);
            })
        }
        "sd" => {
            check_nb_op(instr, 2)?;
            let rs2 = Riscv::emit_reg(&ops[0]);
            let (imm, rs1) = emit_immediate_offset(&ops[1], consts)?;
            Ok(quote! {
                let val = core.get(#rs2);
                let addr = core::ptr::with_exposed_provenance_mut::<u64>(
                    #imm.wrapping_add(core.get(#rs1)) as usize);
                let addr = (#imm.wrapping_add(core.get(#rs1))) as usize as *mut u64;
                core::ptr::write(addr, val as u64);
            })
        }
        "sw" => {
            check_nb_op(instr, 2)?;
            let rs2 = Riscv::emit_reg(&ops[0]);
            let (imm, rs1) = emit_immediate_offset(&ops[1], consts)?;
            Ok(quote! {
                let val = core.get(#rs2);
                let addr = core::ptr::with_exposed_provenance_mut::<u32>(
                    #imm.wrapping_add(core.get(#rs1)) as usize);
                core::ptr::write(addr, val as u32);
            })
        }
        "sh" => {
            check_nb_op(instr, 2)?;
            let rs2 = Riscv::emit_reg(&ops[0]);
            let (imm, rs1) = emit_immediate_offset(&ops[1], consts)?;
            Ok(quote! {
                let val = core.get(#rs2);
                let addr = core::ptr::with_exposed_provenance_mut::<u16>(
                    #imm.wrapping_add(core.get(#rs1)) as usize);
                core::ptr::write(addr, val as u16);
            })
        }
        "sb" => {
            check_nb_op(instr, 2)?;
            let rs2 = Riscv::emit_reg(&ops[0]);
            let (imm, rs1) = emit_immediate_offset(&ops[1], consts)?;
            Ok(quote! {
                let val = core.get(#rs2);
                let addr = core::ptr::with_exposed_provenance_mut::<u8>(
                    #imm.wrapping_add(core.get(#rs1)) as usize);
                core::ptr::write(addr, val as u8);
            })
        }

        // RType
        "add" => rtype!(instr, ADD),
        "slt" => rtype!(instr, SLT),
        "sltu" => rtype!(instr, SLTU),
        "and" => rtype!(instr, AND),
        "or" => rtype!(instr, OR),
        "xor" => rtype!(instr, XOR),
        "sll" => rtype!(instr, SLL),
        "srl" => rtype!(instr, SRL),
        "sub" => rtype!(instr, SUB),
        "sra" => rtype!(instr, SRA),

        // IType
        "addi" => itype!(instr, ADDI, consts),
        "slti" => itype!(instr, SLTI, consts),
        "sltiu" => itype!(instr, SLTIU, consts),
        "andi" => itype!(instr, ANDI, consts),
        "ori" => itype!(instr, ORI, consts),
        "xori" => itype!(instr, XORI, consts),
        "mv" => {
            // Expends into an ADDI
            check_nb_op(instr, 2)?;
            let mut operands = ops.clone();
            operands.push("0".to_string());
            let instr = &Instr {
                mnemonic: "addi".to_string(),
                operands,
                attributes: vec![],
            };
            itype!(instr, ADDI, consts)
        }

        // ShiftIOP
        "slli" => shiftiop!(instr, SLLI, consts),
        "srli" => shiftiop!(instr, SRLI, consts),
        "srai" => shiftiop!(instr, SRAI, consts),

        // MUL
        "mul" => mul!(instr, 0b000),
        "mulh" => mul!(instr, 0b001),
        "mulhsu" => mul!(instr, 0b010),
        "mulhu" => mul!(instr, 0b011),

        // Jumps (control-flow not emulated)
        "jr" => {
            // Pseudo-instruction for `jalr x0, 0(rs1)`
            check_nb_op(instr, 1)?;
            let rs1 = Riscv::emit_reg(&ops[0]);
            let rd = Riscv::emit_reg("x0");
            Ok(quote! { core.execute(ast::JALR((bv(0), #rs1, #rd))); })
        }

        // System
        "mret" => {
            check_nb_op(instr, 0)?;
            Ok(quote! { core.execute(ast::MRET(())); })
        }
        "sret" => {
            check_nb_op(instr, 0)?;
            Ok(quote! { core.execute(ast::SRET(())); })
        }
        "ecall" => {
            check_nb_op(instr, 0)?;
            Ok(quote! { core.execute(ast::ECALL(())); })
        }
        "ebreak" => {
            check_nb_op(instr, 0)?;
            Ok(quote! { core.execute(ast::EBREAK(())); })
        }
        "wfi" => {
            check_nb_op(instr, 0)?;
            Ok(quote! { core.execute(ast::WFI(())); })
        }
        "fence.i" => {
            check_nb_op(instr, 0)?;
            Ok(quote! { core.execute(ast::FENCEI(())); })
        }
        "sfence.vma" => {
            // The assembly can allow omitting some arguments
            let (vaddr, asid) = if instr.operands.is_empty() {
                (Riscv::emit_reg("x0"), Riscv::emit_reg("x0"))
            } else if instr.operands.len() == 1 {
                (Riscv::emit_reg(&ops[0]), Riscv::emit_reg("x0"))
            } else {
                check_nb_op(instr, 2)?;
                (Riscv::emit_reg(&ops[0]), Riscv::emit_reg(&ops[1]))
            };
            Ok(quote! { core.execute(ast::SFENCE_VMA((#vaddr, #asid))); })
        }
        "hfence.gvma" => {
            // Not currently supported in the Sail model, emit a no-op.
            Ok(quote! {})
        }
        "hfence.vvma" => {
            // Not currently supported in the Sail model, emit a no-op.
            Ok(quote! {})
        }

        // Unknown instructions
        _ => Err(Error::new(
            Span::call_site(),
            format!("Unknown instruction: {}", instr.mnemonic),
        )),
    }
}

/// Returns an error if the number of operands is not `n`.
fn check_nb_op(instr: &Instr, n: usize) -> Result<(), Error> {
    let m = instr.operands.len();
    if m == n {
        Ok(())
    } else {
        let s = if n > 1 { "s" } else { "" };
        Err(Error::new(
            Span::call_site(),
            format!(
                "Expected {n} operand{s}, got {m}: {} {:?}",
                instr.mnemonic,
                instr.operands.as_slice()
            ),
        ))
    }
}

/// Creates tokens corresponding to the provided CSR register name.
fn emit_csr(csr: &str) -> TokenStream {
    quote! { csr_name_map_backwards(#csr).bits() }
}

/// Returns the parsed integer as a TokenStream.
///
/// All integers are encoded as u64, this means that negative numbers are represented as 2's
/// complements. It is still possible to add two u64 as if they were signed using
/// `.wrapping_add()`, but care must be taken in case a negative integer is required.
fn emit_integer(n: &str, consts: &HashMap<String, Expr>) -> TokenStream {
    let n = match asm_parser::into_numeric_expr(n) {
        Ok(n) => n,
        Err(err) => {
            return Error::new(Span::call_site(), err.to_string()).to_compile_error();
        }
    };
    emit_integer_from_expr(n, consts)
}

fn emit_integer_from_expr(n: NumExpr, consts: &HashMap<String, Expr>) -> TokenStream {
    match n {
        NumExpr::Number(n) => {
            let n = n as u64;
            quote! {#n}
        }
        NumExpr::Constant(cst) => emit_constant(&cst, consts),
        _ => Error::new(
            Span::call_site(),
            format!("expression not yet supported: '{n:?}'"),
        )
        .to_compile_error(),
    }
}

/// Parse operands of the shape `imm(reg)`, as used in loads and stores.
fn emit_immediate_offset(
    imm_off: &str,
    consts: &HashMap<String, Expr>,
) -> Result<(TokenStream, TokenStream), Error> {
    match asm_parser::into_immediate_offset(imm_off) {
        Ok((offset, reg)) => Ok((emit_integer_from_expr(offset, consts), Riscv::emit_reg(reg))),
        Err(err) => Err(Error::new(Span::call_site(), err.to_string())),
    }
}

fn emit_symbol_addr(sym: &str, syms: &HashMap<String, Path>) -> TokenStream {
    if let Some(path) = syms.get(sym) {
        quote! {(&raw const #path) as *const _}
    } else {
        Error::new(
            Span::call_site(),
            format!("Could not find a symbol named '{sym}'"),
        )
        .to_compile_error()
    }
}

fn emit_constant(cst: &str, consts: &HashMap<String, Expr>) -> TokenStream {
    if let Some(cst) = consts.get(cst) {
        quote! { #cst }
    } else {
        Error::new(
            Span::call_site(),
            format!("Could not find a constant named '{cst}'"),
        )
        .to_compile_error()
    }
}

// ————————————————————————————————— Tests —————————————————————————————————— //

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_emit_integer() {
        let consts = HashMap::new();

        // Test positive decimal
        let result = emit_integer("123", &consts);
        assert_eq!(result.to_string(), "123u64");

        // Test negative decimal
        let result = emit_integer("-456", &consts);
        assert_eq!(result.to_string(), "18446744073709551160u64");

        // Test zero
        let result = emit_integer("0", &consts);
        assert_eq!(result.to_string(), "0u64");

        // Test positive hexadecimal
        let result = emit_integer("0x10", &consts);
        assert_eq!(result.to_string(), "16u64");

        // Test negative hexadecimal
        let result = emit_integer("-0xFF", &consts);
        assert_eq!(result.to_string(), "18446744073709551361u64");

        // Test hexadecimal with mixed case
        let result = emit_integer("0xAbC", &consts);
        assert_eq!(result.to_string(), "2748u64");

        // Test negative zero
        let result = emit_integer("-0", &consts);
        assert_eq!(result.to_string(), "0u64");

        // Test large hexadecimal value
        let result = emit_integer("0x1234", &consts);
        assert_eq!(result.to_string(), "4660u64");

        // Test negative large hexadecimal
        let result = emit_integer("-0x1000", &consts);
        assert_eq!(result.to_string(), "18446744073709547520u64");

        // Test single digit hex
        let result = emit_integer("0x5", &consts);
        assert_eq!(result.to_string(), "5u64");
    }

    #[test]
    fn immediate_offset() {
        let consts = HashMap::new();

        // Test valid decimal immediate with register
        let result = emit_immediate_offset("123(x1)", &consts).unwrap();
        assert_eq!(result.0.to_string(), "123u64");
        assert_eq!(result.1.to_string(), "reg :: X1");

        // Test valid negative decimal immediate
        let result = emit_immediate_offset("-456(sp)", &consts).unwrap();
        assert_eq!(result.0.to_string(), "18446744073709551160u64");
        assert_eq!(result.1.to_string(), "reg :: X2");

        // Test valid hexadecimal immediate
        let result = emit_immediate_offset("0x10(a0)", &consts).unwrap();
        assert_eq!(result.0.to_string(), "16u64");
        assert_eq!(result.1.to_string(), "reg :: X10");

        // Test valid negative hexadecimal immediate
        let result = emit_immediate_offset("-0xFF(t0)", &consts).unwrap();
        assert_eq!(result.0.to_string(), "18446744073709551361u64");
        assert_eq!(result.1.to_string(), "reg :: X5");

        // Test zero immediate
        let result = emit_immediate_offset("0(zero)", &consts).unwrap();
        assert_eq!(result.0.to_string(), "0u64");
        assert_eq!(result.1.to_string(), "reg :: X0");

        // Test register aliases
        let result = emit_immediate_offset("8(fp)", &consts).unwrap();
        assert_eq!(result.0.to_string(), "8u64");
        assert_eq!(result.1.to_string(), "reg :: X8");

        // Test missing immediate
        let result = emit_immediate_offset("(x1)", &consts).unwrap();
        assert_eq!(result.0.to_string(), "0u64");
        assert_eq!(result.1.to_string(), "reg :: X1");

        // Test invalid formats - missing parentheses
        assert!(emit_immediate_offset("123x1", &consts).is_err());

        // Test invalid formats - missing register
        assert!(emit_immediate_offset("123()", &consts).is_err());

        // Test invalid formats - no closing parenthesis
        assert!(emit_immediate_offset("123(x1", &consts).is_err());

        // Test invalid immediate value
        assert!(emit_immediate_offset("invalid(x1)", &consts).is_err());
    }
}
