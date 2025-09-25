use anyhow::Result;
use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use regex::Regex;
use std::collections::HashMap;
use std::sync::LazyLock;
use syn::{Expr, Path, parse_macro_input};

mod asm_parser;
mod parser;
mod riscv;

use parser::{AsmInput, AsmOperand};

use crate::{
    asm_parser::{AsmLine, Instr, into_asm_line},
    parser::{KindRegister, OperandKind, RegisterOperand},
};

#[derive(Clone)]
struct RegAllocation {
    register: String, // "x1", "x2", etc.
    expr: Expr,       // The Rust expression (e.g. variable) for the register
    is_input: bool,
    is_output: bool,
}

struct MultiInstructionAnalysis {
    instructions: Vec<Instr>,
    register_allocation: Vec<RegAllocation>,
    symbols: HashMap<String, Path>,
    consts: HashMap<String, Expr>,
}

fn parse_instructions(assembly_template: &[String]) -> Result<Vec<AsmLine>> {
    let asm_text = assembly_template.join("\n");
    asm_text
        .lines()
        .map(|line| into_asm_line(line.trim()))
        .filter_map(|line| match line {
            Ok(Some(asm)) => Some(Ok(asm)),
            Ok(None) => None,
            Err(err) => Some(Err(err)),
        })
        .collect::<Result<Vec<AsmLine>, _>>()
}

struct OperandMappings(
    Vec<RegAllocation>,
    HashMap<String, String>,
    HashMap<String, Path>,
    HashMap<String, Expr>,
);

fn build_operand_register_map(operands: &[AsmOperand]) -> OperandMappings {
    let mut register_allocation = Vec::new();
    let mut placeholder_instantiation = HashMap::new();
    let mut symbols = HashMap::new();
    let mut consts = HashMap::new();
    let mut reg_counter = 1;
    let mut ident_counter = 0;

    for operand in operands.iter() {
        if let AsmOperand::Register(RegisterOperand { ident, kind }) = operand {
            match kind {
                OperandKind::Register(KindRegister {
                    reg,
                    expr,
                    is_input,
                    is_output,
                }) => {
                    let ident = if let Some(ident) = ident {
                        ident.to_string()
                    } else {
                        // Anonymous registers are referenced by their index in the declaration
                        // order
                        let ident = format!("{}", ident_counter);
                        ident_counter += 1;
                        ident
                    };
                    let register = match reg {
                        parser::RegisterKind::Ident(_ident) => {
                            // TODO: each arch should check the ident to decide which register to
                            // allocate. We use a simple temporary register allocator for now.
                            let register = format!("x{}", reg_counter);
                            reg_counter += 1;
                            register
                        }
                        parser::RegisterKind::String(reg) => reg.clone(),
                    };

                    let regalloc = RegAllocation {
                        register: register.clone(),
                        expr: expr.clone(),
                        is_input: *is_input,
                        is_output: *is_output,
                    };

                    placeholder_instantiation.insert(ident.to_string(), register);
                    register_allocation.push(regalloc);
                }
                OperandKind::Symbol { path } => {
                    let ident = if let Some(ident) = ident {
                        ident.to_string()
                    } else {
                        todo!("Handle operands without identifiers")
                    };
                    let sym = format!("sym({})", ident);
                    symbols.insert(sym.clone(), path.to_owned());
                    placeholder_instantiation.insert(ident, sym);
                }
                OperandKind::Const(expr) => {
                    let ident = if let Some(ident) = ident {
                        ident.to_string()
                    } else {
                        todo!("Handle operands without identifiers")
                    };
                    let cst = format!("const({})", ident);
                    consts.insert(cst.clone(), expr.clone());
                    placeholder_instantiation.insert(ident, cst);
                }
            }
        }
    }

    OperandMappings(
        register_allocation,
        placeholder_instantiation,
        symbols,
        consts,
    )
}

fn analyze_multi_instructions(
    assembly_template: &[String],
    operands: &[AsmOperand],
) -> Result<MultiInstructionAnalysis> {
    static RE: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"\{\s*([A-Za-z0-9_]+)\s*\}").unwrap());

    let OperandMappings(register_allocation, placeholder_instantiation, symbols, consts) =
        build_operand_register_map(operands);
    let asm_lines = parse_instructions(assembly_template)?;

    // For now we only handle instructions
    let mut instructions = asm_lines
        .into_iter()
        .map(|line| match line {
            AsmLine::Instr(instr) => instr,
        })
        .collect::<Vec<_>>();

    // Replace all placeholder by the allocated register
    for instr in &mut instructions {
        for op in &mut instr.operands {
            for caps in RE.captures_iter(&op.clone()) {
                // Note: groups 0 and 1 are always present in this regex
                let substr = caps.get(0).unwrap().as_str();
                let placeholder = caps.get(1).unwrap().as_str();
                if let Some(reg) = placeholder_instantiation.get(placeholder) {
                    *op = op.replacen(substr, reg, 1);
                }
            }
        }
    }

    Ok(MultiInstructionAnalysis {
        instructions,
        register_allocation,
        symbols,
        consts,
    })
}

fn generate_softcore_code(analysis: &MultiInstructionAnalysis) -> proc_macro2::TokenStream {
    let syms = &analysis.symbols;
    let consts = &analysis.consts;
    let mut setup_code = Vec::new();
    let mut instruction_code = Vec::new();
    let mut extract_code = Vec::new();

    // Generate setup code for input registers
    for reg_alloc in &analysis.register_allocation {
        if reg_alloc.is_input {
            let reg = riscv::emit_reg(&reg_alloc.register);
            let expr = &reg_alloc.expr;
            setup_code.push(quote! {
                core.set(#reg, #expr as u64);
            });
        }
    }

    // Generate instruction execution code using proper register mapping
    for instr in analysis.instructions.iter() {
        let tokens = match riscv::emit_softcore_instr(instr, syms, consts) {
            Ok(tokens) => tokens,
            Err(err) => err.to_compile_error(),
        };
        instruction_code.push(tokens);
    }

    // Generate extraction code for output registers
    for reg_alloc in &analysis.register_allocation {
        if reg_alloc.is_output {
            let reg = riscv::emit_reg(&reg_alloc.register);
            let expr = &reg_alloc.expr;
            extract_code.push(quote! {
                #expr = core.get(#reg);
            });
        }
    }

    quote! {
        SOFT_CORE.with_borrow_mut(|core| {
            #(#setup_code)*
            #(#instruction_code)*
            #(#extract_code)*
        })
    }
}

#[proc_macro]
pub fn rasm(input: TokenStream) -> TokenStream {
    let asm_input = parse_macro_input!(input as AsmInput);

    // Extract the assembly string
    let assembly_strings = asm_input
        .template
        .iter()
        .map(|s| s.value())
        .collect::<Vec<String>>();

    // Analyze instructions for multi-instruction and CSR support
    let analysis = match analyze_multi_instructions(&assembly_strings, &asm_input.operands) {
        Ok(analysis) => analysis,
        Err(err) => {
            let err = syn::Error::new(Span::call_site(), err.to_string()).to_compile_error();
            return quote! {#err}.into();
        }
    };
    let softcore_code = generate_softcore_code(&analysis);
    quote! {
        {
            #[allow(unused_imports)]
            use softcore_rv64::{
                ast,
                prelude::bv,
                registers as reg,
                raw::{iop, rop, csr_name_map_backwards, self},
            };
            #softcore_code
        }
    }
    .into()
}
