use proc_macro::TokenStream;
use quote::quote;
use regex::Regex;
use std::collections::HashMap;
use std::sync::LazyLock;
use syn::{Expr, Path, parse_macro_input};

mod parser;
mod riscv;

use parser::{AsmInput, AsmOperand};

use crate::parser::{KindRegister, OperandKind, RegisterOperand};

#[derive(Debug, Clone)]
struct InstructionInfo {
    instr: String,         // "csrrw"
    operands: Vec<String>, // ["x1", "mscratch", "{x}"]
}

#[derive(Clone)]
struct RegAllocation {
    register: String, // "x1", "x2", etc.
    expr: Expr,       // The Rust expression (e.g. variable) for the register
    is_input: bool,
    is_output: bool,
}

struct MultiInstructionAnalysis {
    instructions: Vec<InstructionInfo>,
    register_allocation: Vec<RegAllocation>,
    symbols: HashMap<String, Path>,
}

fn parse_instruction(instr: &str) -> Option<InstructionInfo> {
    let mut splitter = instr.splitn(2, |c: char| c.is_whitespace());
    let instr = splitter.next()?.trim().to_string();
    let operands = splitter
        .next()?
        .split(',')
        .map(|op| op.trim().to_string())
        .collect::<Vec<String>>();

    Some(InstructionInfo { instr, operands })
}

fn parse_instructions(assembly_template: &[String]) -> Vec<InstructionInfo> {
    let asm_text = assembly_template.join("\n");
    let lines: Vec<&str> = asm_text
        .lines()
        .map(|line| line.trim())
        .filter(|line| !line.is_empty() || line.starts_with("//"))
        .collect();

    let mut instrs = Vec::with_capacity(lines.len());
    for line in lines {
        let Some(instr) = parse_instruction(line) else {
            eprintln!("Invalid assembly: '{}'", line);
            continue;
        };
        instrs.push(instr);
    }
    instrs
}

fn build_operand_register_map(
    operands: &[AsmOperand],
) -> (
    Vec<RegAllocation>,
    HashMap<String, String>,
    HashMap<String, Path>,
) {
    let mut register_allocation = Vec::new();
    let mut placeholder_instantiation = HashMap::new();
    let mut symbols = HashMap::new();
    let mut reg_counter = 1;

    for operand in operands.iter() {
        if let AsmOperand::Register(RegisterOperand { ident, kind }) = operand {
            let ident = if let Some(ident) = ident {
                ident
            } else {
                todo!("Handle operands without identifiers")
            };
            match kind {
                OperandKind::Register(KindRegister {
                    reg: _, // TODO: check if the user specifies a register
                    expr,
                    is_input,
                    is_output,
                }) => {
                    // Pick the next available register
                    let register = format!("x{}", reg_counter);
                    let regalloc = RegAllocation {
                        register: register.clone(),
                        expr: expr.clone(),
                        is_input: *is_input,
                        is_output: *is_output,
                    };

                    placeholder_instantiation.insert(ident.to_string(), register);
                    register_allocation.push(regalloc);
                    reg_counter += 1;
                }
                OperandKind::Symbol { path } => {
                    let ident = ident.to_string();
                    let sym = format!("sym({})", ident);
                    symbols.insert(sym.clone(), path.to_owned());
                    placeholder_instantiation.insert(ident, sym);
                }
            }
        }
    }

    (register_allocation, placeholder_instantiation, symbols)
}

fn analyze_multi_instructions(
    assembly_template: &[String],
    operands: &[AsmOperand],
) -> MultiInstructionAnalysis {
    static RE: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"\{\s*([A-Za-z0-9_]+)\s*\}").unwrap());

    let (register_allocation, placeholder_instantiation, symbols) =
        build_operand_register_map(operands);
    let mut instructions = parse_instructions(assembly_template);

    // Replace all placeholder by the allocated register
    for instr in &mut instructions {
        for op in &mut instr.operands {
            for caps in RE.captures_iter(&op.clone()) {
                // Note: groups 0 and 1 are always present in this regex
                let substr = caps.get(0).unwrap().as_str();
                let placeholder = caps.get(1).unwrap().as_str();
                if let Some(reg) = placeholder_instantiation.get(placeholder) {
                    *op = op.replacen(substr, reg, 1);
                } else if symbols.contains_key(placeholder) {
                    eprintln!("### {placeholder}");
                    *op = op.replacen(substr, &format!("sym({placeholder})"), 1);
                }
            }
        }
    }

    MultiInstructionAnalysis {
        instructions,
        register_allocation,
        symbols,
    }
}

fn generate_softcore_code(analysis: &MultiInstructionAnalysis) -> proc_macro2::TokenStream {
    let syms = &analysis.symbols;
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
        let tokens = match riscv::emit_softcore_instr(instr, syms) {
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
    let analysis = analyze_multi_instructions(&assembly_strings, &asm_input.operands);
    let softcore_code = generate_softcore_code(&analysis);
    quote! {
        {
            #softcore_code
        }
    }
    .into()
}
