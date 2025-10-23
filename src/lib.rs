use anyhow::{Result, anyhow};
use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use regex::Regex;
use std::collections::HashMap;
use std::sync::LazyLock;
use syn::{Expr, Path, parse_macro_input};

mod arch;
mod asm_parser;
mod macro_parser;
mod relooper;
mod riscv;

use arch::Arch;
use asm_parser::{AsmLine, Instr, into_asm_line};
use macro_parser::{AsmInput, AsmOperand, KindRegister, OperandKind, RegisterOperand};

use crate::relooper::{Conditional, Shape, StructuredProgram};

// ———————————————————————————— Compiler Driver ————————————————————————————— //

struct Context<A> {
    pub register_allocation: Vec<RegAllocation>,
    pub symbols: HashMap<String, Path>,
    pub consts: HashMap<String, Expr>,
    pub softcore: Expr,
    #[allow(unused)]
    pub arch: A,
}

fn as_to_rust<A: Arch>(asm: AsmInput, arch: A) -> Result<StructuredProgram<A>> {
    // Extract the assembly string
    let assembly_strings = asm
        .template
        .iter()
        .map(|s| s.value())
        .collect::<Vec<String>>();

    parse_raw_assembly(&assembly_strings, &asm.operands, arch)?
        .into_basic_blocks()?
        .into_cfg()?
        .into_structured()
}

// ——————————————————————————————— Proc Macro ——————————————————————————————— //

#[derive(Clone)]
struct RegAllocation {
    register: String, // "x1", "x2", etc.
    expr: Expr,       // The Rust expression (e.g. variable) for the register
    is_input: bool,
    is_output: bool,
}

struct ParsedAssembly<A> {
    asm_lines: Vec<AsmLine>,
    ctx: Context<A>,
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

fn build_operand_register_map<A>(
    operands: &[AsmOperand],
    arch: A,
) -> Result<(Context<A>, HashMap<String, String>)> {
    let mut register_allocation = Vec::new();
    let mut placeholder_instantiation = HashMap::new();
    let mut softcore = None;
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
                        macro_parser::RegisterKind::Ident(_ident) => {
                            // TODO: each arch should check the ident to decide which register to
                            // allocate. We use a simple temporary register allocator for now.
                            let register = format!("x{}", reg_counter);
                            reg_counter += 1;
                            register
                        }
                        macro_parser::RegisterKind::String(reg) => reg.clone(),
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
        } else if let AsmOperand::Softcore(expr) = operand {
            softcore = Some(expr);
        }
    }

    let Some(softcore) = softcore.cloned() else {
        return Err(anyhow!("Missing 'softcore' argument"));
    };

    Ok((
        Context {
            register_allocation,
            symbols,
            consts,
            arch,
            softcore,
        },
        placeholder_instantiation,
    ))
}

fn parse_raw_assembly<A>(
    assembly_template: &[String],
    operands: &[AsmOperand],
    arch: A,
) -> Result<ParsedAssembly<A>> {
    static RE: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"\{\s*([A-Za-z0-9_]+)\s*\}").unwrap());

    let (ctx, placeholder_instantiation) = build_operand_register_map(operands, arch)?;
    let mut asm_lines = parse_instructions(assembly_template)?;

    // Replace all placeholder by the allocated register
    for line in &mut asm_lines {
        let AsmLine::Instr(instr) = line else {
            continue;
        };
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

    Ok(ParsedAssembly { asm_lines, ctx })
}

fn generate_softcore_code<A: Arch>(prog: StructuredProgram<A>) -> proc_macro2::TokenStream {
    let mut setup_code = Vec::new();
    let mut extract_code = Vec::new();
    let mut assignments = Vec::new();

    // Generate setup code for input registers
    for reg_alloc in &prog.ctx.register_allocation {
        if reg_alloc.is_input {
            let reg = riscv::emit_reg(&reg_alloc.register);
            let expr = &reg_alloc.expr;
            setup_code.push(quote! {
                core.set(#reg, #expr as u64);
            });
        }
    }

    // Generate the Rust code corresponding to the assembly
    let instruction_code = generate_structured_code(&prog.shape, &prog.ctx);

    // Generate extraction code for output registers
    for reg_alloc in &prog.ctx.register_allocation {
        if reg_alloc.is_output {
            let reg = riscv::emit_reg(&reg_alloc.register);
            let expr = &reg_alloc.expr;

            // Skip assigning values to `_`
            if let Expr::Infer(_) = expr {
                continue;
            }

            extract_code.push(quote! { core.get(#reg) as _ });
            assignments.push(expr);
        }
    }

    // Get the softcore accessor
    let softcore = prog.ctx.softcore;

    if assignments.is_empty() {
        // No assignment, simply execute the instructions
        quote! {
            #softcore(|core| {
                #(#setup_code)*
                #instruction_code
            });
        }
    } else {
        // Return the assigned values from the closure, and assign them to the target variables
        quote! {
            (#(#assignments,)*) = #softcore(|core| {
                #(#setup_code)*
                #instruction_code
                (#(#extract_code,)*)
            });
        }
    }
}

fn generate_structured_code<A: Arch>(shape: &Shape, ctx: &Context<A>) -> proc_macro2::TokenStream {
    match shape {
        relooper::Shape::Block { instrs, next } => {
            let mut code = proc_macro2::TokenStream::new();
            for instr in instrs {
                let tokens = match riscv::emit_softcore_instr(instr, ctx) {
                    Ok(tokens) => tokens,
                    Err(err) => err.to_compile_error(),
                };
                code.extend(tokens);
            }
            if let Some(next_shape) = next {
                code.extend(generate_structured_code(next_shape, ctx))
            }
            code
        }
        relooper::Shape::If {
            cond,
            then_branch,
            else_branch,
            next,
        } => {
            let cond = A::emit_cond(cond);
            let then_branch = generate_structured_code(then_branch, ctx);
            let else_branch = else_branch
                .as_ref()
                .map(|x| generate_structured_code(x, ctx));
            let next = next.as_ref().map(|x| generate_structured_code(x, ctx));

            quote! {
                if #cond {
                    #then_branch
                } else {
                    #else_branch
                }
                #next
            }
        }
    }
}

#[proc_macro]
pub fn asm(input: TokenStream) -> TokenStream {
    let asm_input = parse_macro_input!(input as AsmInput);
    let arch = riscv::Riscv {}; // We only support RISC-V for now

    let assembly = match as_to_rust(asm_input, arch) {
        Ok(asm) => asm,
        Err(err) => {
            let err = syn::Error::new(Span::call_site(), err.to_string()).to_compile_error();
            return quote! {#err}.into();
        }
    };

    let softcore_code = generate_softcore_code(assembly);
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
