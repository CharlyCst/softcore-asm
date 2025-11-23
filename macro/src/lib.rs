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
use asm_parser::{AsmLine, Instr, parse_instructions};
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
    register: String,          // "x1", "x2", etc.
    input_expr: Option<Expr>,  // The Rust expression for input (when Some)
    output_expr: Option<Expr>, // The Rust expression for output (when Some)
}

struct ParsedAssembly<A> {
    asm_lines: Vec<AsmLine>,
    ctx: Context<A>,
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
                    input_expr,
                    output_expr,
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
                        input_expr: input_expr.clone(),
                        output_expr: output_expr.clone(),
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
    let mut output_registers = Vec::new();
    let mut assignments = Vec::new();

    // Generate setup code for input registers
    for reg_alloc in &prog.ctx.register_allocation {
        if let Some(expr) = &reg_alloc.input_expr {
            let reg = A::emit_reg(&reg_alloc.register);
            setup_code.push(quote! {
                core.set(#reg, #expr as u64);
            });
        }
    }

    // Generate the Rust code corresponding to the assembly
    let instruction_code = generate_structured_code(&prog.shape, &prog.ctx);

    // Generate extraction code for output registers
    for reg_alloc in &prog.ctx.register_allocation {
        if let Some(expr) = &reg_alloc.output_expr {
            // Skip assigning values to `_`
            if let Expr::Infer(_) = expr {
                continue;
            }

            output_registers.push(reg_alloc.register.as_str());
            assignments.push(expr);
        }
    }

    let prologue = if setup_code.is_empty() {
        quote! {}
    } else {
        generate_softcore_block(quote! { #(#setup_code)* }, &[], &prog.ctx)
    };
    let epilogue = if output_registers.is_empty() {
        quote! {}
    } else {
        let epilogue_block = generate_softcore_block(quote! {}, &output_registers, &prog.ctx);
        quote! {
            (#(#assignments,)*) = #epilogue_block;
        }
    };

    // Assemble the whole program
    quote! {
        // We initialize the registers with variable values
        #prologue
        // We emit the Rust program that emulates the instructions
        #instruction_code
        // We extract the output registers into Rust variables
        #epilogue
    }
}

fn generate_softcore_block<A: Arch>(
    instruction_code: proc_macro2::TokenStream,
    output_registers: &[&str],
    ctx: &Context<A>,
) -> proc_macro2::TokenStream {
    // Get the softcore accessor
    let softcore = &ctx.softcore;

    let mut regs = Vec::with_capacity(output_registers.len());
    for r in output_registers {
        let r = A::emit_reg(r);
        regs.push(quote! { core.get(#r) as _ });
    }

    quote! {
        #softcore(|core| {
            #instruction_code
            (#(#regs,)*)
        });
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
            let block = generate_softcore_block(code, &[], ctx);
            let next = if let Some(next_shape) = next {
                generate_structured_code(next_shape, ctx)
            } else {
                quote! {}
            };

            quote! {
                // The instructions from that block
                #block

                // The rest of the code
                #next
            }
        }
        relooper::Shape::FnCall { next, call } => {
            let fun = &call.fn_path;
            let abi = &call.abi;

            // Create identifiers for the function arguments
            let mut args = Vec::new();
            for i in 0..call.num_args {
                let arg = proc_macro2::Ident::new(&format!("arg{i}"), Span::call_site());
                args.push(quote! { #arg });
            }

            // Create the function type
            let args_placeholders = vec![quote! { _ }; call.num_args as usize];
            let ret = if call.noreturn {
                quote! { -> ! }
            } else {
                quote! {}
            };

            // Create a block to extract the arguments, and the next block to execute
            let extract_args_block =
                generate_softcore_block(quote! {}, A::abi_registers(abi, call.num_args), ctx);
            let next = next.as_ref().map(|x| generate_structured_code(x, ctx));

            quote! {
                // Extract the arguments from the registers
                let (#(#args,)*) = #extract_args_block;

                // We try to coerce the function to force a type-check.
                // In particular, we want to be sure no values are returned, as we do not
                // handle return value yet (besite returning `!`).
                let _: extern #abi fn(#(#args_placeholders ,)*) #ret = #fun;

                // Actually call the function
                #fun(#(#args,)*);

                // We are done, continue
                #next
            }
        }
        relooper::Shape::If {
            cond,
            then_branch,
            else_branch,
            next,
        } => {
            // First, write a softcore block to extract the necessary registers
            let [left, right] = cond.get_regs();
            let extract_regs = generate_softcore_block(quote! {}, &[left, right], ctx);

            // Build the condition
            let left = quote! { left };
            let right = quote! { right };
            let cond = generade_cond(cond, &left, &right, ctx);

            let then_branch = generate_structured_code(then_branch, ctx);
            let else_branch = else_branch
                .as_ref()
                .map(|x| generate_structured_code(x, ctx));
            let next = next.as_ref().map(|x| generate_structured_code(x, ctx));

            quote! {
                let (#left, #right): (u64, u64) = #extract_regs;
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

fn generade_cond<A: Arch>(
    cond: &Conditional,
    left: &proc_macro2::TokenStream,
    right: &proc_macro2::TokenStream,
    _ctx: &Context<A>,
) -> proc_macro2::TokenStream {
    match cond {
        Conditional::Eq(_, _) => quote! { #left == #right },
        Conditional::Ne(_, _) => quote! { #left != #right },
        Conditional::Lt(_, _) => quote! { #left <  #right },
        Conditional::Ge(_, _) => quote! { #left >= #right },
        Conditional::Ltu(_, _) => todo!("LTU conditionnal not supported"),
        Conditional::Geu(_, _) => todo!("GEU conditionnal not supported"),
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
            use ::softcore_asm_rv64::softcore_rv64::{
                Core,
                ast,
                prelude::bv,
                registers as reg,
                raw::{iop, rop, sop, csr_name_map_backwards, self},
            };
            use ::softcore_asm_rv64::AsmCallable;
            #softcore_code
        }
    }
    .into()
}
