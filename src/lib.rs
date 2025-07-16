use proc_macro::TokenStream;
use quote::quote;
use syn::{
    parse::{Parse, ParseStream, Result},
    parse_macro_input,
    Expr, Ident, LitStr, Token,
};

#[derive(Clone)]
enum AsmOperand {
    Input { reg: Ident, expr: Expr },
    Output { reg: Ident, expr: Expr },
    InOut { reg: Ident, expr: Expr },
    Raw(Expr),
}

struct AsmInput {
    template: LitStr,
    operands: Vec<AsmOperand>,
}

impl Parse for AsmOperand {
    fn parse(input: ParseStream) -> Result<Self> {
        // Try to parse 'in' keyword specifically (since 'in' is a keyword in Rust)
        if input.peek(Token![in]) {
            input.parse::<Token![in]>()?;
            let content;
            syn::parenthesized!(content in input);
            let reg = content.parse::<Ident>()?;
            let expr = input.parse::<Expr>()?;
            Ok(AsmOperand::Input { reg, expr })
        } else if input.peek(Ident) && input.peek2(syn::token::Paren) {
            let ident = input.parse::<Ident>()?;
            match ident.to_string().as_str() {
                "out" => {
                    let content;
                    syn::parenthesized!(content in input);
                    let reg = content.parse::<Ident>()?;
                    let expr = input.parse::<Expr>()?;
                    Ok(AsmOperand::Output { reg, expr })
                }
                "inout" => {
                    let content;
                    syn::parenthesized!(content in input);
                    let reg = content.parse::<Ident>()?;
                    let expr = input.parse::<Expr>()?;
                    Ok(AsmOperand::InOut { reg, expr })
                }
                _ => {
                    // This shouldn't happen since we checked for Ident followed by Paren
                    return Err(input.error("Expected operand specification"));
                }
            }
        } else {
            // Parse as raw expression
            let expr = input.parse::<Expr>()?;
            Ok(AsmOperand::Raw(expr))
        }
    }
}

impl Parse for AsmInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let template = input.parse::<LitStr>()?;
        
        let mut operands = Vec::new();
        
        while !input.is_empty() {
            input.parse::<Token![,]>()?;
            if input.is_empty() {
                break;
            }
            operands.push(input.parse()?);
        }
        
        Ok(AsmInput { template, operands })
    }
}

fn validate_risc_v_instruction(instruction: &str) -> Vec<String> {
    let mut warnings = Vec::new();
    
    // Basic RISC-V instruction validation
    let common_instructions = [
        "add", "sub", "mul", "div", "rem",
        "addi", "subi", "andi", "ori", "xori",
        "sll", "srl", "sra", "slli", "srli", "srai",
        "lw", "sw", "lb", "sb", "lh", "sh",
        "beq", "bne", "blt", "bge", "bltu", "bgeu",
        "jal", "jalr", "lui", "auipc",
        "li", "mv", "nop"
    ];
    
    // Split instruction into parts
    let parts: Vec<&str> = instruction.split_whitespace().collect();
    if let Some(op) = parts.first() {
        if !common_instructions.contains(op) {
            warnings.push(format!("Unknown RISC-V instruction: {}", op));
        }
    }
    
    warnings
}

fn validate_risc_v_register(reg: &str) -> Vec<String> {
    let mut warnings = Vec::new();
    
    // Check for valid RISC-V register names
    let valid_regs = [
        "x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7",
        "x8", "x9", "x10", "x11", "x12", "x13", "x14", "x15",
        "x16", "x17", "x18", "x19", "x20", "x21", "x22", "x23",
        "x24", "x25", "x26", "x27", "x28", "x29", "x30", "x31",
        "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
        "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
        "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
        "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6",
        "reg" // Generic register placeholder
    ];
    
    if !valid_regs.contains(&reg) {
        warnings.push(format!("Unknown RISC-V register: {}", reg));
    }
    
    warnings
}

#[proc_macro]
pub fn rasm(input: TokenStream) -> TokenStream {
    // Store original input for re-emission
    let original_input: proc_macro2::TokenStream = input.clone().into();
    
    let asm_input = parse_macro_input!(input as AsmInput);
    
    // Extract the assembly string
    let assembly_string = asm_input.template.value();
    
    // Print the assembly string for debugging
    eprintln!("RASM: Extracted assembly string: '{}'", assembly_string);
    
    // Validate RISC-V instruction
    let instruction_warnings = validate_risc_v_instruction(&assembly_string);
    for warning in instruction_warnings {
        eprintln!("RASM WARNING: {}", warning);
    }
    
    // Print operands information
    eprintln!("RASM: Found {} operands", asm_input.operands.len());
    for (i, operand) in asm_input.operands.iter().enumerate() {
        match operand {
            AsmOperand::Input { reg, expr } => {
                eprintln!("RASM: Operand {}: Input reg={}, expr={}", i, reg, quote!(#expr));
                let reg_warnings = validate_risc_v_register(&reg.to_string());
                for warning in reg_warnings {
                    eprintln!("RASM WARNING: {}", warning);
                }
            }
            AsmOperand::Output { reg, expr } => {
                eprintln!("RASM: Operand {}: Output reg={}, expr={}", i, reg, quote!(#expr));
                let reg_warnings = validate_risc_v_register(&reg.to_string());
                for warning in reg_warnings {
                    eprintln!("RASM WARNING: {}", warning);
                }
            }
            AsmOperand::InOut { reg, expr } => {
                eprintln!("RASM: Operand {}: InOut reg={}, expr={}", i, reg, quote!(#expr));
                let reg_warnings = validate_risc_v_register(&reg.to_string());
                for warning in reg_warnings {
                    eprintln!("RASM WARNING: {}", warning);
                }
            }
            AsmOperand::Raw(expr) => {
                eprintln!("RASM: Operand {}: Raw expr={}", i, quote!(#expr));
            }
        }
    }
    
    // Generate conditional output based on target architecture
    let output = quote! {
        {
            #[cfg(target_arch = "riscv64")]
            unsafe {
                core::arch::asm!(#original_input)
            }
        }
    };
    output.into()
}
