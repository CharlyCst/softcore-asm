use proc_macro::TokenStream;
use quote::quote;
use std::collections::HashMap;
use syn::{
    Expr, Ident, LitStr, Token,
    parse::{Parse, ParseStream, Result},
    parse_macro_input,
};

#[derive(Clone)]
enum AsmOperand {
    Input {
        name: Option<Ident>,
        reg: Ident,
        expr: Expr,
    },
    Output {
        name: Option<Ident>,
        reg: Ident,
        expr: Expr,
    },
    InOut {
        name: Option<Ident>,
        reg: Ident,
        expr: Expr,
    },
    Options(Expr),
    Raw(Expr),
}

struct AsmInput {
    template: LitStr,
    operands: Vec<AsmOperand>,
    options: Vec<String>,
}

#[derive(Debug, Clone)]
struct InstructionInfo {
    instruction: String,       // "csrrw"
    placeholders: Vec<String>, // ["{prev}", "{x}"]
    csr_name: Option<String>,  // Some("mscratch")
    is_csr: bool,              // true
    is_load: bool,             // true
    is_store: bool,
}

#[derive(Debug, Clone)]
struct RegAllocation {
    operand_index: usize,
    register: String, // "X1", "X2", etc.
    is_input: bool,
    is_output: bool,
}

#[derive(Debug)]
struct InstructionOperandMapping {
    operand_registers: HashMap<String, String>, // "{prev1}" -> "X2"
}

#[derive(Debug)]
struct MultiInstructionAnalysis {
    instructions: Vec<InstructionInfo>,
    register_allocation: Vec<RegAllocation>,
    instruction_mappings: Vec<InstructionOperandMapping>,
    has_csr_operations: bool,
    has_memory_operations: bool,
}

impl Parse for AsmOperand {
    fn parse(input: ParseStream) -> Result<Self> {
        // Check for named operand: "name = direction(reg) expr"
        if input.peek(Ident) && input.peek2(Token![=]) {
            let name = input.parse::<Ident>()?;
            input.parse::<Token![=]>()?;

            // Now parse the direction(reg) expr part
            if input.peek(Token![in]) {
                input.parse::<Token![in]>()?;
                let content;
                syn::parenthesized!(content in input);
                let reg = content.parse::<Ident>()?;
                let expr = input.parse::<Expr>()?;
                Ok(AsmOperand::Input {
                    name: Some(name),
                    reg,
                    expr,
                })
            } else if input.peek(Ident) && input.peek2(syn::token::Paren) {
                let ident = input.parse::<Ident>()?;
                match ident.to_string().as_str() {
                    "out" => {
                        let content;
                        syn::parenthesized!(content in input);
                        let reg = content.parse::<Ident>()?;
                        let expr = input.parse::<Expr>()?;
                        Ok(AsmOperand::Output {
                            name: Some(name),
                            reg,
                            expr,
                        })
                    }
                    "inout" => {
                        let content;
                        syn::parenthesized!(content in input);
                        let reg = content.parse::<Ident>()?;
                        let expr = input.parse::<Expr>()?;
                        Ok(AsmOperand::InOut {
                            name: Some(name),
                            reg,
                            expr,
                        })
                    }
                    _ => {
                        return Err(input.error("Expected operand specification after name ="));
                    }
                }
            } else {
                return Err(input.error("Expected direction specification after name ="));
            }
        }
        // Check for options(...)
        else if input.peek(Ident) {
            let ident = input.fork().parse::<Ident>()?;
            if ident == "options" && input.peek2(syn::token::Paren) {
                input.parse::<Ident>()?; // consume "options"
                let content;
                syn::parenthesized!(content in input);
                // Parse the entire content as a single expression (handles comma-separated values)
                let remaining_tokens = content.parse::<proc_macro2::TokenStream>()?;
                let expr: Expr = syn::parse2(quote! { (#remaining_tokens) })?;
                Ok(AsmOperand::Options(expr))
            } else if input.peek2(syn::token::Paren) {
                // Handle non-named operand specifications (out/inout)
                let ident = input.parse::<Ident>()?;
                match ident.to_string().as_str() {
                    "out" => {
                        let content;
                        syn::parenthesized!(content in input);
                        let reg = content.parse::<Ident>()?;
                        let expr = input.parse::<Expr>()?;
                        Ok(AsmOperand::Output {
                            name: None,
                            reg,
                            expr,
                        })
                    }
                    "inout" => {
                        let content;
                        syn::parenthesized!(content in input);
                        let reg = content.parse::<Ident>()?;
                        let expr = input.parse::<Expr>()?;
                        Ok(AsmOperand::InOut {
                            name: None,
                            reg,
                            expr,
                        })
                    }
                    _ => {
                        // Parse as raw expression
                        let expr = input.parse::<Expr>()?;
                        Ok(AsmOperand::Raw(expr))
                    }
                }
            } else {
                // Parse as raw expression
                let expr = input.parse::<Expr>()?;
                Ok(AsmOperand::Raw(expr))
            }
        }
        // Try to parse 'in' keyword specifically (since 'in' is a keyword in Rust)
        else if input.peek(Token![in]) {
            input.parse::<Token![in]>()?;
            let content;
            syn::parenthesized!(content in input);
            let reg = content.parse::<Ident>()?;
            let expr = input.parse::<Expr>()?;
            Ok(AsmOperand::Input {
                name: None,
                reg,
                expr,
            })
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
        let mut options = Vec::new();

        while !input.is_empty() {
            input.parse::<Token![,]>()?;
            if input.is_empty() {
                break;
            }
            let operand = input.parse::<AsmOperand>()?;
            if let AsmOperand::Options(expr) = &operand {
                if let Expr::Tuple(tuple) = expr {
                    for elem in &tuple.elems {
                        if let Expr::Path(path) = elem {
                            if let Some(ident) = path.path.get_ident() {
                                options.push(ident.to_string());
                            }
                        }
                    }
                }
            }
            operands.push(operand);
        }

        Ok(AsmInput { template, operands, options })
    }
}

fn validate_risc_v_instruction(instruction: &str) -> Vec<String> {
    let mut warnings = Vec::new();

    // Basic RISC-V instruction validation
    let common_instructions = [
        "add", "sub", "mul", "div", "rem", "addi", "subi", "andi", "ori", "xori", "sll", "srl",
        "sra", "slli", "srli", "srai", "lw", "sw", "lb", "sb", "lh", "sh", "beq", "bne", "blt",
        "bge", "bltu", "bgeu", "jal", "jalr", "lui", "auipc", "li", "mv", "nop", "ld", "sd",
        // CSR instructions
        "csrr", "csrw", "csrs", "csrc", "csrri", "csrwi", "csrsi", "csrci", "csrrw", "csrrs",
        "csrrc", "csrrwi", "csrrsi", "csrrci",
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
        "x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13",
        "x14", "x15", "x16", "x17", "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26",
        "x27", "x28", "x29", "x30", "x31", "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0",
        "s1", "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
        "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6",
        "reg", // Generic register placeholder
    ];

    if !valid_regs.contains(&reg) {
        warnings.push(format!("Unknown RISC-V register: {}", reg));
    }

    warnings
}

fn is_csr_instruction(instruction: &str) -> bool {
    let csr_instructions = [
        "csrr", "csrw", "csrs", "csrc", "csrri", "csrwi", "csrsi", "csrci", "csrrw", "csrrs",
        "csrrc", "csrrwi", "csrrsi", "csrrci",
    ];

    let parts: Vec<&str> = instruction.split_whitespace().collect();
    if let Some(op) = parts.first() {
        csr_instructions.contains(op)
    } else {
        false
    }
}

fn is_load_instruction(instruction: &str) -> bool {
    let load_instructions = ["lw", "ld", "lh", "lb"];

    let parts: Vec<&str> = instruction.split_whitespace().collect();
    if let Some(op) = parts.first() {
        load_instructions.contains(op)
    } else {
        false
    }
}

fn is_store_instruction(instruction: &str) -> bool {
    let store_instructions = ["sw", "sd", "sh", "sb"];

    let parts: Vec<&str> = instruction.split_whitespace().collect();
    if let Some(op) = parts.first() {
        store_instructions.contains(op)
    } else {
        false
    }
}

fn extract_csr_name(instruction: &str) -> Option<String> {
    let parts: Vec<&str> = instruction.split_whitespace().collect();
    
    // Early return if not a valid CSR instruction
    if parts.len() < 2 || !is_csr_instruction(instruction) {
        return None;
    }
    
    let opcode = parts[0];
    
    // Determine CSR position based on instruction format:
    // 2-operand: "csrw csr, rs" -> CSR at index 1
    // 3-operand: "csrrw rd, csr, rs" -> CSR at index 2
    let csr_index = match opcode {
        "csrw" | "csrs" | "csrc" | "csrwi" | "csrsi" | "csrci" => {
            if parts.len() >= 2 { 1 } else { return None; }
        }
        "csrrw" | "csrrs" | "csrrc" | "csrrwi" | "csrrsi" | "csrrci" | "csrr" | "csrri" => {
            if parts.len() >= 3 { 2 } else { return None; }
        }
        _ => return None,
    };
    
    let csr_part = parts[csr_index].trim_end_matches(',');
    
    // Return CSR name only if it's not a placeholder
    if csr_part.starts_with('{') && csr_part.ends_with('}') {
        None
    } else {
        Some(csr_part.to_string())
    }
}

fn extract_placeholders(instruction: &str) -> Vec<String> {
    let mut placeholders = Vec::new();
    let mut chars = instruction.chars().peekable();

    while let Some(&ch) = chars.peek() {
        if ch == '{' {
            chars.next(); // consume '{'
            let mut placeholder = String::new();

            while let Some(&ch) = chars.peek() {
                if ch == '}' {
                    chars.next(); // consume '}'
                    break;
                }
                placeholder.push(chars.next().unwrap());
            }

            if !placeholder.is_empty() {
                placeholders.push(format!("{{{}}}", placeholder));
            }
        } else {
            chars.next();
        }
    }

    placeholders
}

fn parse_instructions(assembly_template: &str) -> Vec<InstructionInfo> {
    let instructions: Vec<&str> = assembly_template
        .lines()
        .map(|line| line.trim())
        .filter(|line| !line.is_empty())
        .collect();

    instructions
        .iter()
        .map(|instruction| {
            let is_csr = is_csr_instruction(instruction);
            let is_load = is_load_instruction(instruction);
            let is_store = is_store_instruction(instruction);
            let csr_name = extract_csr_name(instruction);
            let placeholders = extract_placeholders(instruction);

            InstructionInfo {
                instruction: instruction.to_string(),
                placeholders,
                csr_name,
                is_csr,
                is_load,
                is_store,
            }
        })
        .collect()
}

fn build_operand_register_map(
    instructions: &[InstructionInfo],
    operands: &[AsmOperand],
) -> (Vec<RegAllocation>, Vec<InstructionOperandMapping>) {
    let mut register_allocation = Vec::new();
    let mut instruction_mappings = Vec::new();
    let mut reg_counter = 1;

    // Create a mapping from operand names to registers
    let mut operand_to_register = HashMap::new();

    // First pass: assign registers to all operands
    for (index, operand) in operands.iter().enumerate() {
        match operand {
            AsmOperand::Input {
                name: Some(name), ..
            } => {
                let register = format!("X{}", reg_counter);
                operand_to_register.insert(name.to_string(), register.clone());
                register_allocation.push(RegAllocation {
                    operand_index: index,
                    register,
                    is_input: true,
                    is_output: false,
                });
                reg_counter += 1;
            }
            AsmOperand::Output {
                name: Some(name), ..
            } => {
                let register = format!("X{}", reg_counter);
                operand_to_register.insert(name.to_string(), register.clone());
                register_allocation.push(RegAllocation {
                    operand_index: index,
                    register,
                    is_input: false,
                    is_output: true,
                });
                reg_counter += 1;
            }
            AsmOperand::InOut {
                name: Some(name), ..
            } => {
                let register = format!("X{}", reg_counter);
                operand_to_register.insert(name.to_string(), register.clone());
                register_allocation.push(RegAllocation {
                    operand_index: index,
                    register,
                    is_input: true,
                    is_output: true,
                });
                reg_counter += 1;
            }
            _ => {} // Skip Options and Raw for now
        }
    }

    // Second pass: create instruction mappings
    for instruction in instructions.iter() {
        let mut operand_registers = HashMap::new();

        // Map each placeholder to its register
        for placeholder in &instruction.placeholders {
            // Remove the braces to get the operand name
            let operand_name = placeholder.trim_start_matches('{').trim_end_matches('}');

            if let Some(register) = operand_to_register.get(operand_name) {
                operand_registers.insert(placeholder.clone(), register.clone());
            }
        }

        instruction_mappings.push(InstructionOperandMapping { operand_registers });
    }

    (register_allocation, instruction_mappings)
}

fn analyze_multi_instructions(
    assembly_template: &str,
    operands: &[AsmOperand],
) -> MultiInstructionAnalysis {
    let instructions = parse_instructions(assembly_template);
    let has_csr_operations = instructions.iter().any(|instr| instr.is_csr);
    let has_memory_operations = instructions.iter().any(|instr| instr.is_load || instr.is_store);

    // Build proper operand-to-register mapping
    let (register_allocation, instruction_mappings) =
        build_operand_register_map(&instructions, operands);

    MultiInstructionAnalysis {
        instructions,
        register_allocation,
        instruction_mappings,
        has_csr_operations,
        has_memory_operations,
    }
}

fn generate_softcore_code(
    analysis: &MultiInstructionAnalysis,
    operands: &[AsmOperand],
    options: &[String],
) -> proc_macro2::TokenStream {
    let mut setup_code = Vec::new();
    let mut instruction_code = Vec::new();
    let mut extract_code = Vec::new();

    // Generate setup code for input registers
    for reg_alloc in &analysis.register_allocation {
        if reg_alloc.is_input {
            if let Some(operand) = operands.get(reg_alloc.operand_index) {
                let reg_name = syn::parse_str::<syn::Ident>(&reg_alloc.register).unwrap();
                match operand {
                    AsmOperand::Input { expr, .. } | AsmOperand::InOut { expr, .. } => {
                        setup_code.push(quote! {
                            core.set(reg::#reg_name, #expr);
                        });
                    }
                    _ => {}
                }
            }
        }
    }

    // Generate instruction execution code using proper register mapping
    for (instr_index, instr) in analysis.instructions.iter().enumerate() {
        if instr.is_csr {
            if let Some(csr_name) = &instr.csr_name {
                let csr_name_str = csr_name.clone();

                // Find the mapping for this instruction
                if let Some(mapping) = analysis.instruction_mappings.get(instr_index) {
                    let parts: Vec<&str> = instr.instruction.split_whitespace().collect();
                    let opcode = parts[0];
                    
                    match opcode {
                        // 2-operand CSR instructions: "csrw csr, rs"
                        "csrw" | "csrs" | "csrc" | "csrwi" | "csrsi" | "csrci" => {
                            if parts.len() >= 3 {
                                let src_operand = parts[2].trim_end_matches(',');
                                
                                // Handle source operand  
                                let src_reg_code = if src_operand.starts_with('{') && src_operand.ends_with('}') {
                                    // It's a placeholder
                                    if let Some(src_reg) = mapping.operand_registers.get(src_operand) {
                                        let src_reg_name = syn::parse_str::<syn::Ident>(src_reg).unwrap();
                                        quote! { reg::#src_reg_name }
                                    } else {
                                        continue; // Skip if we can't find the register
                                    }
                                } else {
                                    // It's a literal register
                                    let src_reg_name = syn::parse_str::<syn::Ident>(&src_operand.to_uppercase()).unwrap();
                                    quote! { reg::#src_reg_name }
                                };
                                
                                // For csrw-style instructions, we use csrrw with x0 as destination
                                instruction_code.push(quote! {
                                    core.csrrw(reg::X0, csr_name_map_backwards(#csr_name_str).bits(), #src_reg_code).unwrap();
                                });
                            }
                        }
                        
                        // 3-operand CSR instructions: "csrrw rd, csr, rs" 
                        "csrrw" | "csrrs" | "csrrc" | "csrrwi" | "csrrsi" | "csrrci" | "csrr" | "csrri" => {
                            if parts.len() >= 4 {
                                let dest_operand = parts[1].trim_end_matches(',');
                                let src_operand = parts[3].trim_end_matches(',');

                                // Handle destination operand
                                let dest_reg_code = if dest_operand.starts_with('{') && dest_operand.ends_with('}') {
                                    // It's a placeholder
                                    if let Some(dest_reg) = mapping.operand_registers.get(dest_operand) {
                                        let dest_reg_name = syn::parse_str::<syn::Ident>(dest_reg).unwrap();
                                        quote! { reg::#dest_reg_name }
                                    } else {
                                        continue; // Skip if we can't find the register
                                    }
                                } else {
                                    // It's a literal register
                                    let dest_reg_name = syn::parse_str::<syn::Ident>(&dest_operand.to_uppercase()).unwrap();
                                    quote! { reg::#dest_reg_name }
                                };

                                // Handle source operand
                                let src_reg_code = if src_operand.starts_with('{') && src_operand.ends_with('}') {
                                    // It's a placeholder
                                    if let Some(src_reg) = mapping.operand_registers.get(src_operand) {
                                        let src_reg_name = syn::parse_str::<syn::Ident>(src_reg).unwrap();
                                        quote! { reg::#src_reg_name }
                                    } else {
                                        continue; // Skip if we can't find the register
                                    }
                                } else {
                                    // It's a literal register
                                    let src_reg_name = syn::parse_str::<syn::Ident>(&src_operand.to_uppercase()).unwrap();
                                    quote! { reg::#src_reg_name }
                                };

                                instruction_code.push(quote! {
                                    core.csrrw(#dest_reg_code, csr_name_map_backwards(#csr_name_str).bits(), #src_reg_code).unwrap();
                                });
                            }
                        }
                        
                        _ => {
                            // Unknown CSR instruction format
                            continue;
                        }
                    }
                }
            }
        } else if instr.is_load && !options.contains(&"nomem".to_string()) {
            if let Some(mapping) = analysis.instruction_mappings.get(instr_index) {
                let parts: Vec<&str> = instr.instruction.split_whitespace().collect();
                if parts.len() >= 2 {
                    let dest_operand = parts[1].trim_end_matches(',');
                    let mem_operand = parts[2].trim_end_matches(',');

                    let dest_reg = if dest_operand.starts_with('{') && dest_operand.ends_with('}') {
                        mapping.operand_registers.get(dest_operand)
                    } else {
                        None
                    };

                    let src_reg = if mem_operand.contains("{") && mem_operand.contains("}") {
                        let start = mem_operand.find('{').unwrap();
                        let end = mem_operand.find('}').unwrap();
                        let placeholder = &mem_operand[start..=end];
                        mapping.operand_registers.get(placeholder)
                    } else {
                        None
                    };

                    if let (Some(dest_reg), Some(src_reg)) = (dest_reg, src_reg) {
                        let dest_reg_name = syn::parse_str::<syn::Ident>(dest_reg).unwrap();
                        let src_reg_name = syn::parse_str::<syn::Ident>(src_reg).unwrap();
                        instruction_code.push(quote! {
                            let fresh1 = core.get(reg::#src_reg_name) as *const u64;
                            let fresh2: u64 = unsafe { *fresh1 };
                            core.set(reg::#dest_reg_name, fresh2);
                        });
                    }
                }
            }
        } else if instr.is_store && !options.contains(&"nomem".to_string()) {
            if let Some(mapping) = analysis.instruction_mappings.get(instr_index) {
                let parts: Vec<&str> = instr.instruction.split_whitespace().collect();
                if parts.len() >= 2 {
                    let src_operand = parts[1].trim_end_matches(',');
                    let mem_operand = parts[2].trim_end_matches(',');

                    let src_reg = if src_operand.starts_with('{') && src_operand.ends_with('}') {
                        mapping.operand_registers.get(src_operand)
                    } else {
                        None
                    };

                    let dest_reg = if mem_operand.contains("{") && mem_operand.contains("}") {
                        let start = mem_operand.find('{').unwrap();
                        let end = mem_operand.find('}').unwrap();
                        let placeholder = &mem_operand[start..=end];
                        mapping.operand_registers.get(placeholder)
                    } else {
                        None
                    };

                    if let (Some(dest_reg), Some(src_reg)) = (dest_reg, src_reg) {
                        let dest_reg_name = syn::parse_str::<syn::Ident>(dest_reg).unwrap();
                        let src_reg_name = syn::parse_str::<syn::Ident>(src_reg).unwrap();
                        instruction_code.push(quote! {
                            let fresh1 = core.get(reg::#dest_reg_name) as *mut u64;
                            let fresh2 = core.get(reg::#src_reg_name);
                            unsafe { *fresh1 = fresh2 };
                        });
                    }
                }
            }
        }
    }

    // Generate extraction code for output registers
    for reg_alloc in &analysis.register_allocation {
        if reg_alloc.is_output {
            if let Some(operand) = operands.get(reg_alloc.operand_index) {
                let reg_name = syn::parse_str::<syn::Ident>(&reg_alloc.register).unwrap();
                match operand {
                    AsmOperand::Output { expr, .. } | AsmOperand::InOut { expr, .. } => {
                        extract_code.push(quote! {
                            #expr = core.get(reg::#reg_name);
                        });
                    }
                    _ => {}
                }
            }
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
            AsmOperand::Input { name, reg, expr } => {
                if let Some(name) = name {
                    eprintln!(
                        "RASM: Operand {}: Named Input {}={} reg={}, expr={}",
                        i,
                        name,
                        reg,
                        reg,
                        quote!(#expr)
                    );
                } else {
                    eprintln!(
                        "RASM: Operand {}: Input reg={}, expr={}",
                        i,
                        reg,
                        quote!(#expr)
                    );
                }
                let reg_warnings = validate_risc_v_register(&reg.to_string());
                for warning in reg_warnings {
                    eprintln!("RASM WARNING: {}", warning);
                }
            }
            AsmOperand::Output { name, reg, expr } => {
                if let Some(name) = name {
                    eprintln!(
                        "RASM: Operand {}: Named Output {}={} reg={}, expr={}",
                        i,
                        name,
                        reg,
                        reg,
                        quote!(#expr)
                    );
                } else {
                    eprintln!(
                        "RASM: Operand {}: Output reg={}, expr={}",
                        i,
                        reg,
                        quote!(#expr)
                    );
                }
                let reg_warnings = validate_risc_v_register(&reg.to_string());
                for warning in reg_warnings {
                    eprintln!("RASM WARNING: {}", warning);
                }
            }
            AsmOperand::InOut { name, reg, expr } => {
                if let Some(name) = name {
                    eprintln!(
                        "RASM: Operand {}: Named InOut {}={} reg={}, expr={}",
                        i,
                        name,
                        reg,
                        reg,
                        quote!(#expr)
                    );
                } else {
                    eprintln!(
                        "RASM: Operand {}: InOut reg={}, expr={}",
                        i,
                        reg,
                        quote!(#expr)
                    );
                }
                let reg_warnings = validate_risc_v_register(&reg.to_string());
                for warning in reg_warnings {
                    eprintln!("RASM WARNING: {}", warning);
                }
            }
            AsmOperand::Options(expr) => {
                eprintln!("RASM: Operand {}: Options expr={}", i, quote!(#expr));
            }
            AsmOperand::Raw(expr) => {
                eprintln!("RASM: Operand {}: Raw expr={}", i, quote!(#expr));
            }
        }
    }

    // Analyze instructions for multi-instruction and CSR support
    let analysis = analyze_multi_instructions(&assembly_string, &asm_input.operands);
    eprintln!("{:#?}", analysis);

    // Generate conditional output based on target architecture and CSR operations
    let output = if analysis.has_csr_operations || analysis.has_memory_operations {
        let softcore_code = generate_softcore_code(&analysis, &asm_input.operands, &asm_input.options);
        quote! {
            {
                #[cfg(target_arch = "riscv64")]
                unsafe {
                    core::arch::asm!(#original_input)
                }

                #[cfg(feature = "softcore")]
                {
                    #softcore_code
                }
            }
        }
    } else {
        // Non-CSR instructions - existing behavior
        quote! {
            {
                #[cfg(target_arch = "riscv64")]
                unsafe {
                    core::arch::asm!(#original_input)
                }
            }
        }
    };
    output.into()
}
