use rasm::rasm;

fn main() {
    println!("Testing RISC-V assembly validation...");
    
    // Valid RISC-V instructions
    rasm!("add x1, x2, x3");
    rasm!("lw t0, 0(sp)");
    rasm!("beq a0, a1, label");
    
    // Invalid instruction (should generate warning)
    rasm!("invalid_instruction x1, x2");
    
    // Valid instruction with operands
    let value = 42;
    rasm!("addi x1, x2, {}", value);
    
    // Valid operands with register validation
    let input_val = 10;
    let mut output_val = 0;
    rasm!("add {}, {}, {}", 
          in(reg) input_val,
          out(reg) output_val,
          in(invalid_reg) input_val); // Invalid register name - should warn
    
    println!("Validation tests completed!");
}