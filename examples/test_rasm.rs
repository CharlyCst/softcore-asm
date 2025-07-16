use rasm::rasm;

fn main() {
    // Test 1: Simple RISC-V instruction
    rasm!("addi x1, x2, 42");
    
    // Test 2: Multiple instructions
    rasm!("li x1, 100");
    
    // Test 3: Load/store operations
    rasm!("lw x1, 0(x2)");
    
    // Test 4: Branch instruction
    rasm!("beq x1, x2, label");
    
    // Test 5: Instruction with simple operand
    let x = 5;
    rasm!("addi x1, x2, {}", x);
    
    println!("All tests completed!");
}
