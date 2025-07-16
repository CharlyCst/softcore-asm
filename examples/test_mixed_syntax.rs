use rasm::rasm;

fn main() {
    println!("Testing mixed named and positional operand syntax...");
    
    let input_val = 42;
    let mut output_val = 0;
    let temp = 100;
    
    // Test 1: Mixed named and positional operands
    rasm!("add {result}, {}, {temp}", 
          in(reg) input_val,          // Positional operand
          result = out(reg) output_val,  // Named operand
          temp = in(reg) temp);       // Named operand
    
    // Test 2: Named operands with options
    rasm!("csrrw {old}, mstatus, {new}",
          old = out(reg) output_val,
          new = in(reg) input_val,
          options(nomem, nostack));
    
    // Test 3: All positional
    rasm!("addi {}, {}, 10", 
          out(reg) output_val,
          in(reg) input_val);
    
    println!("Mixed syntax test completed!");
}