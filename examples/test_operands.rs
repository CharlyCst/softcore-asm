use rasm::rasm;

fn main() {
    let x = 5;
    let mut y = 10;
    
    // Test complex operand parsing - remove spaces
    rasm!("add {}, {}, {}", in(reg) x, out(reg) y);
    
    println!("Advanced operand test completed!");
}