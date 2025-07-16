use rasm::rasm;

fn main() {
    println!("Testing macro expansion...");
    
    // This will expand to conditional assembly on RISC-V targets
    let value = 42;
    rasm!("li x1, {}", value);
    
    println!("Expansion test completed!");
}