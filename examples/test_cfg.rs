use rasm::rasm;

fn main() {
    println!("Testing cfg conditions...");
    
    // Test if we're on RISC-V
    #[cfg(target_arch = "riscv64")]
    println!("Running on RISC-V 64-bit target");
    
    #[cfg(not(target_arch = "riscv64"))]
    println!("Running on non-RISC-V target");
    
    // Test our macro
    rasm!("li x1, 42");
    
    println!("CFG test completed!");
}