use core::cell::RefCell;
use rasm::rasm;
use std::thread_local;

use softcore_rv64::raw::csr_name_map_backwards;
use softcore_rv64::registers as reg;
use softcore_rv64::{Core, config, new_core};

// Each thread gets its own copy of the core, this prevent tests using different threads inside a
// same process to share the same core.
thread_local! {
    /// A software RISC-V core that emulates a real CPU.
    ///
    /// We use one core per thread to prevent interference among threads, such as when running
    /// `cargo test`. Therefore, the core lives in threat local storage and must be access using
    /// the `thread_loca!` API.
    ///
    /// Usage:
    ///
    /// ```
    /// SOFT_CORE.with_borrow_mut(|core| {
    ///     // The `core` can be accessed within the closure
    ///     core.set(reg::X1, 0x42);
    ///     core.csrrw(reg::X0, csr::MSCRATCH, reg::X1).unwrap();
    /// });
    /// ```
    pub static SOFT_CORE: RefCell<Core> = {
        let mut core = new_core(config::U74);
        core.reset();
        RefCell::new(core)
    };
}

fn main() {
    println!("Testing multiple CSR instructions...");

    let value1: u64 = 0x1111;
    let value2: u64 = 0x2222;
    let mut result1: u64 = 0;
    let mut result2: u64 = 0;

    // Test multiple CSR instructions in one macro
    rasm!(
        "csrrw {prev1}, mscratch, {x1}
         csrrw {prev2}, mstatus, {x2}",
        x1 = in(reg) value1,
        prev1 = out(reg) result1,
        x2 = in(reg) value2,
        prev2 = out(reg) result2
    );

    println!("Multi-CSR test completed!");
}

