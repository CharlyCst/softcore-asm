use core::cell::RefCell;
use std::thread_local;

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

/// A macro that wraps the softcore asm macro to add the softcore parameter automatically.
macro_rules! rasm {
    ($($asm:tt)*) => {
        softcore_asm_rv64::asm!(
            $($asm)*,
            softcore(SOFT_CORE.with_borrow_mut),
            softcore_trap_handlers(_tracing_trap_handler as usize),
        )
    };
}

/// A macro that wraps the softcore asm macro to emulate naked functions.
macro_rules! naked_rasm {
    ($name:ident, $($asm:tt)*) => {
        extern "C" fn $name() {
            softcore_asm_rv64::asm!(
                $($asm)*,
                softcore(SOFT_CORE.with_borrow_mut)
            );
        }
    };
}

#[test]
fn trapping_csr() {
    // let mscratch: u64;
    // rasm!(
    //     "csrw mscratch, x0",    // Initialize mscratch to 0
    //     "csrw invalid_csr, x1", // Attempt to write to an invalid CSR
    //     "csrr {val}, mscratch", // After the trap, mscratch should be 1 (see _tracing_trap_handler)
    //     val = out(reg) mscratch,
    // );
    // assert_eq!(mscratch, 1);
}


// Trap handler that sets `mscratch` to 1 and skip the trapping instruction.
naked_rasm!(
    _tracing_trap_handler,
    // Save x5
    "csrw mscratch, x5",
    // Skip illegal instruction (pc += 4)
    "csrr x5, mepc",
    "addi x5, x5, 4",
    "csrw mepc, x5",
    // Set mscratch to 1
    "addi x5, x0, 1",
    "csrrw x5, mscratch, x5",
    // Return back to miralis
    "mret",
);
