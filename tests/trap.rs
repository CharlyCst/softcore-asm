use softcore_asm_rv64::softcore_init;
use softcore_rv64::{Core, new_core};

softcore_init!(softcore_rv64::config::U74);

/// A macro that wraps the softcore asm macro to add the softcore parameter automatically.
macro_rules! rasm {
    ($($asm:tt)*) => {
        softcore_asm_rv64::asm!(
            $($asm)*,
            softcore(self),
            softcore_trap_handlers(_tracing_trap_handler),
        )
    };
}

/// A macro that wraps the softcore asm macro to emulate naked functions.
macro_rules! naked_rasm {
    ($name:ident, $($asm:tt)*) => {
        extern "C" fn $name() {
            softcore_asm_rv64::asm!(
                $($asm)*,
                softcore(self)
            );
        }
    };
}

#[test]
fn trapping_csr() {
    let mscratch: u64;
    rasm!(
        // Set the trap handler
        "la {val}, {trap_handler}",
        "csrw mtvec, {val}",

        // Initialiaze mscratch to 0, trap, and check the newt mscratch value.
        // See `_tracing_trap_handler`, which sets mscratch to 1.
        "csrw mscratch, x0",    // Initialize mscratch to 0
        "csrw invalid_csr, x1", // Attempt to write to an invalid CSR
        "csrr {val}, mscratch", // After the trap, mscratch should be 1 (see _tracing_trap_handler)
        val = out(reg) mscratch,
        trap_handler = sym _tracing_trap_handler,
    );
    assert_eq!(mscratch, 1);
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
