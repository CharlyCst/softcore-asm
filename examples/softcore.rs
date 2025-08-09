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
    // Your softcore test code here
    let value: u64 = 0xdeadbeef;
    let mut prev_value: u64 = 0;
    let mut final_value: u64 = 0;

    {
    #[cfg(target_arch = "riscv64")]
    unsafe {
        core::arch::asm!("csrrw {prev}, mscratch, {x}
        csrrw {final_val}, mscratch, x0",x = in(reg)value,prev = out(reg)prev_value,final_val = out(reg)final_value,options(nomem))
    }#[cfg(feature = "softcore")]
    {
        SOFT_CORE.with_borrow_mut(|core|{
            core.set(reg::X1,value);
            core.csrrw(reg::X2,csr_name_map_backwards("mscratch").bits(),reg::X1).unwrap();
            core.csrrw(reg::X3,csr_name_map_backwards("mscratch").bits(),reg::X0).unwrap();
            prev_value = core.get(reg::X2);
            final_value = core.get(reg::X3);
        })
    }
};

    assert_eq!(final_value, value);

    let mscratch_val = 0x1234;
    rasm!("csrw mscratch, {cfg}", cfg = in(reg) mscratch_val, options(nomem));
}
