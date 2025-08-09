use rasm::rasm;
use softcore_rv64::registers as reg;
use softcore_rv64::{Core, config, new_core};
use core::cell::RefCell;
use std::thread_local;

thread_local! {
    pub static SOFT_CORE: RefCell<Core> = {
        let mut core = new_core(config::U74);
        core.reset();
        RefCell::new(core)
    };
}

fn main() {
    let v: u64 = 0x12345678;
    let value = &v as *const u64 as u64;
    let mut final_value: u64 = 0;

    rasm!(
        "lw {final_val}, {x}",
        x = in(reg) value,
        final_val = out(reg) final_value,
        options(nomem)
    );

    assert_eq!(final_value, v);
    println!("final_value: {:x}", final_value);
}
