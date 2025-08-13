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

fn test_load() {
    let v: u64 = 0x12345678;
    let value = &v as *const u64 as u64;
    let mut final_value: u64 = 0;

    rasm!(
        "ld {final_val}, 0({x})",
        x = in(reg) value,
        final_val = out(reg) final_value
    );

    assert_eq!(final_value, v);
    println!("final_value: {:x}", final_value);
}

fn test_store() {
    let mut v: u64 = 0;
    let value: u64 = 0x87654321;
    let addr = &mut v as *mut u64 as u64;

    println!("v before: {:x}", v);
    rasm!(
        "sd {x}, 0({addr})",
        x = in(reg) value,
        addr = in(reg) addr
    );
    println!("v after: {:x}", v);

    assert_eq!(v, value);
    println!("v: {:x}", v);
}

fn main() {
    test_load();
    test_store();
}
