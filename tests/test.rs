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

#[test]
fn csr() {
    let value: u64 = 0xdeadbeef;
    let mut prev_value: u64 = 0;
    let mut final_value: u64 = 0;

    rasm!(
        "csrrw {prev}, mscratch, {x}
        csrrw {final_val}, mscratch, x0",
        x = in(reg) value,
        prev = out(reg) prev_value,
        final_val = out(reg) final_value,
        options(nomem)
    );

    assert_eq!(final_value, value);

    let mscratch_val = 0x1234;
    rasm!("csrw mscratch, {cfg}", cfg = in(reg) mscratch_val, options(nomem));
    SOFT_CORE.with_borrow_mut(|core| {
        assert_eq!(
            core.mscratch.bits(),
            mscratch_val,
            "Failed to write mscratch"
        );
    })
}

// #[test]
// fn load() {
//     let v: u64 = 0x12345678;
//     let value = &v as *const u64 as u64;
//     let mut final_value: u64 = 0;

//     rasm!(
//         "ld {final_val}, 0({x})",
//         x = in(reg) value,
//         final_val = out(reg) final_value
//     );

//     assert_eq!(final_value, v);
//     println!("final_value: {:x}", final_value);
// }

#[test]
fn store() {
    let mut val: u64 = 0;
    let new_val: u64 = 0xbeef00beef;

    unsafe {
        rasm!(
            "sd {x}, 0({addr})",
            x = in(reg) new_val,
            addr = in(reg) (&mut val) as *mut u64 as u64
        );
    }
    assert_eq!(val, new_val, "'sd' did not update memory location");

    // let mut v: u64 = 0;
    // let value: u64 = 0x87654321;
    // let addr = &mut v as *mut u64 as u64;

    // println!("v before: {:x}", v);
    // rasm!(
    //     "sd {x}, 0({addr})",
    //     x = in(reg) value,
    //     addr = in(reg) addr
    // );
    // println!("v after: {:x}", v);

    // assert_eq!(v, value);
    // println!("v: {:x}", v);
}

// /// Testing mixed named and positional operand syntax.
// #[test]
// fn mixed_operands() {
//     let input_val = 42;
//     let mut output_val = 0;
//     let temp = 100;

//     // Test 1: Mixed named and positional operands
//     rasm!("add {result}, {}, {temp}",
//           in(reg) input_val,          // Positional operand
//           result = out(reg) output_val,  // Named operand
//           temp = in(reg) temp); // Named operand

//     // Test 2: Named operands with options
//     rasm!("csrrw {old}, mstatus, {new}",
//           old = out(reg) output_val,
//           new = in(reg) input_val,
//           options(nomem, nostack));

//     // Test 3: All positional
//     rasm!("addi {}, {}, 10",
//           out(reg) output_val,
//           in(reg) input_val);
// }

///// Raw instructions with no interactions witht he Rust code.
/////
///// In practice, those would be undefined behavior if executed on real hardware.
//#[test]
//fn raw_instructions() {
//    // Test 1: Simple RISC-V instruction
//    rasm!("addi x1, x2, 42");

//    // Test 2: Multiple instructions
//    rasm!("li x1, 100");

//    // Test 3: Load/store operations
//    rasm!("lw x1, 0(x2)");

//    // Test 4: Branch instruction
//    rasm!("beq x1, x2, label");

//    // Test 5: Instruction with simple operand
//    let x = 5;
//    rasm!("addi x1, x2, {}", x);

//    println!("All tests completed!");
//}

#[test]
fn load_immediate() {
    rasm!("li x1, 100");
    SOFT_CORE.with_borrow_mut(|core| assert_eq!(core.get(reg::X1), 100));
    rasm!("li x1, 0xbeef");
    SOFT_CORE.with_borrow_mut(|core| assert_eq!(core.get(reg::X1), 0xbeef));

    rasm!("li x1, -100");
    SOFT_CORE.with_borrow_mut(|core| assert_eq!(core.get(reg::X1), (-100i64 as u64)));
    // rasm!("li x1, -0xbeef");
    // SOFT_CORE.with_borrow_mut(|core| assert_eq!(core.get(reg::X1), (-0xbeefi64 as u64)));
}
