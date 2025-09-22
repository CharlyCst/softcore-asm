use core::cell::RefCell;
use softcore_asm::rasm;
use std::thread_local;

use softcore_rv64::prelude::bv;
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

#[test]
fn load() {
    unsafe {
        // Double words
        let mut vals: [u64; 3] = [0xbeef00beef, 0x0badbed00badbed0, 0x0123456789abcdef];
        let vals_addr = vals.as_mut_ptr().offset(1) as usize;
        let mut val0: u64 = 0;
        let mut val1: u64 = 0;
        let mut val2: u64 = 0;

        rasm!(
            "ld {val0}, -8({addr})
             ld {val1}, 0({addr})
             ld {val2},  8({addr})",
            val0 = out(reg) val0,
            val1 = out(reg) val1,
            val2 = out(reg) val2,
            addr = in(reg) vals_addr
        );

        assert_eq!(vals[0], val0);
        assert_eq!(vals[1], val1);
        assert_eq!(vals[2], val2);

        // Words
        let mut vals: [u32; 3] = [0xbeef0000, 0x0badbed0, 0x01234567];
        let vals_addr = vals.as_mut_ptr().offset(1) as usize;
        let mut val0: u64 = 0;
        let mut val1: u64 = 0;
        let mut val2: u64 = 0;

        rasm!(
            "lwu {val0}, -4({addr})
             lwu {val1}, 0({addr})
             lwu {val2},  4({addr})",
            val0 = out(reg) val0,
            val1 = out(reg) val1,
            val2 = out(reg) val2,
            addr = in(reg) vals_addr
        );

        assert_eq!(vals[0], val0 as u32);
        assert_eq!(vals[1], val1 as u32);
        assert_eq!(vals[2], val2 as u32);

        // Half words
        let mut vals: [u16; 3] = [0xbeef, 0x0bad, 0x0123];
        let vals_addr = vals.as_mut_ptr().offset(1) as usize;
        let mut val0: u64 = 0;
        let mut val1: u64 = 0;
        let mut val2: u64 = 0;

        rasm!(
            "lhu {val0}, -2({addr})
             lhu {val1}, 0({addr})
             lhu {val2},  2({addr})",
            val0 = out(reg) val0,
            val1 = out(reg) val1,
            val2 = out(reg) val2,
            addr = in(reg) vals_addr
        );

        assert_eq!(vals[0], val0 as u16);
        assert_eq!(vals[1], val1 as u16);
        assert_eq!(vals[2], val2 as u16);

        // Bytes
        let mut vals: [u8; 3] = [0xbe, 0x0b, 0x01];
        let vals_addr = vals.as_mut_ptr().offset(1) as usize;
        let mut val0: u64 = 0;
        let mut val1: u64 = 0;
        let mut val2: u64 = 0;

        rasm!(
            "lbu {val0}, -1({addr})
             lbu {val1}, 0({addr})
             lbu {val2},  1({addr})",
            val0 = out(reg) val0,
            val1 = out(reg) val1,
            val2 = out(reg) val2,
            addr = in(reg) vals_addr
        );

        assert_eq!(vals[0], val0 as u8);
        assert_eq!(vals[1], val1 as u8);
        assert_eq!(vals[2], val2 as u8);
    }
}

/// Tests the store instructions.
///
/// In those tests we define an array of three elements on the stack, take a pointer to the middle
/// element, and try to write all three of them.
#[test]
fn store() {
    unsafe {
        // Double words
        let mut vals = [0u64; 3];
        let vals_addr = vals.as_mut_ptr().offset(1) as u64;
        let val0: u64 = 0xbeef00beef;
        let val1: u64 = 0x0badbed00badbed0;
        let val2: u64 = 0x0123456789abcdef;

        rasm!(
            "sd {val0}, -8({addr})
             sd {val1}, 0({addr})
             sd {val2},  8({addr})",
            val0 = in(reg) val0,
            val1 = in(reg) val1,
            val2 = in(reg) val2,
            addr = in(reg) vals_addr
        );

        assert_eq!(vals[0], val0);
        assert_eq!(vals[1], val1);
        assert_eq!(vals[2], val2);

        // Words
        let mut vals = [0u32; 3];
        let vals_addr = vals.as_mut_ptr().offset(1) as u64;
        let val0: u32 = 0xbeef0000;
        let val1: u32 = 0x0badbed0;
        let val2: u32 = 0x01234567;

        rasm!(
            "sw {val0}, -4({addr})
             sw {val1}, 0({addr})
             sw {val2},  4({addr})",
            val0 = in(reg) val0 as u64,
            val1 = in(reg) val1 as u64,
            val2 = in(reg) val2 as u64,
            addr = in(reg) vals_addr
        );

        assert_eq!(vals[0], val0);
        assert_eq!(vals[1], val1);
        assert_eq!(vals[2], val2);

        // Half words
        let mut vals = [0u16; 3];
        let vals_addr = vals.as_mut_ptr().offset(1) as u64;
        let val0: u16 = 0xbeef;
        let val1: u16 = 0x0bad;
        let val2: u16 = 0x0123;

        rasm!(
            "sh {val0}, -2({addr})
             sh {val1}, 0({addr})
             sh {val2},  2({addr})",
            val0 = in(reg) val0 as u64,
            val1 = in(reg) val1 as u64,
            val2 = in(reg) val2 as u64,
            addr = in(reg) vals_addr
        );

        assert_eq!(vals[0], val0);
        assert_eq!(vals[1], val1);
        assert_eq!(vals[2], val2);

        // Bytes
        let mut vals = [0u8; 3];
        let vals_addr = vals.as_mut_ptr().offset(1) as u64;
        let val0: u8 = 0xbe;
        let val1: u8 = 0x0b;
        let val2: u8 = 0x01;

        rasm!(
            "sb {val0}, -1({addr})
             sb {val1}, 0({addr})
             sb {val2},  1({addr})",
            val0 = in(reg) val0 as u64,
            val1 = in(reg) val1 as u64,
            val2 = in(reg) val2 as u64,
            addr = in(reg) vals_addr
        );

        assert_eq!(vals[0], val0);
        assert_eq!(vals[1], val1);
        assert_eq!(vals[2], val2);
    }
}

#[test]
fn rtype() {
    let x = 42;
    let y = 20;
    let mut sum = 0;
    rasm!(
        "add {sum}, {x}, {y}",
        x = in(reg) x,
        y = in(reg) y,
        sum = out(reg) sum
    );
    assert_eq!(sum, x + y);

    let mut diff = 0;
    rasm!(
        "sub {diff}, {x}, {y}",
        x = in(reg) x,
        y = in(reg) y,
        diff = out(reg) diff
    );
    assert_eq!(diff, x - y);

    let mut and = 0;
    rasm!(
        "and {and}, {x}, {y}",
        x = in(reg) x,
        y = in(reg) y,
        and = out(reg) and
    );
    assert_eq!(and, x & y);

    let mut or = 0;
    rasm!(
        "or {or}, {x}, {y}",
        x = in(reg) x,
        y = in(reg) y,
        or = out(reg) or
    );
    assert_eq!(or, x | y);

    let mut xor = 0;
    rasm!(
        "xor {xor}, {x}, {y}",
        x = in(reg) x,
        y = in(reg) y,
        xor = out(reg) xor
    );
    assert_eq!(xor, x ^ y);
}

#[test]
fn itype() {
    let x = 42;
    let mut sum1 = 0;
    let mut sum2 = 0;
    rasm!(
        "addi {sum1}, {x}, 20",
        "addi {sum2}, {x}, -20",
        x = in(reg) x,
        sum1 = out(reg) sum1,
        sum2 = out(reg) sum2,
    );
    assert_eq!(sum1, x + 20);
    assert_eq!(sum2, x - 20);

    let mut and_result = 0;
    let mut or_result = 0;
    let mut xor_result = 0;
    rasm!(
        "andi {and_result}, {x}, 0x0f",
        "ori {or_result}, {x}, 0x80",
        "xori {xor_result}, {x}, 0xff",
        x = in(reg) x,
        and_result = out(reg) and_result,
        or_result = out(reg) or_result,
        xor_result = out(reg) xor_result,
    );
    assert_eq!(and_result, x & 0x0f);
    assert_eq!(or_result, x | 0x80);
    assert_eq!(xor_result, x ^ 0xff);
}

#[test]
fn mul() {
    // Test basic multiplication
    let x = 6u64;
    let y = 7u64;
    let mut result = 0u64;

    rasm!(
        "mul {result}, {x}, {y}",
        x = in(reg) x,
        y = in(reg) y,
        result = out(reg) result
    );
    assert_eq!(result, x * y);

    // Test multiplication with larger numbers
    let x = 0x123456789abcdef0u64;
    let y = 0x2u64;
    let mut result = 0u64;

    rasm!(
        "mul {result}, {x}, {y}",
        x = in(reg) x,
        y = in(reg) y,
        result = out(reg) result
    );
    assert_eq!(result, x.wrapping_mul(y));

    // NOTE: the following tests are not yet supported, pending support for 128 bits bitvectors in
    // softcore-rs

    // // Test mulh (signed high multiplication)
    // let x = -1i64 as u64;
    // let y = -1i64 as u64;
    // let mut result = 0u64;

    // rasm!(
    //     "mulh {result}, {x}, {y}",
    //     x = in(reg) x,
    //     y = in(reg) y,
    //     result = out(reg) result
    // );
    // // (-1) * (-1) = 1, high part should be 0
    // assert_eq!(result, 0);

    // // Test mulh with large signed numbers
    // let x = 0x7fffffffffffffffu64; // Large positive
    // let y = 2u64;
    // let mut result = 0u64;

    // rasm!(
    //     "mulh {result}, {x}, {y}",
    //     x = in(reg) x,
    //     y = in(reg) y,
    //     result = out(reg) result
    // );
    // // Should get high 64 bits of the 128-bit result
    // assert_eq!(result, 0);

    // // Test mulhsu (signed * unsigned high multiplication)
    // let x = -1i64 as u64; // All 1's as signed
    // let y = 2u64; // Unsigned 2
    // let mut result = 0u64;

    // rasm!(
    //     "mulhsu {result}, {x}, {y}",
    //     x = in(reg) x,
    //     y = in(reg) y,
    //     result = out(reg) result
    // );
    // // -1 * 2 = -2, high part should be all 1's
    // assert_eq!(result, 0xffffffffffffffffu64);

    // // Test mulhu (unsigned high multiplication)
    // let x = 0xffffffffffffffffu64;
    // let y = 0xffffffffffffffffu64;
    // let mut result = 0u64;

    // rasm!(
    //     "mulhu {result}, {x}, {y}",
    //     x = in(reg) x,
    //     y = in(reg) y,
    //     result = out(reg) result
    // );
    // // Max unsigned * max unsigned, high part should be 0xfffffffffffffffe
    // assert_eq!(result, 0xfffffffffffffffeu64);

    // // Test edge case: multiplication by zero
    // let x = 0x123456789abcdef0u64;
    // let y = 0u64;
    // let mut mul_result = 0u64;
    // let mut mulh_result = 0u64;
    // let mut mulhsu_result = 0u64;
    // let mut mulhu_result = 0u64;

    // rasm!(
    //     "mul {mul_result}, {x}, {y}
    //      mulh {mulh_result}, {x}, {y}
    //      mulhsu {mulhsu_result}, {x}, {y}
    //      mulhu {mulhu_result}, {x}, {y}",
    //     x = in(reg) x,
    //     y = in(reg) y,
    //     mul_result = out(reg) mul_result,
    //     mulh_result = out(reg) mulh_result,
    //     mulhsu_result = out(reg) mulhsu_result,
    //     mulhu_result = out(reg) mulhu_result
    // );
    // assert_eq!(mul_result, 0);
    // assert_eq!(mulh_result, 0);
    // assert_eq!(mulhsu_result, 0);
    // assert_eq!(mulhu_result, 0);
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

#[test]
fn load_immediate() {
    rasm!("li x1, 100");
    SOFT_CORE.with_borrow_mut(|core| assert_eq!(core.get(reg::X1), 100));
    rasm!("li x1, 0xbeef");
    SOFT_CORE.with_borrow_mut(|core| assert_eq!(core.get(reg::X1), 0xbeef));

    rasm!("li x1, -100");
    SOFT_CORE.with_borrow_mut(|core| assert_eq!(core.get(reg::X1), (-100i64 as u64)));
    rasm!("li x1, -0xbeef");
    SOFT_CORE.with_borrow_mut(|core| assert_eq!(core.get(reg::X1), (-0xbeefi64 as u64)));
}

#[test]
fn symbols() {
    static mut MY_SYMBOL: u64 = 0;

    unsafe {
        let new_val: u64 = 0xcafe0bad0bed0;
        let mut sym_addr = 0;

        rasm!(
            "la {sym_addr}, {my_sym}",
            "sd {new_val}, 0({sym_addr})",
            my_sym = sym MY_SYMBOL,
            sym_addr = out(reg) sym_addr,
            new_val = in(reg) new_val,
        );

        assert_eq!(sym_addr, (&raw mut MY_SYMBOL) as *const _ as u64);
        let sym_val = core::ptr::read((&raw mut MY_SYMBOL) as *const u64);
        assert_eq!(new_val, sym_val);
    }
}

#[test]
fn consts() {
    let value: u64 = 42;
    let mut out: u64 = 0;

    rasm!(
        "li {out}, {value_size}",
        out = out(reg) out,
        value_size = const core::mem::size_of_val(&value),
    );

    assert_eq!(out, core::mem::size_of::<u64>() as u64)
}

#[test]
fn miralis_trap_detector() {
    use softcore_rv64::raw;
    const TRAP_ADDR: u64 = 0xffff00;

    SOFT_CORE.with_borrow_mut(|core| {
        for i in 1..32 {
            core.set(raw::regidx::new(i as u8), 100 + i as u64);
        }
        core.mepc = bv(TRAP_ADDR);
    });

    rasm!(
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

    SOFT_CORE.with_borrow_mut(|core| {
        for i in 1..32 {
            assert_eq!(
                core.get(raw::regidx::new(i as u8)),
                100 + i as u64,
                "Unexpected value in x{i}"
            );
        }
        assert_eq!(core.mepc.bits(), TRAP_ADDR + 4);
        assert_eq!(core.mscratch.bits(), 1);
    });
}
