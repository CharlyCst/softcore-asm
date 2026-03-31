//! Symbolic execution tests
//!
//! For now we run the tests using Soteria, using the comamnd:
//!
//! ```sh
//! cargo soteria --kani --test soteria
//! ```
//!
//! On Apple silicon macs `cargo soteria` can be installed with:
//!
//! ```sh
//! cargo install soteria --git https://github.com/soteria-tools/cargo-soteria.git
//! ```
//!
//! On other platforms Soteria needs to be installed from source, see instruction [on
//! github](https://github.com/soteria-tools/soteria).

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

/// Generates an arbitrary value.
///
/// A type can be provided as argument, otherwise it will be inferred if possible.
/// A default value can be provided in addition to the type, it will be used during concrete
/// execution.
///
/// This macro either generate a value of a type, or an arbitrary Kani value during model checking.
/// We use this macro to make our Kani proofs runnable as simple tests, which ensures that we don't
/// break the Kani verification harnesses.
macro_rules! any {
    () => {{
        #[cfg(kani)]
        {
            kani::any()
        }
        #[cfg(not(kani))]
        {
            Default::default()
        }
    }};
    ($t:ty) => {{
        #[cfg(kani)]
        {
            kani::any::<$t>()
        }
        #[cfg(not(kani))]
        {
            <$t>::default()
        }
    }};
    ($t:ty, $value:tt) => {{
        #[cfg(kani)]
        {
            kani::any::<$t>()
        }
        #[cfg(not(kani))]
        {
            let val: $t = $value;
            val
        }
    }};
}

/// A macro that wraps the softcore asm macro to add the softcore parameter automatically.
macro_rules! rasm {
    ($($asm:tt)*) => {
        softcore_asm_rv64::asm!(
            $($asm)*,
            softcore(SOFT_CORE.with_borrow_mut)
        )
    };
}

/// An assembly implementation of a branchless 
fn branchless_i64_abs(x: i64) -> i64 {
    let mut result: u64 = 0;
    let mut _sign: u64 = 0;
    rasm!(
        "srai {sign}, {x}, 63",
        "xor {result}, {x}, {sign}",
        "sub {result}, {result}, {sign}",
        x =      in(reg) x as u64,
        sign =   inout(reg) _sign,
        result = inout(reg) result,
    );
    result as i64
}

#[cfg_attr(kani, kani::proof)]
#[cfg_attr(test, test)]
fn test_branchless_abs() {
    let x = any!(i64);
    let x_abs = branchless_i64_abs(x);
    if x == i64::MIN {
        // TODO: decide what we want in that case
    } else if x < 0 {
        assert_eq!(x_abs, -x);
    } else {
        assert_eq!(x_abs, x);
    }
}
