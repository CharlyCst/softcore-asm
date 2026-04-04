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

use softcore_rv64::{Core, new_core};
use softcore_asm_rv64::softcore_init;

softcore_init!(softcore_rv64::config::U74);

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
            softcore(self)
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
