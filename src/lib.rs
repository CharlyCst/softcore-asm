//! Softcore Assembly Macro

/// The Softcore Assembly macro
///
/// This macro translates RISC-V inline assembly into pure Rust code, by using the `softcore_rv64`
/// CPU model.
pub use softcore_asm_macro::asm;

/// Softcore RV64
///
/// A Rust model of a RISC-V 64 bits CPU, automatically translated from the official [Sail
/// specification](https://github.com/riscv/sail-riscv).
pub use softcore_rv64;

// —————————————————————————— Register Conversion ——————————————————————————— //

/// A trait for types that can be passed through registers
pub trait FromRegister {
    fn from_register(value: u64) -> Self;
}

impl FromRegister for u64 {
    fn from_register(value: u64) -> Self {
        value
    }
}

impl FromRegister for u32 {
    fn from_register(value: u64) -> Self {
        value as u32
    }
}

impl FromRegister for usize {
    fn from_register(value: u64) -> Self {
        value as usize
    }
}

impl<A> FromRegister for *const A {
    fn from_register(value: u64) -> Self {
        value as usize as *const _
    }
}

impl<A> FromRegister for *mut A {
    fn from_register(value: u64) -> Self {
        value as usize as *mut _
    }
}

// —————————————————————————————— Trap Handler —————————————————————————————— //

pub fn handle_trap(addr: u64, trap_handlers: &[extern "C" fn()]) {
    for handler in trap_handlers {
        if *handler as *const () as u64 == addr {
            handler();
            return;
        }
    }

    panic!("Trapped with no valid trap handler registered");
}

// ————————————————————————————— Softcore Macro ————————————————————————————— //

/// Initialize the core with the provided configuration as a threat-local variable.
///
/// It is require to initialize the core in order to use the `soft_asm!` macro, which needs to
/// access the core in order to emulate assembly instructions.
///
/// Usage:
///
/// ```
/// use softcore_asm_rv64::softcore_init;
/// use softcore_rv64::{Core, new_core};
///
/// softcore_init!(softcore_rv64::config::U74);
/// ```
#[macro_export]
macro_rules! softcore_init {
    ($config:path) => {
        // Each thread gets its own copy of the core, this prevent tests using different threads inside a
        // same process to share the same core.
        std::thread_local! {
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
            pub static SOFT_CORE: core::cell::RefCell<softcore_rv64::Core> = {
                let mut core = new_core($config);
                core.reset();
                core::cell::RefCell::new(core)
            };
        }

        /// Returns a raw pointer to the thread local core.
        ///
        /// # Safety:
        ///
        /// The pointer is obtained through `thread_local!`'s `with_borrow_mut` methods, and
        /// therefore should never escape the current thread, nor be derefferenced after another
        /// call to `with_borrow_mut`.
        #[doc(hidden)]
        pub fn _get_softcore_ptr() -> *mut softcore_rv64::Core {
            fn extract_ptr(threat_local_core: &mut Core) -> *mut softcore_rv64::Core {
                threat_local_core as *mut softcore_rv64::Core
            }
            SOFT_CORE.with_borrow_mut(extract_ptr)
        }
    };
}
