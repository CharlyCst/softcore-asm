//! The [AsmCallable] trait defines objects that can be called from assembly.

/// A trait to implement on Rust objects that can be called from assembly.
pub trait AsmCallable<C> {
    fn call_from_assembly(self, core: &mut C);
}

/// A trait for types that can be passed through registers
pub trait FromRegister {
    fn from_register(value: u64) -> Self;
}

impl FromRegister for u64 {
    fn from_register(value: u64) -> Self {
        value
    }
}

impl FromRegister for usize {
    fn from_register(value: u64) -> Self {
        value as usize
    }
}

// ————————————————————————————————— RISC-V ————————————————————————————————— //

use softcore_rv64::Core as Rv64Core;
use softcore_rv64::registers::*;

impl AsmCallable<Rv64Core> for extern "C" fn() {
    fn call_from_assembly(self, _core: &mut Rv64Core) {
        self();
    }
}

impl<T> AsmCallable<Rv64Core> for extern "C" fn(T)
where
    T: FromRegister,
{
    fn call_from_assembly(self, core: &mut Rv64Core) {
        let arg1 = T::from_register(core.get(A0));
        self(arg1);
    }
}

impl<T1, T2> AsmCallable<Rv64Core> for extern "C" fn(T1, T2)
where
    T1: FromRegister,
    T2: FromRegister,
{
    fn call_from_assembly(self, core: &mut Rv64Core) {
        let arg1 = T1::from_register(core.get(A0));
        let arg2 = T2::from_register(core.get(A1));
        self(arg1, arg2);
    }
}
