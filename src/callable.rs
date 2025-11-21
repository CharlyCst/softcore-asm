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

impl<T1, T2, T3> AsmCallable<Rv64Core> for extern "C" fn(T1, T2, T3)
where
    T1: FromRegister,
    T2: FromRegister,
    T3: FromRegister,
{
    fn call_from_assembly(self, core: &mut Rv64Core) {
        let arg1 = T1::from_register(core.get(A0));
        let arg2 = T2::from_register(core.get(A1));
        let arg3 = T3::from_register(core.get(A2));
        self(arg1, arg2, arg3);
    }
}

impl<T1, T2, T3, T4> AsmCallable<Rv64Core> for extern "C" fn(T1, T2, T3, T4)
where
    T1: FromRegister,
    T2: FromRegister,
    T3: FromRegister,
    T4: FromRegister,
{
    fn call_from_assembly(self, core: &mut Rv64Core) {
        let arg1 = T1::from_register(core.get(A0));
        let arg2 = T2::from_register(core.get(A1));
        let arg3 = T3::from_register(core.get(A2));
        let arg4 = T4::from_register(core.get(A3));
        self(arg1, arg2, arg3, arg4);
    }
}

impl<T1, T2, T3, T4, T5> AsmCallable<Rv64Core> for extern "C" fn(T1, T2, T3, T4, T5)
where
    T1: FromRegister,
    T2: FromRegister,
    T3: FromRegister,
    T4: FromRegister,
    T5: FromRegister,
{
    fn call_from_assembly(self, core: &mut Rv64Core) {
        let arg1 = T1::from_register(core.get(A0));
        let arg2 = T2::from_register(core.get(A1));
        let arg3 = T3::from_register(core.get(A2));
        let arg4 = T4::from_register(core.get(A3));
        let arg5 = T5::from_register(core.get(A4));
        self(arg1, arg2, arg3, arg4, arg5);
    }
}

impl<T1, T2, T3, T4, T5, T6> AsmCallable<Rv64Core> for extern "C" fn(T1, T2, T3, T4, T5, T6)
where
    T1: FromRegister,
    T2: FromRegister,
    T3: FromRegister,
    T4: FromRegister,
    T5: FromRegister,
    T6: FromRegister,
{
    fn call_from_assembly(self, core: &mut Rv64Core) {
        let arg1 = T1::from_register(core.get(A0));
        let arg2 = T2::from_register(core.get(A1));
        let arg3 = T3::from_register(core.get(A2));
        let arg4 = T4::from_register(core.get(A3));
        let arg5 = T5::from_register(core.get(A4));
        let arg6 = T6::from_register(core.get(A5));
        self(arg1, arg2, arg3, arg4, arg5, arg6);
    }
}

impl<T1, T2, T3, T4, T5, T6, T7> AsmCallable<Rv64Core> for extern "C" fn(T1, T2, T3, T4, T5, T6, T7)
where
    T1: FromRegister,
    T2: FromRegister,
    T3: FromRegister,
    T4: FromRegister,
    T5: FromRegister,
    T6: FromRegister,
    T7: FromRegister,
{
    fn call_from_assembly(self, core: &mut Rv64Core) {
        let arg1 = T1::from_register(core.get(A0));
        let arg2 = T2::from_register(core.get(A1));
        let arg3 = T3::from_register(core.get(A2));
        let arg4 = T4::from_register(core.get(A3));
        let arg5 = T5::from_register(core.get(A4));
        let arg6 = T6::from_register(core.get(A5));
        let arg7 = T7::from_register(core.get(A6));
        self(arg1, arg2, arg3, arg4, arg5, arg6, arg7);
    }
}

impl<T1, T2, T3, T4, T5, T6, T7, T8> AsmCallable<Rv64Core>
    for extern "C" fn(T1, T2, T3, T4, T5, T6, T7, T8)
where
    T1: FromRegister,
    T2: FromRegister,
    T3: FromRegister,
    T4: FromRegister,
    T5: FromRegister,
    T6: FromRegister,
    T7: FromRegister,
    T8: FromRegister,
{
    fn call_from_assembly(self, core: &mut Rv64Core) {
        let arg1 = T1::from_register(core.get(A0));
        let arg2 = T2::from_register(core.get(A1));
        let arg3 = T3::from_register(core.get(A2));
        let arg4 = T4::from_register(core.get(A3));
        let arg5 = T5::from_register(core.get(A4));
        let arg6 = T6::from_register(core.get(A5));
        let arg7 = T7::from_register(core.get(A6));
        let arg8 = T8::from_register(core.get(A7));
        self(arg1, arg2, arg3, arg4, arg5, arg6, arg7, arg8);
    }
}
