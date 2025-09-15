use core::cell::RefCell;
use softcore_asm::rasm;
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

/// This holds all of the state that the kernel must keep for the process when
/// the process is not executing.
#[derive(Default)]
#[repr(C)]
pub struct Riscv64iStoredState {
    /// Store all of the app registers.
    regs: [u64; 31],

    /// This holds the PC value of the app when the exception/syscall/interrupt
    /// occurred. We also use this to set the PC that the app should start
    /// executing at when it is resumed/started.
    pc: u64,

    /// We need to store the mcause CSR between when the trap occurs and after
    /// we exit the trap handler and resume the context switching code.
    mcause: u64,

    /// We need to store the mtval CSR for the process in case the mcause
    /// indicates a fault. In that case, the mtval contains useful debugging
    /// information.
    mtval: u64,
}

unsafe fn switch_to_process(state: &mut Riscv64iStoredState) {
    // We need to ensure that the compiler does not reorder
    // kernel memory writes to after the userspace context switch
    // to ensure we provide a consistent memory view of
    // application-accessible buffers.
    //
    // The compiler will not be able to reorder memory accesses
    // beyond this point, as the "nomem" option on the asm!-block
    // is not set, hence the compiler has to assume the assembly
    // will issue arbitrary memory accesses (acting as a compiler
    // fence).
    rasm!("
          // Before switching to the app we need to save some kernel registers
          // to the kernel stack, specifically ones which we can't mark as
          // clobbered in the asm!() block. We then save the stack pointer in
          // the mscratch CSR so we can retrieve it after returning to the
          // kernel from the app.
          //
          // A few values get saved to the kernel stack, including an app
          // register temporarily after entering the trap handler. Here is a
          // memory map to make it easier to keep track:
          //
          // ```
          //  8*4(sp):          <- original stack pointer
          //  7*4(sp):
          //  6*4(sp): x9  / s1
          //  5*4(sp): x8  / s0 / fp
          //  4*4(sp): x4  / tp
          //  3*4(sp): x3  / gp
          //  2*4(sp): x10 / a0 (*state, Per-process StoredState struct)
          //  1*4(sp): custom trap handler address
          //  0*4(sp): scratch space, having s1 written to by the trap handler
          //                    <- new stack pointer
          // ```

          addi sp, sp, -8*4  // Move the stack pointer down to make room.

          // Save all registers on the kernel stack which cannot be clobbered
          // by an asm!() block. These are mostly registers which have a
          // designated purpose (e.g. stack pointer) or are used internally
          // by LLVM.
          sd   x9,  6*8(sp)   // s1 (used internally by LLVM)
          sd   x8,  5*8(sp)   // fp (can't be clobbered / used as an operand)
          sd   x4,  4*8(sp)   // tp (can't be clobbered / used as an operand)
          sd   x3,  3*8(sp)   // gp (can't be clobbered / used as an operand)

          sd   x10, 2*8(sp)   // Store process state pointer on stack as well.
                              // We need to have this available for after the
                              // app returns to the kernel so we can store its
                              // registers.

          // Load the address of `_start_app_trap` into `1*4(sp)`. We swap our
          // stack pointer into the mscratch CSR and the trap handler will load
          // and jump to the address at this offset.
          // TODO!!! la    t0, 100f      // t0 = _start_app_trap
          sd    t0, 1*8(sp)   // 1*4(sp) = t0

          // sd x0, 0*8(sp)   // Reserved as scratch space for the trap handler

          // -----> All required registers saved to the stack.
          //        sp holds the updated stack pointer, a0 the per-process state

          // From here on we can't allow the CPU to take interrupts anymore, as
          // we re-route traps to `_start_app_trap` below (by writing our stack
          // pointer into the mscratch CSR), and we rely on certain CSRs to not
          // be modified or used in their intermediate states (e.g., mepc).
          //
          // We atomically switch to user-mode and re-enable interrupts using
          // the `mret` instruction below.
          //
          // If interrupts are disabled _after_ setting mscratch, this result in
          // the race condition of [PR 2308](https://github.com/tock/tock/pull/2308)

          // Therefore, clear the following bits in mstatus first:
          //   0x00000008 -> bit 3 -> MIE (disabling interrupts here)
          // + 0x00001800 -> bits 11,12 -> MPP (switch to usermode on mret)
          li    t0, 0x00001808
          csrc  mstatus, t0         // clear bits in mstatus

          // Afterwards, set the following bits in mstatus:
          //   0x00000080 -> bit 7 -> MPIE (enable interrupts on mret)
          li    t0, 0x00000080
          csrs  mstatus, t0         // set bits in mstatus

          // Execute `_start_app_trap` on a trap by setting the mscratch trap
          // handler address to our current stack pointer. This stack pointer,
          // at `1*4(sp)`, holds the address of `_start_app_trap`.
          //
          // Upon a trap, the global trap handler (_start_trap) will swap `s0`
          // with the `mscratch` CSR and, if it contains a non-zero address,
          // jump to the address that is now at `1*4(s0)`. This allows us to
          // hook a custom trap handler that saves all userspace state:
          //
          csrw  mscratch, sp        // Store `sp` in mscratch CSR. Discard the
                                    // prior value, must have been set to zero.

          // We have to set the mepc CSR with the PC we want the app to start
          // executing at. This has been saved in Riscv32iStoredState for us
          // (either when the app returned back to the kernel or in the
          // `set_process_function()` function).
          ld    t0, 31*8(a0)        // Retrieve the PC from Riscv32iStoredState
          csrw  mepc, t0            // Set mepc CSR to the app's PC.

          // Restore all of the app registers from what we saved. If this is the
          // first time running the app then most of these values are
          // irrelevant, However we do need to set the four arguments to the
          // `_start_ function in the app. If the app has been executing then
          // this allows the app to correctly resume.

          // We do a little switcheroo here, and place the per-process stored
          // state pointer into the `sp` register instead of `a0`. Doing so
          // allows us to use compressed instructions for all of these loads:
          mv    sp,  a0             // sp <- a0 (per-process stored state)

          ld    x1,  0*8(sp)        // ra
          // ------------------------> sp, do last since we overwrite our pointer
          ld    x3,  2*8(sp)        // gp
          ld    x4,  3*8(sp)        // tp
          ld    x5,  4*8(sp)        // t0
          ld    x6,  5*8(sp)        // t1
          ld    x7,  6*8(sp)        // t2
          ld    x8,  7*8(sp)        // s0,fp
          ld    x9,  8*8(sp)        // s1
          ld   x10,  9*8(sp)        // a0
          ld   x11, 10*8(sp)        // a1
          ld   x12, 11*8(sp)        // a2
          ld   x13, 12*8(sp)        // a3
          ld   x14, 13*8(sp)        // a4
          ld   x15, 14*8(sp)        // a5
          ld   x16, 15*8(sp)        // a6
          ld   x17, 16*8(sp)        // a7
          ld   x18, 17*8(sp)        // s2
          ld   x19, 18*8(sp)        // s3
          ld   x20, 19*8(sp)        // s4
          ld   x21, 20*8(sp)        // s5
          ld   x22, 21*8(sp)        // s6
          ld   x23, 22*8(sp)        // s7
          ld   x24, 23*8(sp)        // s8
          ld   x25, 24*8(sp)        // s9
          ld   x26, 25*8(sp)        // s10
          ld   x27, 26*8(sp)        // s11
          ld   x28, 27*8(sp)        // t3
          ld   x29, 28*8(sp)        // t4
          ld   x30, 29*8(sp)        // t5
          ld   x31, 30*8(sp)        // t6
          ld    x2,  1*8(sp)        // sp, overwriting our pointer

          // Call mret to jump to where mepc points, switch to user mode, and
          // start running the app.
          mret
        ",

        // We pass the per-process state struct in a register we are allowed
        // to clobber (not s0 or s1), but still fits into 3-bit register
        // arguments of compressed load- & store-instructions.
        in("x10") core::ptr::from_mut::<Riscv64iStoredState>(state),

        // Clobber all registers which can be marked as clobbered, except
        // for `a0` / `x10`. By making it retain the value of `&mut state`,
        // which we need to stack manually anyway, we can avoid Rust/LLVM
        // stacking it redundantly for us.
        // out("x1") _, out("x5") _, out("x6") _, out("x7") _, out("x11") _,
        // out("x12") _, out("x13") _, out("x14") _, out("x15") _, out("x16") _,
        // out("x17") _, out("x18") _, out("x19") _, out("x20") _, out("x21") _,
        // out("x22") _, out("x23") _, out("x24") _, out("x25") _, out("x26") _,
        // out("x27") _, out("x28") _, out("x29") _, out("x30") _, out("x31") _,
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use softcore_rv64::registers::*;

    #[test]
    fn tock_switch() {
        const STACK_SIZE: usize = 10;
        let mut state = Riscv64iStoredState::default();
        let mut stack = [0_u64; STACK_SIZE];
        let stack_addr = stack
            .as_mut_ptr()
            .expose_provenance()
            .wrapping_add((STACK_SIZE - 3) * size_of::<u64>()) as u64;

        SOFT_CORE.with_borrow_mut(|core| {
            // Set the stack pointer before the call
            core.set(SP, stack_addr);
        });
        for i in 0..31 {
            state.regs[i] = 17 * i as u64;
        }

        unsafe {
            switch_to_process(&mut state);
        }

        SOFT_CORE.with_borrow_mut(|core| {
            use softcore_rv64::*;
            assert_eq!(core.mode(), Privilege::User);
            for i in 0..31 {
                assert_eq!(
                    core.get(registers::GeneralRegister::new(i + 1)),
                    17 * i as u64
                )
            }
        });
    }
}
