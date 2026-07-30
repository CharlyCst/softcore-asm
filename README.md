# Softcore-asm

Softcore-asm is an experiment Rust macro that accept standard inline Rust assembly and translate it into the corresponding sequence of instructions against a [softcore-rs](https://github.com/CharlyCst/softcore-rs) CPU model.

> **Warning:** This project is highly experimental: there is no backward compatibility nor correctness guarantees.

## Example

First, initialize a thread-local software core:

```rs
softcore_asm_rv64::softcore_init!(softcore_rv64::config::U74);
```

Then, the following macro:

```rs
softcore_asm_rv64::asm!(
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
    // Path to the module where `softcore_init!` is used.
    // `self` when within the same module.
    softcore(self) 
);
```

Emits the following Rust code:

```rs
{
    unsafe {
        let mut core = self::_get_softcore_ptr();
        if let Trap::Some(_) = (*core).execute(ast::CSRReg((bv(832u64), reg::X5, reg::X0, csrop::CSRRW))) {
            panic!(...);
        }
        if let Trap::Some(_) = (*core).execute(ast::CSRReg((bv(833u64), reg::X0, reg::X5, csrop::CSRRS))) {
            panic!(...);
        }
        if let Trap::Some(_) = (*core).execute(ast::ITYPE((bv(4u64), reg::X5, reg::X5, iop::ADDI))) {
            panic!(...);
        }
        if let Trap::Some(_) = (*core).execute(ast::CSRReg((bv(833u64), reg::X5, reg::X0, csrop::CSRRW))) {
            panic!(...);
        }
        if let Trap::Some(_) = (*core).execute(ast::ITYPE((bv(1u64), reg::X0, reg::X5, iop::ADDI))) {
            panic!(...);
        }
        if let Trap::Some(_) = (*core).execute(ast::CSRReg((bv(832u64), reg::X5, reg::X5, csrop::CSRRW))) {
            panic!(...);
        }
        if let Trap::Some(_) = (*core).execute(ast::MRET(())) {
            panic!(...);
        }
    }
}
```

For usage examples, see how [softcore-asm is used in Miralis](https://github.com/CharlyCst/miralis/blob/10803bf8671c2759f03d7b2688fec17e8ec3a39e/src/arch/metal.rs).

