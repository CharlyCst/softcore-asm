# Softcore-asm

Softcore-asm is an experiment Rust macro that accept standard inline Rust assembly and translate it into the corresponding sequence of instructions against a [softcore-rs](github.com/CharlyCst/softcore-rs) CPU model.

> **Warning:** This project is highly experimental: there is no backward compatibility nor correctness guarantees.

## Example

The following macro:

```rs
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
```

Emits the following Rust code:

```rs
SOFT_CORE.with_borrow_mut(|core| {
    core.csrrw(reg::X0, csr_name_map_backwards("mscratch").bits(), reg::X5)
        .unwrap();
    core.csrrs(reg::X5, csr_name_map_backwards("mepc").bits(), reg::X0)
        .unwrap();
    core.execute(ast::ITYPE((bv(4u64), reg::X5, reg::X5, iop::ADDI)));
    core.csrrw(reg::X0, csr_name_map_backwards("mepc").bits(), reg::X5)
        .unwrap();
    core.execute(ast::ITYPE((bv(1u64), reg::X0, reg::X5, iop::ADDI)));
    core.csrrw(reg::X5, csr_name_map_backwards("mscratch").bits(), reg::X5)
        .unwrap();
})
```
