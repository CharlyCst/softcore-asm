//! Softcore Assembly Macro

mod callable;

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

pub use callable::AsmCallable;
