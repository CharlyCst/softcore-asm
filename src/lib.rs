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
