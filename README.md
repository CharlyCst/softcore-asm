# RASM - RISC-V Assembly Macro

A Rust procedural macro that mimics the standard library's `asm!` macro for RISC-V assembly code. Currently focuses on parsing and validating assembly strings and operands.

## Features

- **Assembly String Parsing**: Extracts assembly instruction strings from macro invocations
- **Operand Parsing**: Supports `in(reg)`, `out(reg)`, and `inout(reg)` operand specifications
- **RISC-V Validation**: Validates common RISC-V instructions and register names
- **Debug Output**: Prints parsed assembly strings and operands for debugging

## Usage

### Basic Assembly Instructions

```rust
use rasm::rasm;

rasm!("addi x1, x2, 42");
rasm!("lw t0, 0(sp)");
rasm!("beq a0, a1, label");
```

### Assembly with Operands

```rust
let input_val = 10;
let mut output_val = 0;

rasm!("add {}, {}, {}", 
      in(reg) input_val,
      out(reg) output_val);
```

### Assembly with Raw Expressions

```rust
let value = 42;
rasm!("addi x1, x2, {}", value);
```

## Validation

The macro validates:

- **RISC-V Instructions**: Checks against common RISC-V instruction set
- **Register Names**: Validates both numeric (x0-x31) and mnemonic (ra, sp, t0, etc.) register names
- **Operand Syntax**: Ensures proper `in(reg)`, `out(reg)`, `inout(reg)` syntax

## Examples

Run the included examples to see the macro in action:

```bash
cargo run --example test_rasm        # Basic assembly instructions
cargo run --example test_operands    # Advanced operand parsing
cargo run --example test_validation  # Validation features
```

## Conditional Compilation

The macro uses conditional compilation to provide different behavior based on the target architecture:

- **RISC-V targets** (`target_arch = "riscv64"`): Generates actual `core::arch::asm!` inline assembly blocks + debug output
- **Other targets**: Provides debug output only (no assembly execution)

This allows you to:
- Develop and test RISC-V assembly code on any architecture
- Get validation and debugging on all platforms
- Have the assembly actually execute when targeting RISC-V

## Current Status

This implementation provides comprehensive RISC-V assembly macro functionality:

✅ Parses assembly strings  
✅ Extracts and validates operands  
✅ Validates RISC-V instructions and registers  
✅ Provides debug output  
✅ **Conditional inline assembly generation for RISC-V targets**  
✅ **Token re-emission for perfect `asm!` syntax compatibility**  

🔄 Future enhancements could include:  
- More comprehensive RISC-V instruction set support  
- Better error handling and reporting  
- Support for additional RISC-V variants (32-bit, embedded profiles)  

## Implementation Details

The macro uses:
- `syn` for parsing Rust token streams
- `quote` for generating Rust code
- Custom parsing logic for `asm!` macro syntax
- RISC-V instruction and register validation
- **Token re-emission for perfect syntax preservation**
- **Conditional compilation via `cfg(target_arch = "riscv64")`**

### Key Technical Insights

1. **Keyword Handling**: The `in` keyword in Rust is a reserved token, so it requires special handling with `Token![in]` rather than parsing as a regular identifier.

2. **Token Re-emission**: Instead of reconstructing operands from parsed syntax trees, the macro stores and re-emits the original input tokens. This guarantees perfect compatibility with `asm!` syntax.

3. **Conditional Generation**: Uses `cfg(target_arch = "riscv64")` to conditionally generate `core::arch::asm!` blocks only for RISC-V targets while providing debug output on all architectures.