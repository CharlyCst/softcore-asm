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

## Current Status

This is an initial implementation that focuses on parsing and validation. The macro currently:

✅ Parses assembly strings  
✅ Extracts and validates operands  
✅ Validates RISC-V instructions and registers  
✅ Provides debug output  

🔄 Future enhancements could include:  
- Actual inline assembly code generation  
- More comprehensive RISC-V instruction set support  
- Better error handling and reporting  
- Integration with actual RISC-V targets  

## Implementation Details

The macro uses:
- `syn` for parsing Rust token streams
- `quote` for generating Rust code
- Custom parsing logic for `asm!` macro syntax
- RISC-V instruction and register validation

Key insight: The `in` keyword in Rust is a reserved token, so it requires special handling with `Token![in]` rather than parsing as a regular identifier.