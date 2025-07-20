# RASM Project Knowledge Base

## Project Overview

**RASM** is a Rust procedural macro that mimics the standard library's `asm!` macro specifically for RISC-V assembly code. It provides conditional compilation, instruction validation, and softcore simulation capabilities.

### Key Features
- **Conditional Compilation**: Different behavior for RISC-V targets vs other architectures
- **Softcore Simulation**: CSR operations can be simulated using `softcore-rv64` 
- **Multi-instruction Support**: Handle multiple assembly instructions in one macro call
- **Register Allocation**: Proper register assignment for complex instruction sequences
- **CSR Instruction Support**: Both shorthand (`csrw`) and full (`csrrw`) CSR instruction formats
- **Perfect Syntax Compatibility**: Token re-emission ensures 100% `asm!` syntax compatibility

## Architecture & Design

### Three Compilation Modes
1. **RISC-V Target** (`cfg(target_arch = "riscv64")`): Generates actual `core::arch::asm!` blocks
2. **Softcore Mode** (`cfg(feature = "softcore")`): Generates softcore simulation code for CSR operations
3. **Debug Mode** (all other targets): Provides debug output only

### Instruction Processing Pipeline
1. **Parse**: Tokenize assembly template and operands using `syn`
2. **Analyze**: Extract instruction info, placeholders, and CSR operations
3. **Allocate**: Assign unique registers to each operand
4. **Generate**: Emit appropriate code based on compilation mode

### CSR Instruction Support
- **2-operand format**: `csrw csr, rs` (CSR at index 1)
- **3-operand format**: `csrrw rd, csr, rs` (CSR at index 2)
- **Supported instructions**: `csrw`, `csrs`, `csrc`, `csrwi`, `csrsi`, `csrci`, `csrrw`, `csrrs`, `csrrc`, `csrrwi`, `csrrsi`, `csrrci`, `csrr`, `csrri`

## File Structure

```
rasm/
├── Cargo.toml          # Dependencies: syn, quote, proc-macro2, softcore-rv64
├── README.md           # Project documentation
├── CLAUDE.md          # This file - AI assistant knowledge base
├── src/
│   └── lib.rs         # Main macro implementation (~650 lines)
└── examples/          # Test cases and examples
    ├── softcore.rs            # Softcore simulation with CSR operations
    ├── test_multi_csr.rs      # Multiple CSR instructions in one macro
    ├── test_mixed_syntax.rs   # Mixed named/positional operands
    ├── test_rasm.rs           # Basic assembly instructions
    ├── test_operands.rs       # Operand parsing tests
    ├── test_validation.rs     # Validation features
    ├── test_expansion.rs      # Macro expansion tests
    └── test_cfg.rs            # Conditional compilation tests
```

## Key Data Structures

### `AsmOperand` - Operand Types
```rust
enum AsmOperand {
    Input { name: Option<Ident>, reg: Ident, expr: Expr },    // in(reg) expr
    Output { name: Option<Ident>, reg: Ident, expr: Expr },   // out(reg) expr  
    InOut { name: Option<Ident>, reg: Ident, expr: Expr },    // inout(reg) expr
    Options(Expr),                                            // options(nomem, nostack)
    Raw(Expr),                                                // raw expressions
}
```

### `InstructionInfo` - Parsed Instruction Metadata
```rust
struct InstructionInfo {
    instruction: String,       // "csrrw {prev}, mscratch, {x}"
    placeholders: Vec<String>, // ["{prev}", "{x}"]
    csr_name: Option<String>,  // Some("mscratch")
    is_csr: bool,              // true
}
```

### `RegAllocation` - Register Assignment
```rust
struct RegAllocation {
    operand_index: usize,      // Index in operands array
    register: String,          // "X1", "X2", etc.
    is_input: bool,           // Can be read from
    is_output: bool,          // Can be written to
}
```

### `MultiInstructionAnalysis` - Cross-Instruction Analysis
```rust
struct MultiInstructionAnalysis {
    instructions: Vec<InstructionInfo>,
    register_allocation: Vec<RegAllocation>,
    instruction_mappings: Vec<InstructionOperandMapping>,
    has_csr_operations: bool,
}
```

## Testing & Development Commands

### Basic Testing
```bash
# Test basic functionality
cargo run --example test_rasm

# Test operand parsing
cargo run --example test_operands

# Test validation features
cargo run --example test_validation

# Test mixed syntax support
cargo run --example test_mixed_syntax
```

### Softcore Testing (CSR Operations)
```bash
# Test softcore simulation
cargo run --example softcore --features softcore

# Test multiple CSR instructions
cargo run --example test_multi_csr --features softcore
```

### Code Quality & Debugging
```bash
# Check for warnings and errors
cargo check

# Run clippy for linting
cargo clippy

# Expand macro output for debugging
cargo expand --example softcore --features softcore

# View macro output without compilation noise
cargo expand --example softcore --features softcore 2>/dev/null
```

### Specific Debugging Commands
```bash
# Check register allocation in expanded code
cargo expand --example test_multi_csr --features softcore 2>/dev/null | grep -A 10 "core.csrrw"

# View CSR instruction generation
cargo expand --example softcore --features softcore 2>/dev/null | grep -A 5 -B 5 "csr_name_map_backwards"
```

## Development Workflows

### Adding New CSR Instruction Support
1. Add instruction to `is_csr_instruction()` function
2. Update `extract_csr_name()` with correct operand index
3. Add to `generate_softcore_code()` match statement
4. Test with new example in `examples/`

### Debugging Register Allocation Issues
1. Run example with debug output: `cargo run --example <name> --features softcore`
2. Check `MultiInstructionAnalysis` debug output for register assignments
3. Expand macro: `cargo expand --example <name> --features softcore 2>/dev/null`
4. Verify each instruction uses correct registers (X1, X2, X3, X4, etc.)

### Testing Multi-Instruction Scenarios
1. Create example with multiple instructions in one `rasm!` call
2. Ensure each operand gets unique register allocation
3. Verify softcore code generation handles all instructions
4. Test both placeholder and literal register combinations

## Key Functions & Logic

### `extract_csr_name()` - CSR Name Extraction
- Handles both 2-operand (`csrw csr, rs`) and 3-operand (`csrrw rd, csr, rs`) formats
- Returns `None` for placeholder CSR names (`{csr_name}`)
- Uses early returns to avoid deep nesting

### `build_operand_register_map()` - Register Allocation
- Assigns unique registers (X1, X2, X3...) to each named operand
- Creates mappings from placeholders to registers
- Handles input, output, and inout operands correctly

### `generate_softcore_code()` - Code Generation
- Creates setup code for input registers
- Generates CSR instruction calls using `core.csrrw()`
- Creates extraction code for output registers
- Wraps everything in `SOFT_CORE.with_borrow_mut()` closure

## Recent Technical Decisions & Changes

### Register Allocation Bug Fix
**Problem**: Multiple CSR instructions incorrectly reused registers (X1, X2) instead of unique assignment.
**Solution**: Implemented proper placeholder-to-register mapping with unique register allocation per operand.

### CSR Shorthand Support
**Problem**: `extract_csr_name` only worked with 3+ operand instructions, breaking `csrw pmpcfg10, {cfg}` syntax.
**Solution**: Enhanced to handle both 2-operand and 3-operand CSR instruction formats.

### Code Cleanup
**Problem**: Many unused struct fields and function parameters from earlier development.
**Solution**: Removed all unused code, eliminated compiler warnings, simplified data structures.

### Token Re-emission Strategy
**Decision**: Re-emit original input tokens instead of reconstructing from parsed AST.
**Benefit**: Guarantees 100% compatibility with `asm!` syntax, handles edge cases automatically.

## Common Issues & Solutions

### CSR Instruction Not Recognized
**Symptom**: `csr_name: None` in debug output
**Cause**: Instruction not in `is_csr_instruction()` list or wrong operand count
**Solution**: Add instruction to validation list and `extract_csr_name()` logic

### Register Allocation Problems  
**Symptom**: Multiple instructions using same registers (X1, X2)
**Cause**: Register allocation not respecting operand uniqueness
**Solution**: Check `build_operand_register_map()` logic and debug output

### Softcore Runtime Errors
**Symptom**: `Illegal_Instruction` or `unwrap()` panics in softcore mode
**Cause**: Invalid CSR name or unsupported instruction in softcore simulator
**Solution**: Use valid CSR names like `mscratch`, `mstatus` for testing

### Macro Expansion Issues
**Symptom**: Compilation errors in generated code
**Cause**: Incorrect token generation or missing imports
**Solution**: Use `cargo expand` to debug generated code, check imports

## Testing Strategies

### Unit Testing Approach
- Each example focuses on specific functionality
- `softcore.rs`: Basic CSR operations and multi-instruction
- `test_multi_csr.rs`: Register allocation correctness
- `test_mixed_syntax.rs`: Named vs positional operands

### Verification Methods
1. **Debug Output**: Check parsed instruction analysis
2. **Macro Expansion**: Verify generated code correctness  
3. **Runtime Testing**: Ensure softcore simulation works
4. **Cross-Platform**: Test on non-RISC-V targets for debug mode

## Dependencies & Features

### Core Dependencies
- `syn = "2.0"` with `"full"` features - AST parsing
- `quote = "1.0"` - Code generation  
- `proc-macro2 = "1.0"` - Token manipulation
- `softcore-rv64 = "0.4.0"` - RISC-V simulation

### Feature Flags
- `softcore` - Enables softcore simulation code generation
- Default: Debug output only

### Conditional Compilation
- `cfg(target_arch = "riscv64")` - Real assembly generation
- `cfg(feature = "softcore")` - Softcore simulation
- Default - Debug output only

This knowledge base should provide everything needed to understand, develop, and debug the rasm project effectively.