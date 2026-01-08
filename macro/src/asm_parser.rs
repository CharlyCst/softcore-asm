//! Assembly Parser
//!
//! This module holds a parser that takes strings as input and extract various information from
//! assembly code.
//! For instance, assembly can include arbitrarily complex arithmetic expressions to compute the
//! offset of a load or store, which require a proper parser to determine operator precedence.
//!
//! We use [Pest](pest.rs) to generate a parser that produces un-typed nodes from a grammar specification
//! (in `asm_parser.pest`). The output of the Pest parser needs to be further processed to created
//! a typed AST.

use anyhow::{Result, anyhow};
use pest::Parser;
use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::PrattParser;
use pest_derive::Parser;
use std::sync::LazyLock;

// —————————————————————————————— Pest Parser ——————————————————————————————— //

#[derive(Parser)]
#[grammar = "asm_parser.pest"]
struct PestParser;

// ——————————————————————————— Typed Assembly AST ——————————————————————————— //

#[derive(Debug, PartialEq, Eq)]
pub enum AsmLine {
    Instr(Instr),
    Label(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Instr {
    pub mnemonic: String,
    pub operands: Vec<String>,
    pub attributes: Vec<Attribute>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Attribute {
    Abi {
        name: String,
        num_args: u64,
        return_type: ReturnType,
    },
    ReplaceWith {
        instr: Instr,
    },
    Static,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ReturnType {
    Unit,
    Never,
    U64,
    U32,
    I64,
    I32,
}

/// An expression, which can contain other expressions.
///
/// Example: (2 + 3) * 8
#[derive(Debug, PartialEq, Eq)]
pub enum Expr {
    Number(i64),
    Constant(String),
    Neg(Box<Expr>),
    Binop {
        lhs: Box<Expr>,
        op: Binop,
        rhs: Box<Expr>,
    },
}

/// An operation taking a right and left operand, such as '+' or '*'.
#[derive(Debug, PartialEq, Eq)]
pub enum Binop {
    Add,
    Sub,
    Mul,
    Div,
}

impl Expr {
    fn simplify(self) -> Expr {
        match self {
            Expr::Number(_) | Expr::Constant(_) => self,
            Expr::Neg(ref n) => {
                if let Some(n) = n.as_num() {
                    Expr::Number(-n)
                } else {
                    self
                }
            }
            Expr::Binop { lhs, op, rhs } => {
                let lhs = lhs.simplify();
                let rhs = rhs.simplify();
                if let (Some(lhs), Some(rhs)) = (lhs.as_num(), rhs.as_num()) {
                    let n = match op {
                        Binop::Add => lhs.wrapping_add(rhs),
                        Binop::Sub => lhs.wrapping_sub(rhs),
                        Binop::Mul => lhs.wrapping_mul(rhs),
                        Binop::Div => lhs.wrapping_div(rhs),
                    };
                    Expr::Number(n)
                } else {
                    Expr::Binop {
                        lhs: Box::new(lhs),
                        op,
                        rhs: Box::new(rhs),
                    }
                }
            }
        }
    }

    fn as_num(&self) -> Option<i64> {
        match self {
            Expr::Number(n) => Some(*n),
            _ => None,
        }
    }
}

// ——————————————————————————————— Public API ——————————————————————————————— //

/// Parses a list of assembly instructions
pub fn parse_instructions(assembly_template: &[String]) -> Result<Vec<AsmLine>> {
    let asm_text = assembly_template.join("\n");
    let mut result = Vec::new();
    let mut pending_attributes = Vec::new();

    for line in asm_text.lines() {
        let pairs = PestParser::parse(Rule::asm_line, line.trim())?
            .next()
            .unwrap();
        match parse_assembly_line(pairs)? {
            ParsedLine::Attribute(attr) => {
                // Accumulate attributes for the next instruction
                pending_attributes.push(attr);
            }
            ParsedLine::AsmLine(AsmLine::Instr(mut instr)) => {
                // Check for the "replace_with" attribute
                for attr in &pending_attributes {
                    if let Attribute::ReplaceWith { instr: new_instr } = attr {
                        instr = new_instr.clone();
                    }
                }

                // Attach accumulated attributes to this instruction
                instr.attributes = pending_attributes;
                pending_attributes = Vec::new();
                result.push(AsmLine::Instr(instr));
            }
            ParsedLine::AsmLine(asm_line) => {
                // Labels and other assembly lines don't get attributes
                // If there were pending attributes, they are lost
                pending_attributes.clear();
                result.push(asm_line);
            }
            ParsedLine::Skip => {
                // Directives, empty lines, etc. - don't clear pending attributes
            }
        }
    }

    Ok(result)
}

/// Parses an immediate offset, such as `2*8(x1)`
pub fn into_immediate_offset(input: &str) -> Result<(Expr, &'_ str)> {
    let pairs = PestParser::parse(Rule::imm_off, input)?.next().unwrap();
    parse_immediate_offset(pairs)
}

/// Parses an expression, such as `(2 + 3) * 8`
pub fn into_numeric_expr(input: &str) -> Result<Expr> {
    let pairs = PestParser::parse(Rule::expr, input)
        .unwrap()
        .next()
        .unwrap();
    parse_numeric_expr(pairs).map(|expr| expr.simplify())
}

// —————————————————————————————— Typed Parser —————————————————————————————— //

#[derive(Debug, PartialEq, Eq)]
enum ParsedLine {
    AsmLine(AsmLine),
    Attribute(Attribute),
    Skip, // Directives, empty lines, comments
}

fn parse_assembly_line(pair: Pair<Rule>) -> Result<ParsedLine> {
    let pairs = pair.into_inner().next().unwrap();
    match pairs.as_rule() {
        Rule::asm_instr => Ok(ParsedLine::AsmLine(AsmLine::Instr(parse_asm_instr(
            pairs,
            vec![],
        )?))),
        Rule::asm_label => Ok(ParsedLine::AsmLine(AsmLine::Label(parse_asm_label(pairs)?))),
        Rule::attr_line => Ok(ParsedLine::Attribute(parse_attribute(pairs)?)),
        Rule::directive => Ok(ParsedLine::Skip),
        Rule::empty_line => Ok(ParsedLine::Skip),
        _ => Err(anyhow!(
            "Could not parse assembly line, got: {:?}",
            pairs.as_rule()
        )),
    }
}

fn parse_asm_label(pair: Pair<Rule>) -> Result<String> {
    let pairs = pair.into_inner().next().unwrap();
    match pairs.as_rule() {
        Rule::label_id => Ok(pairs.as_str().to_string()),
        _ => Err(anyhow!("Expected a label, got: {:?}", pairs.as_rule())),
    }
}

fn parse_attribute(pair: Pair<Rule>) -> Result<Attribute> {
    // attr_line is: "//" ~ attribute
    let pairs = pair.into_inner().next().unwrap();
    match pairs.as_rule() {
        Rule::attribute => {
            let mut inner = pairs.into_inner();
            let attr_name = inner.next().unwrap().as_str();

            match attr_name {
                "abi" => parse_abi_attribute(inner),
                "replace_with" => parse_replace_with_attribute(inner),
                "static" => parse_static_attribute(inner),
                _ => Err(anyhow!("Unknown attribute: {}", attr_name)),
            }
        }
        _ => Err(anyhow!("Expected an attribute, got: {:?}", pairs.as_rule())),
    }
}

/// Parses an ABI attribute.
///
/// An ABI attribute specifies the calling convention and number of arguments for a function call.
/// It takes two or three arguments:
/// - A string literal specifying the ABI name (e.g., "C", "Rust", "Custom")
/// - A number literal specifying the number of arguments
/// - An optional return type ("!", "u64", "u32", "i64", "i32")
///
/// Example: `#[abi("C", 4)]` or `#[abi("C", 4, u64)]`
///
/// This would be used in assembly like:
/// ```text
/// // #[abi("C", 4, u64)]
/// call my_function
/// ```
fn parse_abi_attribute(mut args: Pairs<Rule>) -> Result<Attribute> {
    // First argument: string (ABI name)
    let name_arg = args
        .next()
        .ok_or_else(|| anyhow!("abi attribute requires arguments: abi(\"name\", num_args)"))?;

    let name = match name_arg.as_rule() {
        Rule::attribute_arg_str => {
            // Strip quotes from the string
            let s = name_arg.as_str();
            s.trim_matches('"').to_string()
        }
        _ => return Err(anyhow!("First argument of abi must be a string")),
    };

    // Second argument: number (number of arguments)
    let num_arg = args
        .next()
        .ok_or_else(|| anyhow!("abi attribute requires 2 arguments: abi(\"name\", num_args)"))?;

    let num_args = match num_arg.as_rule() {
        Rule::attribute_arg_num => num_arg.as_str().parse::<u64>()?,
        _ => return Err(anyhow!("Second argument of abi must be a number")),
    };

    // Third argument (optional): return type
    let return_type = match args.next() {
        Some(arg) if arg.as_rule() == Rule::attribute_arg_ret => match arg.as_str() {
            "!" => ReturnType::Never,
            "u64" => ReturnType::U64,
            "u32" => ReturnType::U32,
            "i64" => ReturnType::I64,
            "i32" => ReturnType::I32,
            _ => return Err(anyhow!("Invalid return type: {}", arg.as_str())),
        },
        Some(_) => {
            return Err(anyhow!(
                "Third argument of abi must be a return type (!, u64, u32, i64, i32)"
            ));
        }
        None => ReturnType::Unit, // Default to Unit if not specified
    };

    // Ensure no extra arguments
    if args.next().is_some() {
        return Err(anyhow!("abi attribute takes at most 3 arguments"));
    }

    Ok(Attribute::Abi {
        name,
        num_args,
        return_type,
    })
}

fn parse_replace_with_attribute(mut args: Pairs<Rule>) -> Result<Attribute> {
    let instr_arg = args
        .next()
        .ok_or_else(|| anyhow!("replace_with attribute requires one instruction as argument: replace_with(\"addi x10, x11, 42\")"))?;

    // Throw an error for extra arguments
    if args.next().is_some() {
        return Err(anyhow!(
            "replace_with attribute expects exactly one argument"
        ));
    }

    // Strip quotes from the string
    let instr_str = match instr_arg.as_rule() {
        Rule::attribute_arg_str => {
            let s = instr_arg.as_str();
            s.trim_matches('"')
        }
        _ => return Err(anyhow!("replace_with attribute argument must be a string")),
    };

    let instr = parse_asm_instr_from_str(instr_str)?;

    Ok(Attribute::ReplaceWith { instr })
}

/// Parses a static attribute.
///
/// A static attribute indicates that the symbol should be treated as a static, not a function.
///
/// Example: `#[static]`
///
/// This would be used in assembly like:
/// ```text
/// // #[static]
/// la x1, {my_static_symbol}
/// ```
fn parse_static_attribute(mut args: Pairs<Rule>) -> Result<Attribute> {
    // static attribute should have no arguments
    if args.next().is_some() {
        return Err(anyhow!("static attribute takes no arguments"));
    }
    Ok(Attribute::Static)
}

fn parse_asm_instr(pair: Pair<Rule>, attributes: Vec<Attribute>) -> Result<Instr> {
    let mut operands = Vec::new();
    let mut pairs = match pair.as_rule() {
        Rule::asm_instr => pair.into_inner(),
        _ => return Err(anyhow!("Expected an asm_line, got: {:?}", pair.as_rule())),
    };
    let mnemonic = pairs.next().unwrap().as_str().to_string(); // Always exist
    for pair in pairs {
        match pair.as_rule() {
            Rule::operand => operands.push(pair.as_str().to_string()),
            Rule::comment => (),
            _ => return Err(anyhow!("Invalid asm instruction: {:?}", pair)),
        }
    }

    Ok(Instr {
        mnemonic,
        operands,
        attributes,
    })
}

/// Parse a single instruction from a string.
fn parse_asm_instr_from_str(instr: &str) -> Result<Instr> {
    let pair = PestParser::parse(Rule::asm_instr, instr.trim())?
        .next()
        .unwrap();
    parse_asm_instr(pair, Vec::new())
}

/// Parses an immediate offset, such as `2*8(x1)`
fn parse_immediate_offset(pair: Pair<'_, Rule>) -> Result<(Expr, &'_ str)> {
    let mut pairs = pair.into_inner();

    // The offset if optional
    let offset = match pairs.peek().unwrap().as_rule() {
        Rule::expr => parse_numeric_expr(pairs.next().unwrap())?,
        _ => Expr::Number(0),
    };
    let register = parse_register(pairs.next().unwrap())?;
    Ok((offset.simplify(), register))
}

/// Parses an expression, such as `(2 + 3) * 8`
fn parse_numeric_expr(pair: Pair<Rule>) -> Result<Expr> {
    static NUM_EXPR_PARSER: LazyLock<PrattParser<Rule>> = LazyLock::new(|| {
        use Rule::*;
        use pest::pratt_parser::Assoc::*;
        use pest::pratt_parser::Op;

        // From low to high precedence
        PrattParser::new()
            .op(Op::infix(add, Left) | Op::infix(sub, Left))
            .op(Op::infix(mul, Left) | Op::infix(div, Left))
            .op(Op::prefix(unary_minus))
    });

    // Return 0 for empty expressions
    let pair = pair.into_inner();
    let Some(_) = pair.peek() else {
        return Ok(Expr::Number(0));
    };

    // Non-empty expression, parse with our expression parser
    let expr = NUM_EXPR_PARSER
        .map_primary(|atom| match atom.as_rule() {
            Rule::number => Ok(Expr::Number(parse_number(atom)?)),
            Rule::hex_number => Ok(Expr::Number(parse_hex_number(atom)?)),
            Rule::constant => Ok(Expr::Constant(atom.as_str().to_string())),
            Rule::expr => parse_numeric_expr(atom),
            _ => Err(anyhow!("Unexpected atom: {:?}", atom.as_rule())),
        })
        .map_infix(|left, op, right| {
            let op = parse_binop(op)?;
            Ok(Expr::Binop {
                lhs: Box::new(left?),
                op,
                rhs: Box::new(right?),
            })
        })
        .map_prefix(|op, rhs| match op.as_rule() {
            Rule::unary_minus => Ok(Expr::Neg(Box::new(rhs?))),
            _ => Err(anyhow!("Unexpected prefix operator: {:?}", op.as_rule())),
        })
        .parse(pair)?;

    Ok(expr)
}

fn parse_register(pair: Pair<'_, Rule>) -> Result<&'_ str> {
    match pair.as_rule() {
        Rule::any_reg => Ok(pair.as_str()),
        _ => Err(anyhow!("Expected a register, got: {:?}", pair)),
    }
}

fn parse_number(pair: Pair<Rule>) -> Result<i64> {
    match pair.as_rule() {
        Rule::number => Ok(pair.as_str().parse::<i64>()?),
        _ => Err(anyhow!("Expected a number, got: {:?}", pair)),
    }
}

fn parse_hex_number(pair: Pair<Rule>) -> Result<i64> {
    match pair.as_rule() {
        Rule::hex_number => Ok(i64::from_str_radix(
            pair.as_str().strip_prefix("0x").unwrap(),
            16,
        )?),
        _ => Err(anyhow!("Expected an hex number, got: {:?}", pair)),
    }
}

fn parse_binop(pair: Pair<Rule>) -> Result<Binop> {
    match pair.as_rule() {
        Rule::add => Ok(Binop::Add),
        Rule::sub => Ok(Binop::Sub),
        Rule::mul => Ok(Binop::Mul),
        Rule::div => Ok(Binop::Div),
        _ => Err(anyhow!("Unknown binary operator: {:?}", pair.as_rule())),
    }
}

// ————————————————————————————————— Tests —————————————————————————————————— //

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn immediate_offset() {
        let parse = |s: &'static str| {
            let ast = PestParser::parse(Rule::imm_off, s).unwrap().next().unwrap();
            parse_immediate_offset(ast).unwrap()
        };
        assert_eq!(parse("8(x1)"), (Expr::Number(8), "x1"));
        assert_eq!(parse("2*8(x1)"), (Expr::Number(16), "x1"));
        assert_eq!(parse("(2 + 6)*8(x1)"), (Expr::Number(64), "x1"));
        assert_eq!(parse("8({some_reg})"), (Expr::Number(8), "{some_reg}"));
    }

    #[test]
    fn num_expr() {
        let parse = |s: &'static str| {
            let ast = PestParser::parse(Rule::expr, s).unwrap().next().unwrap();
            parse_numeric_expr(ast).unwrap().simplify()
        };
        assert_eq!(parse("3"), Expr::Number(3));
        assert_eq!(parse("3+2"), Expr::Number(5));
        assert_eq!(parse("3-2"), Expr::Number(1));
        assert_eq!(parse("3*2"), Expr::Number(6));
        assert_eq!(parse("8/2"), Expr::Number(4));
        assert_eq!(parse("3 + 2"), Expr::Number(5));
        assert_eq!(parse("(2 + 6) * 8"), Expr::Number(64));
        assert_eq!(parse("-3"), Expr::Number(-3));
        assert_eq!(parse("0x42"), Expr::Number(0x42));
    }

    #[test]
    fn assembly_instr() {
        // Test an instruction without operands
        let wfi = parse_asm_instr_from_str("wfi").unwrap();
        assert_eq!(wfi.mnemonic, "wfi");
        assert_eq!(wfi.operands, Vec::<String>::new());
        assert_eq!(wfi.attributes, Vec::<Attribute>::new());

        // Test the same instruction with whitespace
        let wfi = parse_asm_instr_from_str("  wfi  ").unwrap();
        assert_eq!(wfi.mnemonic, "wfi");
        assert_eq!(wfi.operands, Vec::<String>::new());

        // Test an instruction with operands
        let csrw = parse_asm_instr_from_str("csrw mscratch, x1").unwrap();
        assert_eq!(csrw.mnemonic, "csrw");
        assert_eq!(csrw.operands, vec!["mscratch", "x1"]);
        assert_eq!(csrw.attributes, Vec::<Attribute>::new());

        // Test with extra whitespace
        let csrw = parse_asm_instr_from_str("   csrw  mscratch  , x1  ").unwrap();
        assert_eq!(csrw.mnemonic, "csrw");
        assert_eq!(csrw.operands, vec!["mscratch", "x1"]);

        // Test an instruction with comments
        let csrw = parse_asm_instr_from_str("csrw mscratch, x1 // test comment").unwrap();
        assert_eq!(csrw.mnemonic, "csrw");
        assert_eq!(csrw.operands, vec!["mscratch", "x1"]);

        // Test an instruction with multiple operands
        let add = parse_asm_instr_from_str("add x1, x2, x3").unwrap();
        assert_eq!(add.mnemonic, "add");
        assert_eq!(add.operands, vec!["x1", "x2", "x3"]);
    }

    #[test]
    fn assembly_line() {
        let parse = |s: &'static str| {
            let ast = PestParser::parse(Rule::asm_line, s)
                .unwrap()
                .next()
                .unwrap();
            parse_assembly_line(ast).unwrap()
        };

        // Test an instruction without operands
        let wfi = ParsedLine::AsmLine(AsmLine::Instr(Instr {
            mnemonic: "wfi".to_string(),
            operands: vec![],
            attributes: vec![],
        }));
        assert_eq!(parse("wfi"), wfi);
        assert_eq!(parse("wfi // This is a test comment"), wfi);

        // Test an instruction with operands
        let csrw = ParsedLine::AsmLine(AsmLine::Instr(Instr {
            mnemonic: "csrw".to_string(),
            operands: vec!["mscratch".to_string(), "x1".to_string()],
            attributes: vec![],
        }));
        assert_eq!(parse("csrw mscratch, x1"), csrw);
        assert_eq!(parse("   csrw  mscratch  , x1  "), csrw);
        assert_eq!(parse("csrw mscratch, x1 // Test comment"), csrw);
    }

    #[test]
    fn directive() {
        let parse = |s: &'static str| {
            let ast = PestParser::parse(Rule::asm_line, s)
                .unwrap()
                .next()
                .unwrap();
            parse_assembly_line(ast).unwrap()
        };

        // Directives should return Skip (be ignored)
        assert_eq!(parse(".option push"), ParsedLine::Skip);
        assert_eq!(parse(".option pop"), ParsedLine::Skip);
        assert_eq!(parse(".option norvc"), ParsedLine::Skip);
        assert_eq!(parse("  .option push  "), ParsedLine::Skip);
        assert_eq!(parse(".option rvc"), ParsedLine::Skip);
    }

    #[test]
    fn attributes_on_instructions() {
        // Test that attributes are correctly attached to instructions
        let code = vec!["// #[abi(\"C\", 4)]".to_string(), "call foo".to_string()];
        let result = parse_instructions(&code).unwrap();
        assert_eq!(result.len(), 1);
        match &result[0] {
            AsmLine::Instr(instr) => {
                assert_eq!(instr.mnemonic, "call");
                assert_eq!(instr.operands, vec!["foo"]);
                assert_eq!(instr.attributes.len(), 1);
                assert_eq!(
                    instr.attributes[0],
                    Attribute::Abi {
                        name: "C".to_string(),
                        num_args: 4,
                        return_type: ReturnType::Unit,
                    }
                );
            }
            _ => panic!("Expected instruction"),
        }

        // Test multiple attributes on a single instruction
        let code = vec![
            "// #[abi(\"C\", 2)]".to_string(),
            "// #[abi(\"Rust\", 3)]".to_string(),
            "// #[abi(\"C\", 0)]".to_string(),
            "csrw mscratch, x1".to_string(),
        ];
        let result = parse_instructions(&code).unwrap();
        assert_eq!(result.len(), 1);
        match &result[0] {
            AsmLine::Instr(instr) => {
                assert_eq!(instr.mnemonic, "csrw");
                assert_eq!(instr.attributes.len(), 3);
            }
            _ => panic!("Expected instruction"),
        }

        // Test that attributes only apply to the next instruction
        let code = vec![
            "// #[abi(\"C\", 1)]".to_string(),
            "call foo".to_string(),
            "call bar".to_string(),
        ];
        let result = parse_instructions(&code).unwrap();
        assert_eq!(result.len(), 2);
        match &result[0] {
            AsmLine::Instr(instr) => {
                assert_eq!(instr.mnemonic, "call");
                assert_eq!(instr.operands, vec!["foo"]);
                assert_eq!(instr.attributes.len(), 1);
            }
            _ => panic!("Expected instruction"),
        }
        match &result[1] {
            AsmLine::Instr(instr) => {
                assert_eq!(instr.mnemonic, "call");
                assert_eq!(instr.operands, vec!["bar"]);
                assert_eq!(instr.attributes.len(), 0);
            }
            _ => panic!("Expected instruction"),
        }

        // Test that empty lines/directives between attributes and instruction preserve attributes
        let code = vec![
            "// #[abi(\"C\", 6)]".to_string(),
            "".to_string(),
            ".option norvc".to_string(),
            "call foo".to_string(),
        ];
        let result = parse_instructions(&code).unwrap();
        assert_eq!(result.len(), 1);
        match &result[0] {
            AsmLine::Instr(instr) => {
                assert_eq!(instr.attributes.len(), 1);
            }
            _ => panic!("Expected instruction"),
        }
    }

    #[test]
    fn abi_attribute_parsing() {
        // Test basic abi attribute parsing
        let code = vec!["// #[abi(\"C\", 4)]".to_string(), "call foo".to_string()];
        let result = parse_instructions(&code).unwrap();
        assert_eq!(result.len(), 1);
        match &result[0] {
            AsmLine::Instr(instr) => {
                assert_eq!(instr.attributes.len(), 1);
                match &instr.attributes[0] {
                    Attribute::Abi {
                        name,
                        num_args,
                        return_type,
                    } => {
                        assert_eq!(name, "C");
                        assert_eq!(*num_args, 4);
                        assert_eq!(*return_type, ReturnType::Unit);
                    }
                    _ => panic!("Expected Abi attribute"),
                }
            }
            _ => panic!("Expected instruction"),
        }

        // Test different ABI names
        let code = vec!["// #[abi(\"Rust\", 0)]".to_string(), "call bar".to_string()];
        let result = parse_instructions(&code).unwrap();
        match &result[0] {
            AsmLine::Instr(instr) => match &instr.attributes[0] {
                Attribute::Abi {
                    name,
                    num_args,
                    return_type,
                } => {
                    assert_eq!(name, "Rust");
                    assert_eq!(*num_args, 0);
                    assert_eq!(*return_type, ReturnType::Unit);
                }
                _ => panic!("Expected Abi attribute"),
            },
            _ => panic!("Expected instruction"),
        }

        // Test with larger number of arguments
        let code = vec![
            "// #[abi(\"Custom\", 100)]".to_string(),
            "call baz".to_string(),
        ];
        let result = parse_instructions(&code).unwrap();
        match &result[0] {
            AsmLine::Instr(instr) => match &instr.attributes[0] {
                Attribute::Abi {
                    name,
                    num_args,
                    return_type,
                } => {
                    assert_eq!(name, "Custom");
                    assert_eq!(*num_args, 100);
                    assert_eq!(*return_type, ReturnType::Unit);
                }
                _ => panic!("Expected Abi attribute"),
            },
            _ => panic!("Expected instruction"),
        }

        // Test never return type attribute
        let code = vec![
            "// #[abi(\"C\", 1, !)]".to_string(),
            "call exit".to_string(),
        ];
        let result = parse_instructions(&code).unwrap();
        match &result[0] {
            AsmLine::Instr(instr) => match &instr.attributes[0] {
                Attribute::Abi {
                    name,
                    num_args,
                    return_type,
                } => {
                    assert_eq!(name, "C");
                    assert_eq!(*num_args, 1);
                    assert_eq!(*return_type, ReturnType::Never);
                }
                _ => panic!("Expected Abi attribute"),
            },
            _ => panic!("Expected instruction"),
        }

        // Test u64 return type
        let code = vec![
            "// #[abi(\"C\", 1, u64)]".to_string(),
            "call get_value".to_string(),
        ];
        let result = parse_instructions(&code).unwrap();
        match &result[0] {
            AsmLine::Instr(instr) => match &instr.attributes[0] {
                Attribute::Abi {
                    name,
                    num_args,
                    return_type,
                } => {
                    assert_eq!(name, "C");
                    assert_eq!(*num_args, 1);
                    assert_eq!(*return_type, ReturnType::U64);
                }
                _ => panic!("Expected Abi attribute"),
            },
            _ => panic!("Expected instruction"),
        }
    }

    #[test]
    fn abi_attribute_errors() {
        // Test missing arguments
        let code = vec!["// #[abi]".to_string(), "call foo".to_string()];
        assert!(parse_instructions(&code).is_err());

        // Test missing second argument
        let code = vec!["// #[abi(\"C\")]".to_string(), "call foo".to_string()];
        assert!(parse_instructions(&code).is_err());

        // Test invalid third argument (should be "!")
        let code = vec!["// #[abi(\"C\", 4, 5)]".to_string(), "call foo".to_string()];
        assert!(parse_instructions(&code).is_err());

        // Test too many arguments
        let code = vec![
            "// #[abi(\"C\", 4, !, !)]".to_string(),
            "call foo".to_string(),
        ];
        assert!(parse_instructions(&code).is_err());

        // Test wrong first argument type (should be string)
        let code = vec!["// #[abi(42, 4)]".to_string(), "call foo".to_string()];
        assert!(parse_instructions(&code).is_err());

        // Test wrong second argument type (should be number)
        let code = vec![
            "// #[abi(\"C\", \"four\")]".to_string(),
            "call foo".to_string(),
        ];
        assert!(parse_instructions(&code).is_err());

        // Test unknown attribute
        let code = vec!["// #[unknown]".to_string(), "call foo".to_string()];
        assert!(parse_instructions(&code).is_err());
    }

    #[test]
    fn replace_with_attribute() {
        // Test basic replace_with attribute
        let code = vec![
            "// #[replace_with(\"addi x10, x10, 42\")]".to_string(),
            "wfi".to_string(),
        ];
        let result = parse_instructions(&code).unwrap();
        assert_eq!(result.len(), 1);
        match &result[0] {
            AsmLine::Instr(instr) => {
                // The instruction should be replaced with addi
                assert_eq!(instr.mnemonic, "addi");
                assert_eq!(instr.operands, vec!["x10", "x10", "42"]);
            }
            _ => panic!("Expected instruction"),
        }

        // Test that replace_with only affects the next instruction
        let code = vec![
            "// #[replace_with(\"nop\")]".to_string(),
            "wfi".to_string(),
            "wfi".to_string(),
        ];
        let result = parse_instructions(&code).unwrap();
        assert_eq!(result.len(), 2);
        match &result[0] {
            AsmLine::Instr(instr) => {
                assert_eq!(instr.mnemonic, "nop");
            }
            _ => panic!("Expected instruction"),
        }
        match &result[1] {
            AsmLine::Instr(instr) => {
                assert_eq!(instr.mnemonic, "wfi");
                assert_eq!(instr.attributes.len(), 0);
            }
            _ => panic!("Expected instruction"),
        }
    }
}
