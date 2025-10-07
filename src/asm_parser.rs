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
use pest::iterators::Pair;
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

/// Parses a line of assembly.
///
/// Note that the line can be a comment or empty, in which case None is returned.
pub fn into_asm_line(input: &str) -> Result<Option<AsmLine>> {
    let pairs = PestParser::parse(Rule::asm_line, input)?.next().unwrap();
    parse_assembly_line(pairs)
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

fn parse_assembly_line(pair: Pair<Rule>) -> Result<Option<AsmLine>> {
    let pairs = pair.into_inner().next().unwrap();
    match pairs.as_rule() {
        Rule::asm_instr => Ok(Some(AsmLine::Instr(parse_asm_instr(pairs)?))),
        Rule::asm_label => Ok(Some(AsmLine::Label(parse_asm_label(pairs)?))),
        Rule::empty_line => Ok(None),
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

fn parse_asm_instr(pair: Pair<Rule>) -> Result<Instr> {
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

    Ok(Instr { mnemonic, operands })
}

/// Parses an immediate offset, such as `2*8(x1)`
fn parse_immediate_offset(pair: Pair<'_, Rule>) -> Result<(Expr, &'_ str)> {
    let mut pairs = pair.into_inner();
    let offset = parse_numeric_expr(pairs.next().unwrap())?;
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
        .parse(pair.into_inner())?;

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
    fn assembly_line() {
        let parse = |s: &'static str| {
            let ast = PestParser::parse(Rule::asm_line, s)
                .unwrap()
                .next()
                .unwrap();
            parse_assembly_line(ast).unwrap()
        };

        // Test an instruction without operands
        let wfi = AsmLine::Instr(Instr {
            mnemonic: "wfi".to_string(),
            operands: vec![],
        });
        assert_eq!(parse("wfi").unwrap(), wfi);
        assert_eq!(parse("wfi // This is a test comment").unwrap(), wfi);

        // Test an instruction with operands
        let csrw = AsmLine::Instr(Instr {
            mnemonic: "csrw".to_string(),
            operands: vec!["mscratch".to_string(), "x1".to_string()],
        });
        assert_eq!(parse("csrw mscratch, x1").unwrap(), csrw);
        assert_eq!(parse("   csrw  mscratch  , x1  ").unwrap(), csrw);
        assert_eq!(parse("csrw mscratch, x1 // Test comment").unwrap(), csrw);
    }
}
