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

// ——————————————————————————————— Typed Ast ———————————————————————————————— //

/// An expression, which can contain other expressions.
///
/// Example: (2 + 3) * 8
#[derive(Debug)]
pub enum Expr {
    Number(i64),
    Binop {
        rhs: Box<Expr>,
        op: Binop,
        lhs: Box<Expr>,
    },
}

/// An operation taking a right and left operand, such as '+' or '*'.
#[derive(Debug)]
pub enum Binop {
    Add,
    Sub,
    Mul,
    Div,
}

impl Expr {
    fn evaluate(&self) -> i64 {
        match self {
            Expr::Number(n) => *n,
            Expr::Binop { rhs, op, lhs } => match op {
                Binop::Add => rhs.evaluate().wrapping_add(lhs.evaluate()),
                Binop::Sub => rhs.evaluate().wrapping_sub(lhs.evaluate()),
                Binop::Mul => rhs.evaluate().wrapping_mul(lhs.evaluate()),
                Binop::Div => rhs.evaluate().wrapping_div(lhs.evaluate()),
            },
        }
    }
}

// —————————————————————————————— Typed Parser —————————————————————————————— //

/// Parses an expression, such as `(2 + 3) * 8`
pub fn parse_immediate_offset(pair: Pair<Rule>) -> Result<i64> {
    static IMM_OFFSET_PARSER: LazyLock<PrattParser<Rule>> = LazyLock::new(|| {
        use Rule::*;
        use pest::pratt_parser::Assoc::*;
        use pest::pratt_parser::Op;

        // From low to high precedence
        PrattParser::new()
            .op(Op::infix(add, Left) | Op::infix(sub, Left))
            .op(Op::infix(mul, Left) | Op::infix(div, Left))
    });

    let expr = IMM_OFFSET_PARSER
        .map_primary(|atom| match atom.as_rule() {
            Rule::number => Ok(Expr::Number(parse_number(atom)?)),
            _ => Err(anyhow!("Unexpected atom: {:?}", atom.as_rule())),
        })
        .map_infix(|left, op, right| {
            let op = parse_binop(op)?;
            Ok(Expr::Binop {
                rhs: Box::new(left?),
                op,
                lhs: Box::new(right?),
            })
        })
        .parse(pair.into_inner())?;

    Ok(expr.evaluate())
}

fn parse_number(pair: Pair<Rule>) -> Result<i64> {
    match pair.as_rule() {
        Rule::number => Ok(pair.as_str().parse::<i64>()?),
        _ => Err(anyhow!("Expected a number, got: {:?}", pair)),
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
        let expr_as_pair =
            |s: &'static str| PestParser::parse(Rule::expr, s).unwrap().next().unwrap();
        assert_eq!(parse_immediate_offset(expr_as_pair("3")).unwrap(), 3);
        assert_eq!(parse_immediate_offset(expr_as_pair("3+2")).unwrap(), 5);
        assert_eq!(parse_immediate_offset(expr_as_pair("3-2")).unwrap(), 1);
        assert_eq!(parse_immediate_offset(expr_as_pair("3*2")).unwrap(), 6);
        assert_eq!(parse_immediate_offset(expr_as_pair("8/2")).unwrap(), 4);
    }
}
