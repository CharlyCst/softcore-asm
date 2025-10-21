//! Relooper
//!
//! This module is responsible for processing raw assembly lines to re-construct the high-level
//! control flow. This is required because arbitrary assembly jumps must be converted to Rust's
//! control flow primitives such as `if`s and `loop`s.

use crate::arch::Arch;
use crate::asm_parser::{AsmLine, Instr};
use crate::{Context, ParsedAssembly};
use anyhow::{Result, anyhow};

// —————————————————————————————— Relooper AST —————————————————————————————— //

/// Unique identifier for a basic block
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BasicBlockID(usize);

impl BasicBlockID {
    /// Create a new basic block ID from an index
    pub fn new(id: usize) -> Self {
        BasicBlockID(id)
    }
}

/// A basic block is a sequence of instructions.
///
/// Within the basic block no instruction changes the control flow. Control flow changes such as
/// jumps are only allowed at the junction of two basic blocks. This is the "raw" version that
/// uses string labels instead of resolved basic block IDs.
#[derive(Debug)]
pub struct RawBasicBlock {
    /// Labels that mark the entry to this basic block
    pub labels: Vec<String>,
    /// Sequential instructions within the block
    pub instrs: Vec<Instr>,
    /// Control flow instruction at the end of the block (using string labels)
    pub terminator: LabelTerminator,
}

impl Default for RawBasicBlock {
    fn default() -> Self {
        RawBasicBlock {
            labels: Vec::new(),
            instrs: Vec::new(),
            terminator: LabelTerminator::Done,
        }
    }
}

/// A basic block with resolved control flow targets.
///
/// This is the resolved version of `RawBasicBlock` where string labels have been
/// converted to basic block IDs, forming a complete control flow graph.
#[derive(Debug)]
pub struct BasicBlock {
    /// Unique identifier for this block
    pub id: BasicBlockID,
    /// Sequential instructions within the block
    pub instrs: Vec<Instr>,
    /// Control flow instruction at the end (using resolved BasicBlockIDs)
    pub terminator: Terminator,
}

/// Control flow terminator using string labels (unresolved).
///
/// This represents the control flow instruction at the end of a basic block
/// before labels have been resolved to basic block IDs.
#[derive(Debug)]
pub enum LabelTerminator {
    /// No control flow - end of execution or fallthrough to next block
    Done,
    /// Conditional branch - jump to label if condition is true, otherwise fallthrough
    Branch { cond: Conditional, if_true: String },
    /// Unconditional jump to a label
    Jump(String),
}

/// Control flow terminator using resolved basic block IDs.
///
/// This represents the control flow instruction at the end of a basic block
/// after all string labels have been resolved to basic block IDs.
#[derive(Clone, Debug)]
pub enum Terminator {
    /// End of execution - no successor blocks
    Done,
    /// Conditional branch - jump to if_true if condition holds, otherwise to if_false
    Branch {
        cond: Conditional,
        if_true: BasicBlockID,
        if_false: BasicBlockID,
    },
    /// Unconditional jump to a basic block
    Jump(BasicBlockID),
}

/// Branch condition for conditional control flow.
///
/// Represents comparison operations used in branch instructions.
/// Each variant contains two register names to compare.
#[derive(Clone, Debug)]
pub enum Conditional {
    /// Equal comparison (beq)
    Eq(String, String),
    /// Not equal comparison (bne)
    Ne(String, String),
    /// Less than comparison - signed (blt)
    Lt(String, String),
    /// Greater or equal comparison - signed (bge)
    Ge(String, String),
    /// Less than comparison - unsigned (bltu)
    Ltu(String, String),
    /// Greater or equal comparison - unsigned (bgeu)
    Geu(String, String),
}

/// Collection of basic blocks with unresolved control flow.
///
/// Control flow targets are still represented as string labels. To create a usable
/// control flow graph, these labels must be resolved to basic block IDs via `into_cfg()`.
pub struct RawBasicBlocks<A> {
    /// Vector of raw basic blocks with label-based control flow
    pub blocks: Vec<RawBasicBlock>,
    /// Architecture-specific context
    pub ctx: Context<A>,
}

/// Control flow graph with fully resolved basic block references.
///
/// All control flow targets have been resolved from string labels to basic block IDs,
/// forming a complete graph representation of the program's control flow.
pub struct ControlFlowGraph<A> {
    /// Vector of basic blocks with resolved control flow
    pub blocks: Vec<BasicBlock>,
    /// Architecture-specific context
    pub ctx: Context<A>,
}

/// Structured control flow representation (output of relooper algorithm).
///
/// The relooper algorithm converts an arbitrary control flow graph into this
/// structured representation using only high-level constructs (blocks and conditionals).
#[derive(Debug)]
pub enum Shape {
    /// Sequential block of instructions with optional continuation
    Block {
        /// Instructions to execute in sequence
        instrs: Vec<Instr>,
        /// Next shape to execute after this block
        next: Option<Box<Shape>>,
    },
    /// Conditional branch (if/else)
    If {
        /// Condition to evaluate
        cond: Conditional,
        /// Shape to execute if condition is true
        then_branch: Box<Shape>,
        /// Shape to execute if condition is false (optional)
        else_branch: Option<Box<Shape>>,
        /// Shape to execute after the conditional branches merge
        next: Option<Box<Shape>>,
    },
}

/// Final structured program representation.
///
/// Contains the complete program as a tree of structured control flow shapes,
/// produced by the relooper algorithm from a control flow graph.
pub struct StructuredProgram<A> {
    /// Root of the structured control flow tree
    pub shape: Shape,
    /// Architecture-specific context
    pub ctx: Context<A>,
}

// ——————————————————————————— Relooper Algorithm ——————————————————————————— //

impl<A: Arch> ParsedAssembly<A> {
    /// Convert parsed assembly into basic blocks.
    ///
    /// Splits the instruction stream into basic blocks at control flow boundaries
    /// (labels and control flow instructions). Control flow targets are still
    /// represented as string labels at this stage.
    pub fn into_basic_blocks(self) -> Result<RawBasicBlocks<A>> {
        let mut blocks = Vec::new();
        let mut bb = RawBasicBlock::default();

        for line in self.asm_lines {
            match line {
                AsmLine::Instr(instr) => {
                    if let Some(terminator) = A::as_control_flow(&instr)? {
                        // This is a control flow instruction, terminate the basic block here
                        bb.terminator = terminator;
                        blocks.push(bb);

                        // Create a fresh block
                        let new_bb = RawBasicBlock::default();
                        bb = new_bb;
                    } else {
                        // This is not a control-flow instruction, add it to the current block
                        bb.instrs.push(instr);
                    }
                }
                AsmLine::Label(label) => {
                    // We never allow labels within a basic block, because they can be jump
                    // targets. Therefore, if the current basic block already has instructions we
                    // terminate it.
                    if bb.instrs.is_empty() {
                        bb.labels.push(label);
                    } else {
                        let mut new_bb = RawBasicBlock::default();
                        new_bb.labels.push(label);
                        blocks.push(bb);
                        bb = new_bb;
                    }
                }
            }
        }
        blocks.push(bb);

        Ok(RawBasicBlocks {
            blocks,
            ctx: self.ctx,
        })
    }
}

impl<A: Arch> RawBasicBlocks<A> {
    /// Resolve the control flow targets of the basic blocks.
    ///
    /// Converts string labels to basic block IDs, creating a complete control flow graph
    /// where all control flow edges are explicitly represented.
    pub fn into_cfg(self) -> Result<ControlFlowGraph<A>> {
        let mut blocks = Vec::new();

        for (id, bb) in self.blocks.iter().enumerate() {
            let terminator = resolve_terminator(&bb.terminator, id, &self.blocks)?;

            blocks.push(BasicBlock {
                id: BasicBlockID(id),
                instrs: bb.instrs.clone(),
                terminator,
            });
        }

        Ok(ControlFlowGraph {
            blocks,
            ctx: self.ctx,
        })
    }
}

impl<A: Arch> ControlFlowGraph<A> {
    /// Convert the CFG into structured control flow using the relooper algorithm.
    ///
    /// Transforms an arbitrary control flow graph into a structured representation
    /// using only high-level constructs (blocks, if/else). Currently does not support loops.
    pub fn into_structured(self) -> Result<StructuredProgram<A>> {
        let all_blocks: HashSet<BasicBlockID> = self.blocks.iter().map(|b| b.id).collect();

        let entry = BasicBlockID::new(0);
        let shape = reloop(entry, &all_blocks, &self.blocks)?;

        Ok(StructuredProgram {
            shape,
            ctx: self.ctx,
        })
    }
}

/// Resolve a label-based terminator to a basic block ID-based terminator.
///
/// Looks up string labels in the blocks vector and converts them to basic block IDs.
/// Also handles implicit fallthrough to the next block.
fn resolve_terminator(
    terminator: &LabelTerminator,
    index: usize,
    blocks: &Vec<RawBasicBlock>,
) -> Result<Terminator> {
    match terminator {
        LabelTerminator::Done => {
            if index >= blocks.len() - 1 {
                // This is the last block
                Ok(Terminator::Done)
            } else {
                // Fallthrough to the next block
                Ok(Terminator::Jump(BasicBlockID::new(index + 1)))
            }
        }
        LabelTerminator::Branch { cond, if_true } => match resolve_label(if_true, index, blocks) {
            Some(if_true) => Ok(Terminator::Branch {
                cond: cond.clone(),
                if_true: BasicBlockID(if_true),
                if_false: BasicBlockID(index + 1),
            }),
            None => Err(anyhow!("Could not find label '{}'", if_true)),
        },
        LabelTerminator::Jump(target) => match resolve_label(target, index, blocks) {
            Some(id) => Ok(Terminator::Jump(BasicBlockID::new(id))),
            None => Err(anyhow!("Could not find label '{}'", target)),
        },
    }
}

/// Find the index of a basic block by its label.
///
/// Searches through all blocks to find one with a matching label, returning its index.
fn resolve_label(label: &str, block_index: usize, blocks: &[RawBasicBlock]) -> Option<usize> {
    if let Some(l) = label.strip_suffix('f')
        && l.parse::<usize>().is_ok()
    {
        // Forward numeric label
        resolve_numeric_label_forward(l, block_index, blocks)
    } else if let Some(l) = label.strip_suffix('b')
        && l.parse::<usize>().is_ok()
    {
        // Backward numeric label
        resolve_numeric_label_backward(l, block_index, blocks)
    } else {
        // String label
        resolve_named_label(label, blocks)
    }
}

/// Find the index of a basic block by its string label.
///
/// Searches through all blocks to find one with a matching label, returning its index.
fn resolve_named_label(label: &str, blocks: &[RawBasicBlock]) -> Option<usize> {
    for (id, bb) in blocks.iter().enumerate() {
        if bb.labels.iter().any(|l| l == label) {
            return Some(id);
        }
    }

    None
}

/// Find the index of a basic block by its numeric label, searching forward.
///
/// Searches through blocks after the current block to find one with a matching numeric label.
/// Used for forward references like "1f".
fn resolve_numeric_label_forward(
    label: &str,
    block_index: usize,
    blocks: &[RawBasicBlock],
) -> Option<usize> {
    for (id, bb) in blocks.iter().enumerate().skip(block_index + 1) {
        if bb.labels.iter().any(|l| l == label) {
            return Some(id);
        }
    }

    None
}

/// Find the index of a basic block by its numeric label, searching backward.
///
/// Searches through blocks before the current block to find one with a matching numeric label.
/// Used for backward references like "1b".
fn resolve_numeric_label_backward(
    label: &str,
    block_index: usize,
    blocks: &[RawBasicBlock],
) -> Option<usize> {
    for (id, bb) in blocks.iter().enumerate().take(block_index) {
        if bb.labels.iter().any(|l| l == label) {
            return Some(id);
        }
    }

    None
}

// ———————————————————————— Structured Control Flow ————————————————————————— //

use std::collections::{HashSet, VecDeque};

/// Find all blocks reachable from a starting block within the unprocessed set.
///
/// Uses breadth-first search to find all blocks that can be reached from the start block,
/// considering only blocks in the unprocessed set (blocks already processed are ignored).
fn find_reachable(
    start: BasicBlockID,
    unprocessed: &HashSet<BasicBlockID>,
    cfg: &[BasicBlock],
) -> HashSet<BasicBlockID> {
    let mut reachable = HashSet::new();
    let mut queue = VecDeque::new();
    queue.push_back(start);

    while let Some(current) = queue.pop_front() {
        if unprocessed.contains(&current) && !reachable.contains(&current) {
            reachable.insert(current);

            // Get successors from the terminator
            let block = &cfg[current.0];
            match &block.terminator {
                Terminator::Done => {}
                Terminator::Jump(target) => {
                    queue.push_back(*target);
                }
                Terminator::Branch {
                    if_true, if_false, ..
                } => {
                    queue.push_back(*if_true);
                    queue.push_back(*if_false);
                }
            }
        }
    }

    reachable
}

/// Find the merge point where branches rejoin.
///
/// Returns the block where control flow from different branches merges back together.
/// For a simplified implementation, returns the block with the smallest ID in the remaining set.
fn find_merge_point(
    remaining: &HashSet<BasicBlockID>,
    _cfg: &[BasicBlock],
) -> Option<BasicBlockID> {
    if remaining.is_empty() {
        return None;
    }

    // For a simplified implementation, we return the block with the smallest ID
    // This works for structured control flow where blocks are ordered sequentially
    remaining.iter().min_by_key(|id| id.0).copied()
}

/// Detect the control flow shape starting from the entry block
///
//  TODO: To support loops, add backedge detection here before checking terminators:
//  1. Check if any block in `unprocessed` can reach back to `entry` (using `can_reach()`)
//  2. If yes, collect all loop blocks with `find_blocks_that_loop_to()`
//  3. Return a `Shape::Loop` variant with the loop body and continuation
fn detect_shape(
    entry: BasicBlockID,
    unprocessed: &HashSet<BasicBlockID>,
    cfg: &[BasicBlock],
) -> Result<Shape> {
    // TODO: Loop detection goes here
    // if !find_blocks_that_loop_to(entry, unprocessed, cfg).is_empty() {
    //     return Shape::Loop { ... }
    // }

    let block = &cfg[entry.0];

    match &block.terminator {
        Terminator::Done => {
            // Terminal block - no continuation
            Ok(Shape::Block {
                instrs: block.instrs.clone(),
                next: None,
            })
        }

        Terminator::Jump(target) => {
            // Simple linear flow
            let mut remaining = unprocessed.clone();
            remaining.remove(&entry);

            let next = if remaining.contains(target) {
                Some(Box::new(reloop(*target, &remaining, cfg)?))
            } else {
                None
            };

            Ok(Shape::Block {
                instrs: block.instrs.clone(),
                next,
            })
        }

        Terminator::Branch {
            cond,
            if_true,
            if_false,
        } => {
            // Branching control flow (if/else)
            let mut remaining = unprocessed.clone();
            remaining.remove(&entry);

            // Find blocks reachable from each branch
            let true_reachable = find_reachable(*if_true, &remaining, cfg);
            let false_reachable = find_reachable(*if_false, &remaining, cfg);

            // Process true branch
            let then_branch = Box::new(reloop(*if_true, &true_reachable, cfg)?);

            // Remove true branch blocks from remaining
            for block_id in &true_reachable {
                remaining.remove(block_id);
            }

            // Process false branch
            let else_branch = if remaining.contains(if_false) {
                let else_shape = reloop(*if_false, &false_reachable, cfg)?;

                // Remove false branch blocks from remaining
                for block_id in &false_reachable {
                    remaining.remove(block_id);
                }

                Some(Box::new(else_shape))
            } else {
                None
            };

            // Find merge point
            let next = if let Some(merge_id) = find_merge_point(&remaining, cfg) {
                Some(Box::new(reloop(merge_id, &remaining, cfg)?))
            } else {
                None
            };

            Ok(Shape::If {
                cond: cond.clone(),
                then_branch,
                else_branch,
                next,
            })
        }
    }
}

/// Main relooper algorithm - recursively converts CFG to structured control flow.
///
/// Takes an entry block and a set of unprocessed blocks, and recursively builds
/// a structured control flow tree by detecting patterns (blocks, conditionals, loops).
fn reloop(
    entry: BasicBlockID,
    unprocessed: &HashSet<BasicBlockID>,
    cfg: &[BasicBlock],
) -> Result<Shape> {
    if unprocessed.is_empty() {
        return Err(anyhow!("Cannot reloop empty block set"));
    }

    detect_shape(entry, unprocessed, cfg)
}
