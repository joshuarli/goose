import Goose.Lower.Validation.ReplacementScopedOperandsSource
import Goose.Lower.Validation.OperandSource

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lowerExpr_emitsFreshUses (expr : Expr) {env before value captured}
    (run : lowerExpr expr env before = (value, captured)) :
    EmitsOnly (RhsUsesFresh before.vals.size) before captured := by
  have emitted := rhsOperands_lowerExpr before.vals.size expr env before (Nat.le_refl _)
  change EmitsOnly (RhsUsesFresh before.vals.size) before (lowerExpr expr env before).2 at emitted
  simpa only [run] using emitted

theorem lowerPlace_emitsFreshUses (place : Place) {env before value captured}
    (run : lowerPlace place env before = (value, captured)) :
    EmitsOnly (RhsUsesFresh before.vals.size) before captured := by
  have emitted := rhsOperands_lowerPlace before.vals.size place env before (Nat.le_refl _)
  change EmitsOnly (RhsUsesFresh before.vals.size) before (lowerPlace place env before).2 at emitted
  simpa only [run] using emitted

theorem lowerView_emitsFreshUses (view : View) {env before value captured}
    (run : lowerView view env before = (value, captured)) :
    EmitsOnly (RhsUsesFresh before.vals.size) before captured := by
  have emitted := rhsOperands_lowerView before.vals.size view env before (Nat.le_refl _)
  change EmitsOnly (RhsUsesFresh before.vals.size) before (lowerView view env before).2 at emitted
  simpa only [run] using emitted

theorem lowerExpr_scoped_definition_operands (expr : Expr) {env before value captured finalState}
    (run : lowerExpr expr env before = (value, captured))
    (initialDense : before.DenseDefinitions) (initialLive : LiveBound before)
    (initialOperands : OperandBounds before) (finalDense : finalState.DenseDefinitions)
    (extension : captured.Ext finalState) {func : Func} (blocks : func.blocks = finishBlocks finalState.blocks)
    {block : GIR.Block} {result : ValueId} {op : Op}
    (member : block ∈ func.blocks.toList) (defined : Inst.def result op ∈ block.insts)
    (lower : before.vals.size ≤ result) (upper : result < captured.vals.size) :
    ∀ source ∈ (Inst.def result op).uses, before.vals.size ≤ source ∧ source < captured.vals.size := by
  have emitted := lowerExpr_emitsFreshUses expr run
  have capturedDense := (dense_lowerExpr expr env before value captured run initialDense initialLive).1
  have capturedOperands := operands_source_lowerExpr expr env before value captured run initialOperands
  exact scoped_definition_operand_bounds initialDense capturedDense finalDense emitted.extension extension
    blocks emitted capturedOperands member defined lower upper

theorem lowerExpr_scoped_incoming_operands (expr : Expr) {env before value captured finalState}
    (run : lowerExpr expr env before = (value, captured))
    (initialDense : before.DenseDefinitions) (initialLive : LiveBound before)
    (initialOperands : OperandBounds before) (initialTargets : TargetsBounded before)
    (finalDense : finalState.DenseDefinitions) (extension : captured.Ext finalState)
    (framed : IntervalEdgesFramed before captured finalState)
    {func : Func} (blocks : func.blocks = finishBlocks finalState.blocks)
    {parameterBlock sourceBlock : GIR.Block} {target parameterIndex parameter : Nat} {type : VTy} {term : Term}
    (targetAt : func.blocks[target]? = some parameterBlock)
    (parameterAt : parameterBlock.params[parameterIndex]? = some (parameter, type))
    (lower : before.vals.size ≤ parameter) (upper : parameter < captured.vals.size)
    (sourceMember : sourceBlock ∈ func.blocks.toList) (termMember : Inst.term term ∈ sourceBlock.insts)
    (successor : target ∈ term.successors) :
    ∀ source ∈ term.uses, before.vals.size ≤ source ∧ source < captured.vals.size := by
  have emitted := lowerExpr_emitsFreshUses expr run
  have capturedDense := (dense_lowerExpr expr env before value captured run initialDense initialLive).1
  have capturedOperands := operands_source_lowerExpr expr env before value captured run initialOperands
  exact scoped_incoming_operand_bounds initialDense capturedDense finalDense emitted.extension extension
    blocks emitted capturedOperands initialTargets framed targetAt parameterAt lower upper sourceMember termMember successor

end Goose.Lower.Validation
