import Goose.Lower.Validation.SummaryPreservationRefinedEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpExpr_un_after_operand {env : PEnv} {op : UnOp} {operand : Expr} {origin : OriginId}
    {initial before : RState} {operandRoots : List RootRef}
    (operandSource : rpExpr env operand initial = .ok (operandRoots, before)) :
    rpExpr env (.un op operand origin) initial =
      .ok ([], { before with eff := match op with | .neg => { before.eff with aborts := true } | .bitnot => before.eff }) := by
  cases op <;> simp [rpExpr, operandSource, bind, pure, noteAborts, modify, Except.bind, Except.pure, StateT.modifyGet, StateT.bind, StateT.pure, modifyGet, MonadStateOf.modifyGet] <;> rfl


theorem rpExpr_bin_after_operands {env : PEnv} {op : BinOp} {left right : Expr} {origin : OriginId}
    {initial middle before : RState} {leftRoots rightRoots : List RootRef}
    (leftSource : rpExpr env left initial = .ok (leftRoots, middle))
    (rightSource : rpExpr env right middle = .ok (rightRoots, before)) :
    rpExpr env (.bin op left right origin) initial =
      .ok ([], { before with eff := if op.mayAbort then { before.eff with aborts := true } else before.eff }) := by
  cases aborts : op.mayAbort <;>
    simp [rpExpr, leftSource, rightSource, aborts, bind, pure, noteAborts, modify,
      Except.bind, Except.pure, StateT.modifyGet, StateT.bind, StateT.pure, modifyGet, MonadStateOf.modifyGet] <;> rfl


theorem rpExpr_cmp_after_operands {env : PEnv} {op : CmpOp} {left right : Expr}
    {initial middle before : RState} {leftRoots rightRoots : List RootRef}
    (leftSource : rpExpr env left initial = .ok (leftRoots, middle))
    (rightSource : rpExpr env right middle = .ok (rightRoots, before)) :
    rpExpr env (.cmp op left right) initial = .ok ([], before) := by
  simp [rpExpr, leftSource, rightSource, bind, pure, Except.bind, Except.pure, StateT.modifyGet, StateT.bind, StateT.pure] <;> rfl

end Goose.Lower.Validation.SummaryPreservation
