import Goose.Lower.DemandIntegerAssignmentStopped
import Goose.Lower.DemandControlStatementAgreement
import Goose.Lower.Validation.ExpressionTypingScalarOps

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive IntegerControlExpression : Expr → Prop
  | literal (type : IntTy) (number : Int) : IntegerControlExpression (.lit type number)
  | unary (operation : UnOp) {child : Expr} (origin : OriginId) (form : ControlPrefixExpression child) :
      IntegerControlExpression (.un operation child origin)
  | binary (operation : BinOp) {left right : Expr} (origin : OriginId)
      (first : ControlPrefixExpression left) (second : ControlPrefixExpression right) :
      IntegerControlExpression (.bin operation left right origin)
  | convert (kind : ConvKind) (target : IntTy) {child : Expr} (origin : OriginId) (form : ControlPrefixExpression child) :
      IntegerControlExpression (.conv kind (.int target) child origin)

theorem IntegerControlExpression.control {expression : Expr} (form : IntegerControlExpression expression) :
    ControlPrefixExpression expression := by
  cases form with
  | literal type number => exact .scalar (.literal type number)
  | unary operation origin form => exact .unary operation origin form
  | binary operation origin first second => exact .binary operation origin first second
  | convert kind target origin form => exact .convert kind target origin form

theorem IntegerControlExpression.integer {expression : Expr} (form : IntegerControlExpression expression)
    {cfg : Cfg} {env : Env} {state : St} (source : ExprSource cfg env expression state) :
    ∃ type, source.ty = .int type := by
  cases form with
  | literal type number =>
    have typed := source.typed
    simp only [tyExpr] at typed
    split at typed
    · exact ⟨type, (congrArg Prod.fst (Except.ok.inj typed)).symm⟩
    · cases typed
  | unary operation origin form =>
    obtain ⟨_, _, type, _, shape, _⟩ := Validation.tyExpr_un_child source.typed
    exact ⟨type, shape⟩
  | binary operation origin first second =>
    obtain ⟨_, _, _, _, type, _, _, shape⟩ := Validation.tyExpr_bin_children source.typed
    exact ⟨type, shape⟩
  | convert kind target origin form =>
    obtain ⟨_, type, _, _, _, _, shape, _⟩ := Validation.tyExpr_conversion_child source.typed
    exact ⟨type, shape⟩

#print axioms IntegerControlExpression.integer

end Goose.Lower
