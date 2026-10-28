import Goose.Lower.DemandScalarAssignmentStopped
import Goose.Lower.DemandControlStatementAgreement
import Goose.Lower.Validation.ExpressionTypingScalarOps

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

inductive ScalarControlExpression : Expr → Prop
  | literal (type : IntTy) (number : Int) : ScalarControlExpression (.lit type number)
  | boolean (value : Bool) : ScalarControlExpression (.bool value)
  | not {child : Expr} (form : ControlPrefixExpression child) : ScalarControlExpression (.not child)
  | and {left right : Expr} (first : ControlPrefixExpression left) (second : ControlPrefixExpression right) :
      ScalarControlExpression (.and left right)
  | or {left right : Expr} (first : ControlPrefixExpression left) (second : ControlPrefixExpression right) :
      ScalarControlExpression (.or left right)
  | compare (operation : CmpOp) {left right : Expr}
      (first : ControlPrefixExpression left) (second : ControlPrefixExpression right) :
      ScalarControlExpression (.cmp operation left right)
  | unary (operation : UnOp) {child : Expr} (origin : OriginId) (form : ControlPrefixExpression child) :
      ScalarControlExpression (.un operation child origin)
  | binary (operation : BinOp) {left right : Expr} (origin : OriginId)
      (first : ControlPrefixExpression left) (second : ControlPrefixExpression right) :
      ScalarControlExpression (.bin operation left right origin)
  | convert (kind : ConvKind) (target : IntTy) {child : Expr} (origin : OriginId) (form : ControlPrefixExpression child) :
      ScalarControlExpression (.conv kind (.int target) child origin)

theorem ScalarControlExpression.control {expression : Expr} (form : ScalarControlExpression expression) :
    ControlPrefixExpression expression := by
  cases form with
  | literal type number => exact .scalar (.literal type number)
  | boolean value => exact .scalar (.boolean value)
  | not form => exact .not form
  | and first second => exact .and first second
  | or first second => exact .or first second
  | compare operation first second => exact .compare operation first second
  | unary operation origin form => exact .unary operation origin form
  | binary operation origin first second => exact .binary operation origin first second
  | convert kind target origin form => exact .convert kind target origin form

theorem ScalarControlExpression.scalar {expression : Expr} (form : ScalarControlExpression expression)
    {cfg : Cfg} {env : Env} {state : St} (source : ExprSource cfg env expression state) :
    source.ty = .bool ∨ ∃ type, source.ty = .int type := by
  cases form with
  | literal type number =>
    have typed := source.typed
    simp only [tyExpr] at typed
    split at typed
    · exact Or.inr ⟨type, (congrArg Prod.fst (Except.ok.inj typed)).symm⟩
    · cases typed
  | boolean value =>
    have typed := source.typed
    simp only [tyExpr, st_pure_ok] at typed
    exact Or.inl (congrArg Prod.fst typed)
  | not form =>
    obtain ⟨_, _, shape⟩ := Validation.tyExpr_not_child source.typed
    exact Or.inl shape
  | and first second =>
    have typed := source.typed
    simp only [tyExpr] at typed
    obtain ⟨_, _, _, typed⟩ := (st_bind_ok _ _ _ _).mp typed
    obtain ⟨_, _, _, typed⟩ := (st_bind_ok _ _ _ _).mp typed
    obtain ⟨_, _, _, typed⟩ := (st_bind_ok _ _ _ _).mp typed
    obtain ⟨_, _, _, typed⟩ := (st_bind_ok _ _ _ _).mp typed
    exact Or.inl (congrArg Prod.fst ((st_pure_ok _ _ _).mp typed))
  | or first second =>
    have typed := source.typed
    simp only [tyExpr] at typed
    obtain ⟨_, _, _, typed⟩ := (st_bind_ok _ _ _ _).mp typed
    obtain ⟨_, _, _, typed⟩ := (st_bind_ok _ _ _ _).mp typed
    obtain ⟨_, _, _, typed⟩ := (st_bind_ok _ _ _ _).mp typed
    obtain ⟨_, _, _, typed⟩ := (st_bind_ok _ _ _ _).mp typed
    exact Or.inl (congrArg Prod.fst ((st_pure_ok _ _ _).mp typed))
  | compare operation first second =>
    have typed := source.typed
    simp only [tyExpr] at typed
    obtain ⟨leftType, _, _, typed⟩ := (st_bind_ok _ _ _ _).mp typed
    obtain ⟨rightType, _, _, typed⟩ := (st_bind_ok _ _ _ _).mp typed
    split at typed
    · split at typed
      · exact Or.inl (congrArg Prod.fst ((st_pure_ok _ _ _).mp typed))
      · obtain ⟨_, _, impossible, _⟩ := (st_bind_ok _ _ _ _).mp typed
        exact ((rej_ok _ _ _ _).mp impossible).elim
    · cases operation <;> simp_all [st_pure_ok, rej_ok]
    · exact ((rej_ok _ _ _ _).mp typed).elim
  | unary operation origin form =>
    obtain ⟨_, _, type, _, shape, _⟩ := Validation.tyExpr_un_child source.typed
    exact Or.inr ⟨type, shape⟩
  | binary operation origin first second =>
    obtain ⟨_, _, _, _, type, _, _, shape⟩ := Validation.tyExpr_bin_children source.typed
    exact Or.inr ⟨type, shape⟩
  | convert kind target origin form =>
    obtain ⟨_, type, _, _, _, _, shape, _⟩ := Validation.tyExpr_conversion_child source.typed
    exact Or.inr ⟨type, shape⟩

#print axioms ScalarControlExpression.scalar

end Goose.Lower
