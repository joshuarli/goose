import Goose.Lower.Validation.ExpressionTypingSliceOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

def MutableReferenceExpression : Expr → Prop
  | .read .. | .ref .. | .call .. | .push .. | .pop .. | .ifE .. | .blockE .. => True
  | _ => False

theorem tyExpr_mutable_reference_form {env : Core.TEnv} {expr : Expr} {target : Ty} {start finish : Nat}
    (source : Core.tyExpr env expr start = .ok (.ref .mutable target, finish)) :
    MutableReferenceExpression expr := by
  cases expr with
  | read _ | ref _ _ | call _ _ _ | push _ _ _ | pop _ _ | ifE _ _ _ | blockE _ => trivial
  | lit integer number =>
    by_cases range : integer.inRange number
    · simp only [Core.tyExpr, range, ite_true] at source
      have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
      cases shape
    · simp [Core.tyExpr, range, rej_ok] at source
  | bool value =>
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    cases shape
  | slice mu view lo hi origin =>
    obtain ⟨_, _, _, _, _, _, _, _, _, shape⟩ := tyExpr_slice_children source
    cases shape
  | len view =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    cases shape
  | un op child origin =>
    obtain ⟨_, _, _, _, shape, _⟩ := tyExpr_un_child source
    cases shape
  | bin op left right origin =>
    obtain ⟨_, _, _, _, _, _, _, shape⟩ := tyExpr_bin_children source
    cases shape
  | cmp op left right =>
    obtain ⟨_, _, _, _, _, _, shape, _⟩ := tyExpr_comparison_children source
    cases shape
  | and left right | or left right =>
    simp only [Core.tyExpr] at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    have shape := congrArg Prod.fst ((st_pure_ok _ _ _).mp source)
    cases shape
  | not child =>
    obtain ⟨_, _, shape⟩ := tyExpr_not_child source
    cases shape
  | conv kind ty child origin =>
    obtain ⟨_, _, _, _, _, _, shape, _⟩ := tyExpr_conversion_child source
    cases shape
  | arrLit arrayTy children =>
    obtain ⟨shape, _, _, _, element, _, _⟩ := tyExpr_arrayLiteral_children source
    rw [← shape] at element
    cases element
  | fill arrayTy child =>
    obtain ⟨shape, _, _, _, _, arrayShape, _⟩ := tyExpr_fill_child source
    cases shape.trans arrayShape
  | structLit structTy children =>
    obtain ⟨shape, _, _, _, _, definition, _⟩ := tyExpr_structLiteral_children source
    obtain ⟨_, _, nominal, _, _, _, _⟩ := structDef_ok _ _ _ _ _ definition
    cases shape.trans nominal

#print axioms tyExpr_mutable_reference_form

end Goose.Lower.Validation
