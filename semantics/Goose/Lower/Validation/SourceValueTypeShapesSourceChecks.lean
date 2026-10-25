import Goose.Lower.Validation.SourceValueTypeShapesSyntax
import Goose.Lower.Validation.ExpressionTypingAggregateOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem shape_tyExpr_arrLit_storable {env : Core.TEnv} {annotation type : Ty} {exprs : List Expr}
    {start finish : Nat}
    (checked : Core.tyExpr env (.arrLit annotation exprs) start = .ok (type, finish)) :
    annotation.storable = true := by
  simp only [Core.tyExpr] at checked
  obtain ⟨_, _, _, checked⟩ := (st_bind_ok _ _ _ _).mp checked
  cases annotation with
  | arr element count | grow element | growshrink element | limited element count =>
    by_cases flat : element.flat = true
    · exact flat
    · simp [flat, chk] at checked
  | _ => simp [chk] at checked

theorem shape_tyExpr_fill_storable {env : Core.TEnv} {annotation type : Ty} {expr : Expr}
    {start finish : Nat}
    (checked : Core.tyExpr env (.fill annotation expr) start = .ok (type, finish)) :
    annotation.storable = true := by
  simp only [Core.tyExpr] at checked
  obtain ⟨_, _, _, checked⟩ := (st_bind_ok _ _ _ _).mp checked
  cases annotation with
  | arr element count =>
    by_cases flat : element.flat = true
    · exact flat
    · simp [flat, chk] at checked
  | _ => simp [chk] at checked

theorem shape_tyExpr_structLit_storable {env : Core.TEnv} {annotation type : Ty} {exprs : List Expr}
    {start finish : Nat}
    (checked : Core.tyExpr env (.structLit annotation exprs) start = .ok (type, finish)) :
    annotation.storable = true := by
  obtain ⟨_, descriptor, _, _, _, definition, _⟩ := tyExpr_structLiteral_children checked
  obtain ⟨id, fields, rfl, flat, _, _, _⟩ := structDef_ok _ _ _ _ _ definition
  exact flat

end Goose.Lower.Validation
