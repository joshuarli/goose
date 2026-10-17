import Goose.Lower.Validation.EmittedMetadataStaticState

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem static_requireShrink {env : Core.TEnv} {start finish : Nat}
    (checked : Core.requireShrink env start = .ok ((), finish)) : env.mod.profile = .shrink := by
  by_cases profile : env.mod.profile = .shrink
  · exact profile
  · simp [Core.requireShrink, profile, chk] at checked

theorem static_checkType {env : Core.TEnv} {type : Ty} {start finish : Nat}
    (checked : Core.checkType env type start = .ok ((), finish)) :
    Core.checkResolvedType env.mod type = .ok () := by
  unfold Core.checkType at checked
  obtain ⟨unit, resolved, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
  cases unit
  exact resolved

theorem static_tyExpr_pop_profile {env : Core.TEnv} {owner : Place} {origin : OriginId}
    {type : Ty} {start finish : Nat}
    (checked : Core.tyExpr env (.pop owner origin) start = .ok (type, finish)) :
    env.mod.profile = .shrink := by
  simp only [Core.tyExpr] at checked
  obtain ⟨unit, _, profile, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp checked
  cases unit
  exact static_requireShrink profile

theorem static_tyStmt_popN_profile {env output : Core.TEnv} {scope start finish : Nat}
    {owner : Place} {count : Expr} {origin : OriginId} :
    Core.tyStmt env scope (.popN owner count origin) start = .ok (output, finish) → env.mod.profile = .shrink := by
  intro checked
  change (Core.requireShrink env >>= _) start = .ok (output, finish) at checked
  obtain ⟨unit, _, profile, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp checked
  cases unit
  exact static_requireShrink profile

theorem static_tyStmt_resize_profile {env output : Core.TEnv} {scope start finish : Nat}
    {owner : Place} {size : Expr} {fill : Option Expr} {origin : OriginId} :
    Core.tyStmt env scope (.resize owner size fill origin) start = .ok (output, finish) → env.mod.profile = .shrink := by
  cases fill
  all_goals
    intro checked
    change (Core.requireShrink env >>= _) start = .ok (output, finish) at checked
    obtain ⟨unit, _, profile, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp checked
    cases unit
    exact static_requireShrink profile

theorem static_tyStmt_clear_profile {env output : Core.TEnv} {scope start finish : Nat}
    {owner : Place} {origin : OriginId} :
    Core.tyStmt env scope (.clear owner origin) start = .ok (output, finish) → env.mod.profile = .shrink := by
  intro checked
  change (Core.requireShrink env >>= _) start = .ok (output, finish) at checked
  obtain ⟨unit, _, profile, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp checked
  cases unit
  exact static_requireShrink profile

theorem static_tyStmt_assignWhole_profile {env output : Core.TEnv} {scope start finish : Nat}
    {owner : Place} {replacement : Expr} {origin : OriginId} :
    Core.tyStmt env scope (.assignWhole owner replacement origin) start = .ok (output, finish) → env.mod.profile = .shrink := by
  intro checked
  change (Core.requireShrink env >>= _) start = .ok (output, finish) at checked
  obtain ⟨unit, _, profile, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp checked
  cases unit
  exact static_requireShrink profile

theorem static_tyExpr_arrLit_resolved {env : Core.TEnv} {annotation type : Ty} {exprs : List Expr}
    {start finish : Nat}
    (checked : Core.tyExpr env (.arrLit annotation exprs) start = .ok (type, finish)) :
    Core.checkResolvedType env.mod annotation = .ok () := by
  simp only [Core.tyExpr] at checked
  obtain ⟨unit, _, resolved, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp checked
  cases unit
  exact static_checkType resolved

theorem static_tyExpr_fill_resolved {env : Core.TEnv} {annotation type : Ty} {expr : Expr}
    {start finish : Nat}
    (checked : Core.tyExpr env (.fill annotation expr) start = .ok (type, finish)) :
    Core.checkResolvedType env.mod annotation = .ok () := by
  simp only [Core.tyExpr] at checked
  obtain ⟨unit, _, resolved, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp checked
  cases unit
  exact static_checkType resolved

theorem static_structDef_profile {env : Core.TEnv} {type : Ty} {descriptor : StructDef}
    {start finish : Nat}
    (checked : Core.structDef env type start = .ok (descriptor, finish)) : env.mod.profile = .shrink := by
  by_cases profile : env.mod.profile = .shrink
  · exact profile
  · simp [Core.structDef, profile, chk] at checked

theorem static_tyPlace_field_profile {env : Core.TEnv} {owner : Place} {index : Nat}
    {info : PlaceInfo} {start finish : Nat}
    (checked : Core.tyPlace env (.field owner index) start = .ok (info, finish)) :
    env.mod.profile = .shrink := by
  simp only [Core.tyPlace] at checked
  obtain ⟨_, _, _, checked⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp checked
  obtain ⟨_, _, field, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp checked
  simp only [Core.structField] at field
  obtain ⟨_, _, descriptor, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp field
  exact static_structDef_profile descriptor

end Goose.Lower.Validation
