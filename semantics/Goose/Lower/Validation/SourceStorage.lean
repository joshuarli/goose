import Goose.Lower.Validation.StorageRules
import Goose.Core.Sound.Check

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem tyExpr_read_storage {env : TEnv} {place : Place} {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.read place) start = .ok (ty, finish)) :
    ∃ info next, Core.tyPlace env place start = .ok (info, next) ∧ ty = info.ty ∧ info.ty.readable = true := by
  simp only [Core.tyExpr] at source
  obtain ⟨info, next, checked, source⟩ := (st_bind_ok _ _ _ _).mp source
  by_cases readable : info.ty.readable = true
  · simp only [readable, ite_true] at source
    have pair := (st_pure_ok _ _ _).mp source
    exact ⟨info, next, checked, congrArg Prod.fst pair, readable⟩
  · simp [readable, chk] at source

theorem flat_or_slice_readable {ty : Ty} (copyable : ty.flat = true ∨ ty.isSlice = true) :
    ty.readable = true := by
  cases ty <;> simp_all [Ty.flat, Ty.isSlice, Ty.readable]

theorem tyStmt_assign_storage {env output : TEnv} {place : Place} {expr : Expr}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assign place expr origin) start = .ok (output, finish)) :
    ∃ info next, Core.tyPlace env place start = .ok (info, next) ∧
      info.bindingWritable = true ∧ info.ty.readable = true := by
  simp only [Core.tyStmt] at source
  obtain ⟨_, next, originChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  have same : next = start := congrArg Prod.snd ((checkOrg_ok _ _ _ _).mp originChecked).2
  subst next
  obtain ⟨info, next, placeChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  refine ⟨info, next, placeChecked, ?_, ?_⟩
  all_goals
    try inv at source
    repeat' first
      | (guard_hyp source : _ ∧ _; obtain ⟨fact, source⟩ := source)
      | (guard_hyp source : ∃ _, _; obtain ⟨value, source⟩ := source)
      | assumption
  · apply flat_or_slice_readable
    rcases (show info.ty.flat = true ∨ info.ty.isSlice = true ∧ place.derefVar?.isSome = true from by simpa only [Bool.or_eq_true, Bool.and_eq_true] using (show (info.ty.flat || info.ty.isSlice && place.derefVar?.isSome) = true from by assumption)) with flat | ⟨slice, _⟩
    · exact Or.inl flat
    · exact Or.inr slice

theorem tyStmt_assignOp_storage {env output : TEnv} {place : Place} {expr : Expr}
    {operation : BinOp} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assignOp operation place expr origin) start = .ok (output, finish)) :
    ∃ info next, Core.tyPlace env place start = .ok (info, next) ∧
      info.bindingWritable = true ∧ info.ty.readable = true := by
  simp only [Core.tyStmt] at source
  obtain ⟨_, next, originChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  have same : next = start := congrArg Prod.snd ((checkOrg_ok _ _ _ _).mp originChecked).2
  subst next
  obtain ⟨info, next, placeChecked, source⟩ := (st_bind_ok _ _ _ _).mp source
  refine ⟨info, next, placeChecked, ?_, ?_⟩
  all_goals
    try inv at source
    repeat' first
      | (guard_hyp source : _ ∧ _; obtain ⟨fact, source⟩ := source)
      | (guard_hyp source : ∃ _, _; obtain ⟨value, source⟩ := source)
      | assumption
      | (solve | simp_all [Ty.readable, Ty.flat])

theorem passableTo_readable {source target : Ty} (passable : source.passableTo target = true)
    (readable : source.readable = true) : target.readable = true := by
  cases source <;> cases target <;> simp_all [Ty.passableTo, Ty.readable]

theorem passableTo_source_refLike {source target : Ty}
    (passable : source.passableTo target = true) (reference : target.isRefLike = true) :
    source.isRefLike = true := by
  cases source <;> cases target <;> simp_all [Ty.passableTo, Ty.isRefLike]

theorem passableTo_noRefSlice {source target : Ty} (passable : source.passableTo target = true)
    (ordinary : source.isRefSlice = false) : target.isRefSlice = false := by
  cases source <;> cases target <;> simp_all [Ty.passableTo, Ty.isRefSlice]
  case ref.ref sourceMu sourceTy targetMu targetTy =>
    cases targetTy <;> simp_all [Ty.isRefSlice]

end Goose.Lower.Validation
