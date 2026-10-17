import Goose.Lower.Validation.PermissionPreservationSource
import Goose.Lower.Validation.ExpressionTypingSourceContents

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem source_ownerMutation_contents {env : Core.TEnv} {info : PlaceInfo} {element : Ty}
    (resolved : Core.checkResolvedType env.mod info.ty = .ok ())
    (owner : info.ty.ownerElem? = some element)
    (allowed : info.ownerMutationWritable env.mod.profile = true) :
    info.contentsWritable = true ∧ ContentsTarget info.ty := by
  rcases info with ⟨type, binding, contents⟩
  cases type <;> simp only [Ty.ownerElem?] at owner
  all_goals try cases owner
  all_goals
    cases profile : env.mod.profile
    all_goals first
      | exact ⟨by simpa [PlaceInfo.ownerMutationWritable, profile] using allowed, trivial⟩
      | simp [Core.checkResolvedType, profile, Core.reject, bind, Except.bind] at resolved

theorem source_push_contents {env : Core.TEnv} {place : Place} {value : Expr}
    {origin : Option OriginId} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.push place value origin) start = .ok (type, finish)) :
    ∃ info ownerStart ownerFinish, Core.tyPlace env place ownerStart = .ok (info, ownerFinish) ∧
      info.contentsWritable = true ∧ ContentsTarget info.ty := by
  have solve : ∀ ownerStart, (do
      let info ← Core.tyPlace env place
      let element ← Core.ownerElement env info.ty
      let argTy ← Core.tyExpr env value
      unless argTy == element do Core.rej .type "a pushed element of another type than the array's"
      Core.requireWrite "push" (info.ownerMutationWritable env.mod.profile)
      pure (Ty.ref .mutable element)) ownerStart = .ok (type, finish) →
      ∃ info ownerStart ownerFinish, Core.tyPlace env place ownerStart = .ok (info, ownerFinish) ∧
        info.contentsWritable = true ∧ ContentsTarget info.ty := by
    intro ownerStart lowered
    obtain ⟨info, ownerFinish, placeSource, lowered⟩ := (st_bind_ok _ _ _ _).mp lowered
    obtain ⟨element, _, elementSource, lowered⟩ := (st_bind_ok _ _ _ _).mp lowered
    have owner := ownerElement_ok _ _ _ _ _ elementSource
    obtain ⟨argTy, _, _, lowered⟩ := (st_bind_ok _ _ _ _).mp lowered
    by_cases equal : (argTy == element) = true
    · simp only [equal, ite_true] at lowered
      obtain ⟨_, _, required, _⟩ := (st_bind_ok _ _ _ _).mp lowered
      have allowed : info.ownerMutationWritable env.mod.profile = true := by
        apply Classical.byContradiction
        intro denied
        have rejected := Bool.eq_false_iff.mpr denied
        simp [Core.requireWrite, rejected, rej_ok] at required
      exact ⟨info, ownerStart, ownerFinish, placeSource,
        source_ownerMutation_contents owner.1 owner.2.1 allowed⟩
    · simp only [equal] at lowered
      obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp lowered
      exact (rej_ok _ _ _ _).mp rejected |>.elim
  unfold Core.tyExpr at source
  cases profile : env.mod.profile <;> cases origin with
  | none =>
    simp only [profile] at source solve
    first
    | exact solve start source
    | (obtain ⟨_, _, rejected, _⟩ := (st_bind_ok _ _ _ _).mp source
       exact (rej_ok _ _ _ _).mp rejected |>.elim)
  | some origin =>
    simp only [profile] at source solve
    obtain ⟨_, ownerStart, initial, source⟩ := (st_bind_ok _ _ _ _).mp source
    first
    | exact solve ownerStart source
    | exact (rej_ok _ _ _ _).mp initial |>.elim

theorem source_pop_contents {env : Core.TEnv} {place : Place} {origin : OriginId}
    {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.pop place origin) start = .ok (type, finish)) :
    ∃ info ownerStart ownerFinish, Core.tyPlace env place ownerStart = .ok (info, ownerFinish) ∧
      info.contentsWritable = true ∧ ContentsTarget info.ty := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, ownerStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨info, ownerFinish, ownerSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨element, _, elementSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  have owner := ownerElement_ok _ _ _ _ _ elementSource
  obtain ⟨_, _, required, _⟩ := (st_bind_ok _ _ _ _).mp source
  have allowed : info.contentsWritable = true := by
    apply Classical.byContradiction
    intro denied
    have rejected := Bool.eq_false_iff.mpr denied
    simp [Core.requireWrite, rejected, rej_ok] at required
  have container : ContentsTarget info.ty := by
    have shape := owner.2.1
    cases typeShape : info.ty <;> simp [Ty.ownerElem?, typeShape, ContentsTarget] at shape ⊢
  exact ⟨info, ownerStart, ownerFinish, ownerSource, allowed, container⟩

#print axioms source_pop_contents

#print axioms source_push_contents

#print axioms source_ownerMutation_contents

end Goose.Lower.Validation
