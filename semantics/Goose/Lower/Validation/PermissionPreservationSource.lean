import Goose.Lower.Validation.PermissionPreservation
import Goose.Core.Sound.Check

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem mapped_rejection (function : α → β) (rule : Rule) (message : String) :
    function <$> (Core.rej rule message : Core.T α) = (Core.rej rule message : Core.T β) := rfl

inductive StatementWrite : Stmt → Place → (ArtifactProfile → PlaceInfo → Bool) → Prop where
  | assign (place value origin) : StatementWrite (.assign place value origin) place (fun _ info => info.bindingWritable)
  | assignOp (operator place value origin) :
    StatementWrite (.assignOp operator place value origin) place (fun _ info => info.bindingWritable)
  | append (place source origin) :
    StatementWrite (.append place source origin) place (fun profile info => info.ownerMutationWritable profile)
  | popN (place count origin) : StatementWrite (.popN place count origin) place (fun _ info => info.contentsWritable)
  | resize (place count fill origin) :
    StatementWrite (.resize place count fill origin) place (fun _ info => info.contentsWritable)
  | clear (place origin) : StatementWrite (.clear place origin) place (fun _ info => info.contentsWritable)
  | replace (place value origin) :
    StatementWrite (.assignWhole place value origin) place (fun _ info => info.bindingWritable && info.contentsWritable)

theorem source_statement_write_authority {env : Core.TEnv} {scope : Nat} {statement : Stmt}
    {owner : Place} {permission : ArtifactProfile → PlaceInfo → Bool}
    (effect : StatementWrite statement owner permission) {start finish : Nat} {after : Core.TEnv}
    (source : Core.tyStmt env scope statement start = .ok (after, finish)) :
    ∃ info ownerStart ownerFinish, Core.tyPlace env owner ownerStart = .ok (info, ownerFinish) ∧
      permission env.mod.profile info = true := by
  cases effect with
  | assign owner value origin =>
    unfold Core.tyStmt at source
    obtain ⟨_, ownerStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨info, ownerFinish, placeSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    refine ⟨info, ownerStart, ownerFinish, placeSource, ?_⟩
    apply Classical.byContradiction
    intro denied
    have noWrite : (info.bindingWritable) = false := Bool.eq_false_iff.mpr denied
    simp [Core.requireWrite, noWrite, mapped_rejection, st_bind_ok, st_pure_ok, rej_ok] at source
    try grind [st_bind_ok, rej_ok]
  | assignOp operator owner value origin =>
    unfold Core.tyStmt at source
    obtain ⟨_, ownerStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨info, ownerFinish, placeSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    refine ⟨info, ownerStart, ownerFinish, placeSource, ?_⟩
    apply Classical.byContradiction
    intro denied
    have noWrite : (info.bindingWritable) = false := Bool.eq_false_iff.mpr denied
    simp [Core.requireWrite, noWrite, mapped_rejection, st_bind_ok, st_pure_ok, rej_ok] at source
    try grind [st_bind_ok, rej_ok]
  | append owner value origin =>
    unfold Core.tyStmt at source
    obtain ⟨_, ownerStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨info, ownerFinish, placeSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    refine ⟨info, ownerStart, ownerFinish, placeSource, ?_⟩
    apply Classical.byContradiction
    intro denied
    have noWrite : (info.ownerMutationWritable env.mod.profile) = false := Bool.eq_false_iff.mpr denied
    simp [Core.requireWrite, noWrite, mapped_rejection, st_bind_ok, st_pure_ok, rej_ok] at source
    try grind [st_bind_ok, rej_ok]
  | popN owner count origin =>
    unfold Core.tyStmt at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, ownerStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨info, ownerFinish, placeSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    refine ⟨info, ownerStart, ownerFinish, placeSource, ?_⟩
    apply Classical.byContradiction
    intro denied
    have noWrite : (info.contentsWritable) = false := Bool.eq_false_iff.mpr denied
    simp [Core.requireWrite, noWrite, mapped_rejection, st_bind_ok, st_pure_ok, rej_ok] at source
    try grind [st_bind_ok, rej_ok]
  | resize owner count fill origin =>
    cases fill
    all_goals
      unfold Core.tyStmt at source
      obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
      obtain ⟨_, ownerStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
      obtain ⟨info, ownerFinish, placeSource, source⟩ := (st_bind_ok _ _ _ _).mp source
      refine ⟨info, ownerStart, ownerFinish, placeSource, ?_⟩
      apply Classical.byContradiction
      intro denied
      have noWrite : (info.contentsWritable) = false := Bool.eq_false_iff.mpr denied
      simp [Core.requireWrite, noWrite, mapped_rejection, st_bind_ok, st_pure_ok, rej_ok] at source
      try grind [st_bind_ok, rej_ok]
  | clear owner origin =>
    unfold Core.tyStmt at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, ownerStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨info, ownerFinish, placeSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    refine ⟨info, ownerStart, ownerFinish, placeSource, ?_⟩
    apply Classical.byContradiction
    intro denied
    have noWrite : (info.contentsWritable) = false := Bool.eq_false_iff.mpr denied
    simp [Core.requireWrite, noWrite, mapped_rejection, st_bind_ok, st_pure_ok, rej_ok] at source
    try grind [st_bind_ok, rej_ok]
  | replace owner value origin =>
    unfold Core.tyStmt at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, ownerStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨info, ownerFinish, placeSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    refine ⟨info, ownerStart, ownerFinish, placeSource, ?_⟩
    apply Classical.byContradiction
    intro denied
    have noWrite : (info.bindingWritable && info.contentsWritable) = false := Bool.eq_false_iff.mpr denied
    cases shape : info.ty <;> simp [shape, Core.requireWrite, noWrite, mapped_rejection, st_bind_ok, st_pure_ok, rej_ok] at source
    all_goals try grind [st_bind_ok, rej_ok]

inductive ExpressionWrite : Expr → Place → (ArtifactProfile → PlaceInfo → Bool) → Prop where
  | push (place value origin) :
    ExpressionWrite (.push place value origin) place (fun profile info => info.ownerMutationWritable profile)
  | pop (place origin) : ExpressionWrite (.pop place origin) place (fun _ info => info.contentsWritable)
  | reference (place) :
    ExpressionWrite (.ref .mutable place) place (fun profile info => info.referenceWritable profile)

theorem source_expression_write_authority {env : Core.TEnv} {expression : Expr}
    {owner : Place} {permission : ArtifactProfile → PlaceInfo → Bool}
    (effect : ExpressionWrite expression owner permission) {start finish : Nat} {ty : Ty}
    (source : Core.tyExpr env expression start = .ok (ty, finish)) :
    ∃ info ownerStart ownerFinish, Core.tyPlace env owner ownerStart = .ok (info, ownerFinish) ∧
      permission env.mod.profile info = true := by
  cases effect with
  | push owner value origin =>
    have solve : ∀ ownerStart, (do
        let info ← Core.tyPlace env owner
        let element ← ownerElement env info.ty
        let argTy ← Core.tyExpr env value
        unless argTy == element do rej .type "a pushed element of another type than the array's"
        requireWrite "push" (info.ownerMutationWritable env.mod.profile)
        pure (Ty.ref .mutable element)) ownerStart = .ok (ty, finish) →
        ∃ info ownerStart ownerFinish, Core.tyPlace env owner ownerStart = .ok (info, ownerFinish) ∧
          info.ownerMutationWritable env.mod.profile = true := by
      intro ownerStart source
      obtain ⟨info, ownerFinish, placeSource, source⟩ := (st_bind_ok _ _ _ _).mp source
      refine ⟨info, ownerStart, ownerFinish, placeSource, ?_⟩
      apply Classical.byContradiction
      intro denied
      have noWrite : info.ownerMutationWritable env.mod.profile = false := Bool.eq_false_iff.mpr denied
      simp [Core.requireWrite, noWrite, mapped_rejection, st_bind_ok, st_pure_ok, rej_ok] at source
      grind [st_bind_ok, rej_ok]
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
  | pop owner origin =>
    unfold Core.tyExpr at source
    obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨_, ownerStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
    obtain ⟨info, ownerFinish, placeSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    refine ⟨info, ownerStart, ownerFinish, placeSource, ?_⟩
    apply Classical.byContradiction
    intro denied
    have noWrite : info.contentsWritable = false := Bool.eq_false_iff.mpr denied
    simp [Core.requireWrite, noWrite, mapped_rejection, st_bind_ok, st_pure_ok, rej_ok] at source
  | reference owner =>
    unfold Core.tyExpr at source
    obtain ⟨info, ownerFinish, placeSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    refine ⟨info, start, ownerFinish, placeSource, ?_⟩
    apply Classical.byContradiction
    intro denied
    have noWrite : info.referenceWritable env.mod.profile = false := Bool.eq_false_iff.mpr denied
    simp [Core.requireWrite, noWrite, mapped_rejection, st_bind_ok, st_pure_ok, rej_ok] at source
    grind [st_bind_ok, rej_ok]

theorem source_mutable_slice_authority {env : Core.TEnv} {view : View} {lo hi : Bound}
    {origin : OriginId} {start finish : Nat} {ty : Ty}
    (source : Core.tyExpr env (.slice .mutable view lo hi origin) start = .ok (ty, finish)) :
    ∃ element viewStart viewFinish,
      Core.tyView env view viewStart = .ok ((element, true), viewFinish) := by
  unfold Core.tyExpr at source
  obtain ⟨_, viewStart, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨⟨element, writable⟩, viewFinish, viewSource, source⟩ := (st_bind_ok _ _ _ _).mp source
  have allowed : writable = true := by
    apply Classical.byContradiction
    intro denied
    have noWrite : writable = false := Bool.eq_false_iff.mpr denied
    simp [Core.requireWrite, noWrite, mapped_rejection, st_bind_ok, st_pure_ok, rej_ok] at source
  exact ⟨element, viewStart, viewFinish, by simpa only [allowed] using viewSource⟩

#print axioms source_statement_write_authority
#print axioms source_expression_write_authority
#print axioms source_mutable_slice_authority

end Goose.Lower.Validation
