import Goose.Lower.Validation.ReplacementSourceSitesOutputs
import Goose.Lower.Validation.ReplacementSourceSitesControl
import Goose.Lower.Validation.SourceStatementTypingTransfers

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {root : DemandNode} {targets : List BlockId}

theorem replacementSites_let_source {env output : Core.TEnv} {results : List Ty} {slot : VarId}
    {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.letS slot expr origin) start = .ok (output, finish))
    (child : ReplacementSitesExprChild (root := root) (targets := targets) env results expr) (loop : Option LoopCtx)
    {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerStmt loop (.letS slot expr origin)) := by
  obtain ⟨localVar, childType, childStart, _, childSource, _, _⟩ := tyStmt_let_children source
  exact (child childSource generated).bind ((ReplacementSitesAt.coerceSlot _ _ _ _ _).bind
    (ReplacementSitesAt.emitEffect _ (by intros; trivial)))

theorem replacementSites_expr_source {env output : Core.TEnv} {results : List Ty}
    {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.expr expr origin) start = .ok (output, finish))
    (child : ReplacementSitesExprChild (root := root) (targets := targets) env results expr) (loop : Option LoopCtx)
    {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerStmt loop (.expr expr origin)) := by
  obtain ⟨type, childSource, _⟩ := tyStmt_expr_children source
  exact (child childSource generated).bind (ReplacementSitesAt.pure _ _ _)

theorem replacementSites_return_source {env output : Core.TEnv} {results : List Ty}
    {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.ret (some expr) origin) start = .ok (output, finish))
    (child : ReplacementSitesExprChild (root := root) (targets := targets) env results expr) (loop : Option LoopCtx)
    {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerStmt loop (.ret (some expr) origin)) := by
  obtain ⟨expected, actual, impl, _, _, _, childSource, _, _⟩ := tyStmt_return_children source
  unfold lowerStmt
  apply (child childSource generated).bind
  apply (ReplacementSitesAt.coerceResult _ _ _ _).bind
  apply (ReplacementSitesAt.pure _ _ _).bind
  exact (ReplacementSitesAt.leaveTo _ _ _).bind (ReplacementSitesAt.emitTerm _ _ _)

theorem ReplacementSitesAt.return_none (le : LEnv) (before : LS) (loop : Option LoopCtx) (origin : OriginId) :
    ReplacementSitesAt (root := root) (targets := targets) le before (lowerStmt loop (.ret none origin)) :=
  (ReplacementSitesAt.pure _ _ _).bind ((ReplacementSitesAt.leaveTo _ _ _).bind (ReplacementSitesAt.emitTerm _ _ _))

theorem ReplacementSitesAt.breakStmt (le : LEnv) (before : LS) (loop : Option LoopCtx) (origin : OriginId)
    (allowed : ReplacementLoopTargetsIncluded loop targets) :
    ReplacementSitesAt (root := root) (targets := targets) le before (lowerStmt loop (.brk origin)) := by
  cases loop with
  | none => exact ReplacementSitesAt.pure _ _ _
  | some loop =>
    have targetAllowed := allowed loop.breakTo (by simp [LoopBuilderFrameTargets])
    exact (ReplacementSitesAt.leaveTo _ _ _).bind (ReplacementSitesAt.emitTerm _ _ _
      (by simpa [Term.successors] using Or.inl targetAllowed))

theorem ReplacementSitesAt.continueStmt (le : LEnv) (before : LS) (loop : Option LoopCtx) (origin : OriginId)
    (allowed : ReplacementLoopTargetsIncluded loop targets) :
    ReplacementSitesAt (root := root) (targets := targets) le before (lowerStmt loop (.cont origin)) := by
  cases loop with
  | none => exact ReplacementSitesAt.pure _ _ _
  | some loop =>
    apply (ReplacementSitesAt.leaveTo _ _ _).bind
    cases kind : loop.cont with
    | jump header =>
      have targetAllowed := allowed header (by simp [LoopBuilderFrameTargets, kind])
      exact ReplacementSitesAt.emitTerm _ _ _ (by simpa [Term.successors] using Or.inl targetAllowed)
    | next header type value =>
      have targetAllowed := allowed header (by simp [LoopBuilderFrameTargets, kind])
      exact (ReplacementSitesAt.emitDef _ (by intros; trivial)).bind (ReplacementSitesAt.emitTerm _ _ _
        (by simpa [Term.successors] using Or.inl targetAllowed))

theorem replacementSites_assert_source {env output : Core.TEnv} {results : List Ty}
    {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assertS expr origin) start = .ok (output, finish))
    (child : ReplacementSitesExprChild (root := root) (targets := targets) env results expr) (loop : Option LoopCtx)
    {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerStmt loop (.assertS expr origin)) := by
  have childSource := (tyStmt_assert_children source).1
  apply (child childSource generated).bind
  apply ReplacementSitesAt.whenLive
  intro block live
  exact (ReplacementSitesAt.fork _ _ _).bind ((ReplacementSitesAt.setCur _ _ _).bind
    ((ReplacementSitesAt.emitTerm _ _ _).bind (ReplacementSitesAt.setCur _ _ _)))

theorem replacementSites_exit_source {env output : Core.TEnv} {results : List Ty}
    {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.exit expr origin) start = .ok (output, finish))
    (child : ReplacementSitesExprChild (root := root) (targets := targets) env results expr) (loop : Option LoopCtx)
    {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerStmt loop (.exit expr origin)) := by
  obtain ⟨integer, childSource, _⟩ := tyStmt_exit_children source
  exact (child childSource generated).bind (ReplacementSitesAt.emitTerm _ _ _)

end Goose.Lower.Validation
