import Goose.Lower.Validation.PermissionPreservationControlEffects
import Goose.Core.Sound.Check

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem permissionInstructions_expression_source {env sourceAfter : Core.TEnv} {scope start finish : Nat}
    {expr : Expr} {origin : OriginId}
    (source : Core.tyStmt env scope (.expr expr origin) start = .ok (sourceAfter, finish))
    {module : GIR.Module} {func : Func} {results : List Ty} {loop : Option LoopCtx} {first : Nat}
    {before after : LS} {result : Unit}
    (run : lowerStmt loop (.expr expr origin) (lowerEnv env.mod env.vars results) before = (result, after))
    (_generated : GeneratedBuilderState before) (floor : first ≤ before.vals.size)
    (child : ∀ type childStart childFinish,
      Core.tyExpr env expr childStart = .ok (type, childFinish) →
      ∀ value middle, lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, middle) →
      NewPermissionInstructions module func (lowerEnv env.mod env.vars results) before.vals.size before middle) :
    NewPermissionInstructions module func (lowerEnv env.mod env.vars results) first before after := by
  simp only [Core.tyStmt] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨type, childFinish, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  simp only [lowerStmt] at run
  obtain ⟨value, middle, childRun, returned⟩ := bind_eq.mp run
  obtain ⟨_, rfl⟩ := pure_eq.mp returned
  exact (child type _ childFinish childSource value middle childRun).weaken floor

theorem permissionInstructions_abort {module : GIR.Module} {func : Func} {le : LEnv}
    {loop : Option LoopCtx} {first : Nat} {kind : String} {origin : OriginId}
    {before after : LS} {result : Unit}
    (run : lowerStmt loop (.abort kind origin) le before = (result, after)) :
    NewPermissionInstructions module func le first before after :=
  .emitFreeTerm run trivial

theorem permissionInstructions_exit_source {env sourceAfter : Core.TEnv} {scope start finish : Nat}
    {expr : Expr} {origin : OriginId}
    (source : Core.tyStmt env scope (.exit expr origin) start = .ok (sourceAfter, finish))
    {module : GIR.Module} {func : Func} {results : List Ty} {loop : Option LoopCtx} {first : Nat}
    {before after : LS} {result : Unit}
    (run : lowerStmt loop (.exit expr origin) (lowerEnv env.mod env.vars results) before = (result, after))
    (generated : GeneratedBuilderState before) (floor : first ≤ before.vals.size)
    (child : ∀ type childStart childFinish,
      Core.tyExpr env expr childStart = .ok (type, childFinish) →
      ∀ value middle, lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, middle) →
      NewPermissionInstructions module func (lowerEnv env.mod env.vars results) before.vals.size before middle) :
    NewPermissionInstructions module func (lowerEnv env.mod env.vars results) first before after := by
  simp only [Core.tyStmt] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨type, childFinish, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  simp only [lowerStmt] at run
  obtain ⟨value, middle, childRun, emitted⟩ := bind_eq.mp run
  have permitted := (child type _ childFinish childSource value middle childRun).weaken floor
  have middleGenerated := generated.lowerExpr expr childRun
  exact permitted.compose_framed (.emitFreeTerm emitted trivial) emitted
    (dense_emitTerm _) (advB_emitTerm _) (types_emitTerm _)
    (generatedTargetFrame_emitNoSuccessors none _ (by simp [Term.successors])) middleGenerated (by trivial)

theorem permissionInstructions_assert_source {env sourceAfter : Core.TEnv} {scope start finish : Nat}
    {expr : Expr} {origin : OriginId}
    (source : Core.tyStmt env scope (.assertS expr origin) start = .ok (sourceAfter, finish))
    {module : GIR.Module} {func : Func} {results : List Ty} {loop : Option LoopCtx} {first : Nat}
    {before after : LS} {result : Unit}
    (run : lowerStmt loop (.assertS expr origin) (lowerEnv env.mod env.vars results) before = (result, after))
    (generated : GeneratedBuilderState before) (floor : first ≤ before.vals.size)
    (child : ∀ type childStart childFinish,
      Core.tyExpr env expr childStart = .ok (type, childFinish) →
      ∀ value middle, lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, middle) →
      NewPermissionInstructions module func (lowerEnv env.mod env.vars results) before.vals.size before middle) :
    NewPermissionInstructions module func (lowerEnv env.mod env.vars results) first before after := by
  simp only [Core.tyStmt] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨type, childFinish, childSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  simp only [lowerStmt] at run
  obtain ⟨value, middle, childRun, tailRun⟩ := bind_eq.mp run
  have permitted := (child type _ childFinish childSource value middle childRun).weaken floor
  have middleGenerated := generated.lowerExpr expr childRun
  cases current : middle.cur with
  | none =>
    rw [whenLive_none _ _ _ current] at tailRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj tailRun
    exact permitted
  | some currentBlock =>
    rw [whenLive_some _ _ _ current] at tailRun
    obtain ⟨arms, forked, forkRun, tailRun⟩ := bind_eq.mp tailRun
    obtain ⟨_, failed, failedRun, tailRun⟩ := bind_eq.mp tailRun
    obtain ⟨_, aborted, abortRun, passedRun⟩ := bind_eq.mp tailRun
    have forkGenerated := middleGenerated.fork value forkRun
    have ids := fork_ids forkRun
    have failedBound : arms.2 < forked.blocks.size := by
      rw [ids.1, ids.2]
      exact Nat.add_lt_add_left (by decide : 1 < 2) _
    have failedGenerated := forkGenerated.setCur (some arms.2)
      (by intro target same; cases same; exact failedBound) failedRun
    have forkPermissions := permitted.compose_framed (NewPermissionInstructions.fork forkRun)
      forkRun (dense_fork value) (advB_fork value) (types_fork value)
      (generatedTargetFrame_fork none value) middleGenerated (by trivial)
    have failedPermissions := forkPermissions.append_setCur failedRun
    have abortedPermissions := failedPermissions.compose_framed
      (NewPermissionInstructions.emitFreeTerm abortRun trivial) abortRun
      (dense_emitTerm _) (advB_emitTerm _) (types_emitTerm _)
      (generatedTargetFrame_emitNoSuccessors none _ (by simp [Term.successors])) failedGenerated (by trivial)
    exact abortedPermissions.append_setCur passedRun

#print axioms permissionInstructions_assert_source

#print axioms permissionInstructions_expression_source
#print axioms permissionInstructions_abort
#print axioms permissionInstructions_exit_source

end Goose.Lower.Validation
