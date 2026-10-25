import Goose.Lower.Validation.PermissionPreservationSourceValues
import Goose.Lower.Validation.SourceStatementTypingBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerBlock_value_permissionTransfer
    {env : Core.TEnv} {sourcePre : List (VarId × Ty)} {scope : ScopeId}
    {statements : List Stmt} {expr : Expr} {sourceType targetType : Ty} {start finish : Nat}
    (source : Core.tyBlock env sourcePre (.mk scope statements (some expr)) start = .ok (sourceType, finish))
    (compatible : sourceType.passableTo targetType = true)
    {results : List Ty} {loop : Option LoopCtx} {pre : List (SlotId × ValueId × OriginId)} {want : Bool}
    {before after : LS} {value : ValueId}
    (run : lowerBlock loop pre want (.mk scope statements (some expr))
      (lowerEnv env.mod env.vars results) before = (value, after))
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before)
    (live : after.cur.isSome = true) :
    PermissionTransfer env.mod.profile
      (FreshWritableEvidence (lowerEnv env.mod env.vars results) 0 after)
      (FreshContentsEvidence (lowerEnv env.mod env.vars results) 0 after) value targetType := by
  obtain ⟨_, declared, finalEnv, statementStart, valueStart, declaration, statementsTyped, valueSource⟩ :=
    tyBlock_checked_children source
  have declaredEnv := declarePre_lowerEnv declaration results
  have finalLower := tyStmts_lowerEnv statementsTyped results
  have sameEnv : lowerEnv finalEnv.mod finalEnv.vars results = lowerEnv env.mod env.vars results :=
    finalLower.trans declaredEnv
  simp only [lowerBlock, inScope] at run
  obtain ⟨_, entered, enterRun, run⟩ := bind_eq.mp run
  obtain ⟨_, pushed, pushRun, run⟩ := bind_eq.mp run
  obtain ⟨result, bodyAfter, bodyRun, run⟩ := bind_eq.mp run
  obtain ⟨_, popped, popRun, run⟩ := bind_eq.mp run
  obtain ⟨resultEq, stateEq⟩ := pure_eq.mp run
  subst after
  subst value
  obtain ⟨_, initialized, initRun, bodyRun⟩ := bind_eq.mp bodyRun
  obtain ⟨_, statementsAfter, statementsRun, bodyRun⟩ := bind_eq.mp bodyRun
  obtain ⟨result, valueAfter, valueRun, bodyRun⟩ := bind_eq.mp bodyRun
  obtain ⟨_, left, leaveRun, bodyRun⟩ := bind_eq.mp bodyRun
  obtain ⟨rfl, rfl⟩ := pure_eq.mp bodyRun
  have poppedLive := dead_popScope.live_before popRun live
  have valueLive := (dead_emitEffect (.leave scope)).live_before leaveRun poppedLive
  have enteredGenerated := generated.emitEffect (.enter scope) enterRun
  have pushedGenerated : GeneratedBuilderState pushed := by
    rw [pushScope_run] at pushRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj pushRun
    exact ⟨enteredGenerated.dense, enteredGenerated.live, enteredGenerated.targets⟩
  have initializedGenerated := pushedGenerated.initSlots pre initRun
  have enteredFrames := frames.mono (advB_emitEffect (.enter scope) _ _ _ _ enterRun).ext
  have pushedFrames : LoopBuilderFrames loop pushed := by
    rw [pushScope_run] at pushRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj pushRun
    exact enteredFrames
  have initializedFrames := pushedFrames.mono (advB_initSlots pre _ _ _ _ initRun).ext
  have statementsGenerated := initializedGenerated.lowerStmts loop statements initializedFrames.toTargets statementsRun
  have valueGenerated := statementsGenerated.lowerBlockValue want (some expr) valueRun
  simp only [lowerBlockValue] at valueRun
  have finalRun : lowerExpr expr (lowerEnv finalEnv.mod finalEnv.vars results) statementsAfter =
      (result, valueAfter) := by rw [sameEnv]; exact valueRun
  have transferred := lowerExpr_generated_permissionTransfer expr valueSource compatible finalRun valueLive statementsGenerated
  have profile : finalEnv.mod.profile = env.mod.profile :=
    congrArg (fun le : LEnv => le.mod.profile) sameEnv
  rw [sameEnv, profile] at transferred
  have retained := transferred.mono
    (fun _ evidence => (evidence.of_framed_run (loop := none) leaveRun (dense_emitEffect _)
      (advB_emitEffect _) (types_emitEffect _) (generatedTargetFrame_emitEffect none _)
      valueGenerated.dense valueGenerated.live trivial).weaken (Nat.zero_le _))
    (fun _ evidence => (evidence.of_framed_run (loop := none) leaveRun (dense_emitEffect _)
      (advB_emitEffect _) (types_emitEffect _) (generatedTargetFrame_emitEffect none _)
      valueGenerated.dense valueGenerated.live trivial).weaken (Nat.zero_le _))
  rw [popScope_run] at popRun
  obtain ⟨_, rfl⟩ := Prod.mk.inj popRun
  exact retained

#print axioms lowerBlock_value_permissionTransfer

end Goose.Lower.Validation
