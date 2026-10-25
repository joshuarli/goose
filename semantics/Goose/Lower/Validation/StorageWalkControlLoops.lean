import Goose.Lower.Validation.StorageWalkFlowFork
import Goose.Lower.Validation.ScopeFlowLoop

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageWalkConfiguration.loopBack {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : StorageWalkConfiguration slots entry exit before) (continueTo : ContKind) (env : LEnv)
    (target : entry (scopeContinueHeader continueTo) = before.stack)
    (bound : scopeContinueHeader continueTo < before.blocks.size) :
    StorageWalkConfiguration slots entry exit (scopeLoopBack continueTo env before).2 := by
  cases continueTo with
  | jump header =>
    exact config.emitTerm (.br header []) rfl env
      (by
        intro destination member
        have same : destination = header := by simpa [Term.successors] using member
        subst destination
        exact target)
      (by
        intro destination member
        have same : destination = header := by simpa [Term.successors] using member
        subst destination
        exact bound)
  | next header type counter =>
    cases live : before.cur with
    | none =>
      simpa only [scopeLoopBack, Goose.Lower.rangeBack, bind_run, isLive_none live, Bool.false_eq_true,
        reduceIte, pure_run] using config
    | some block =>
      have defined := config.emitDef (.next type counter) env (fun _ => trivial)
      have stack : (Goose.Lower.emitDef (.next type counter) env before).2.stack = before.stack :=
        (advB_emitDef (.next type counter) env before _ _ rfl).stack
      have closed := defined.emitTerm
        (.br header [(Goose.Lower.emitDef (.next type counter) env before).1]) rfl env
        (by
          intro destination member
          have same : destination = header := by simpa [Term.successors] using member
          subst destination
          exact target.trans stack.symm)
        (by
          intro destination member
          have same : destination = header := by simpa [Term.successors] using member
          subst destination
          rw [emitDef_size]
          exact bound)
      simpa only [scopeLoopBack, Goose.Lower.rangeBack, bind_run, isLive_run live, reduceIte] using closed

theorem storageWalk_loopBody_flow {slots : Array Slot} {stack : List ScopeId}
    (condition : ValueId) (continueTo : ContKind) (body : Nat → BlockId → B ValueId)
    (bodyAction : ∀ depth target, StorageWalkAction slots stack
      (some ⟨depth, target, continueTo⟩) (body depth target))
    (env : LEnv) (before : LS) (entry exit : BlockId → List ScopeId)
    (config : StorageWalkConfiguration slots entry exit before) (stackEq : before.stack = stack)
    (current : BlockId) (live : before.cur = some current)
    (headerStack : entry (scopeContinueHeader continueTo) = before.stack)
    (headerBound : scopeContinueHeader continueTo < before.blocks.size)
    {result : Unit} {after : LS}
    (run : Goose.Lower.loopBody condition body (scopeLoopBack continueTo) env before = (result, after)) :
    ∃ nextEntry nextExit, StorageWalkConfiguration slots nextEntry nextExit after ∧
      ScopeMapAdvance before entry exit nextEntry nextExit := by
  simp only [Goose.Lower.loopBody, bind_eq] at run
  obtain ⟨observedStack, observed, observeRun, ⟨tb, xb⟩, forked, forkRun, u1, started, startRun,
    value, evaluated, bodyRun, u2, closed, backRun, resumeRun⟩ := run
  simp only [get_apply, Prod.mk.injEq] at observeRun
  obtain ⟨rfl, rfl⟩ := observeRun
  have ids := fork_ids forkRun
  obtain ⟨tbId, xbId⟩ := Prod.mk.inj ids.1
  subst tbId xbId
  have forkedConfig := config.fork condition env
  rw [forkRun] at forkedConfig
  dsimp only at forkedConfig
  have forkTargets := fork_open_targets live (config.openCurrent.bound current live) condition env
  rw [forkRun] at forkTargets
  dsimp only at forkTargets
  obtain ⟨bodyRow, bodyLookup, bodyOpen⟩ := forkTargets.1
  obtain ⟨exitBody, exitRow, exitOpen⟩ := forkTargets.2
  have forkAdvance := advB_fork condition env before _ _ forkRun
  have startedConfig := forkedConfig.setCur before.blocks.size bodyRow bodyLookup bodyOpen (by
    simp [forkScopeMap, forkAdvance.stack]) env
  rw [startRun] at startedConfig
  dsimp only at startedConfig
  have startAdvance := adv_setCur_step forkAdvance (Or.inr (Nat.le_refl _))
    (by have size := ids.2; nat_omega) startRun
  have exitOld : before.blocks.size + 1 < started.blocks.size := by
    rw [setCur_blocks startRun]
    have size := ids.2
    nat_omega
  have startedCurrent : started.cur = some before.blocks.size := by
    rw [setCur_run] at startRun
    exact congrArg (fun pair => pair.2.cur) startRun.symm
  have notExit : started.cur ≠ some (before.blocks.size + 1) := by
    rw [startedCurrent]
    intro same
    have equality := Option.some.inj same
    nat_omega
  have headerOld : scopeContinueHeader continueTo < started.blocks.size :=
    Nat.lt_of_lt_of_le headerBound startAdvance.ext.1
  have startedLoop : ScopeLoopContext (some ⟨before.stack.length, before.blocks.size + 1, continueTo⟩)
      (forkScopeMap before entry) started.stack started.blocks.size := by
    refine ⟨?_, exitOld, ?_, headerOld, ?_⟩
    · rw [startAdvance.stack]
      exact Nat.le_refl _
    · rw [startAdvance.stack]
      simp [forkScopeMap]
    · rw [startAdvance.stack]
      change forkScopeMap before entry (scopeContinueHeader continueTo) = _
      rw [forkScopeMap_old before entry _ headerBound, headerStack]
      simp
  obtain ⟨nextEntry, nextExit, evaluatedConfig, bodyMaps⟩ :=
    (bodyAction before.stack.length (before.blocks.size + 1)).preserves env started
      (forkScopeMap before entry) (forkScopeMap before exit) startedConfig startedLoop
      (by rw [startAdvance.stack]; exact stackEq)
  rw [bodyRun] at evaluatedConfig
  dsimp only at evaluatedConfig
  have bodyAdvance := (bodyAction before.stack.length (before.blocks.size + 1)).advance env started _ _ bodyRun
  have evaluatedStack : evaluated.stack = before.stack := bodyAdvance.stack.trans startAdvance.stack
  have backTarget : nextEntry (scopeContinueHeader continueTo) = evaluated.stack := by
    rw [(bodyMaps _ headerOld).1, forkScopeMap_old before entry _ headerBound, headerStack]
    exact evaluatedStack.symm
  have backBound : scopeContinueHeader continueTo < evaluated.blocks.size :=
    Nat.lt_of_lt_of_le headerOld bodyAdvance.ext.1
  have closedConfig := evaluatedConfig.loopBack continueTo env backTarget backBound
  rw [backRun] at closedConfig
  dsimp only at closedConfig
  have backAdvance := scopeLoopBack_advance continueTo env evaluated _ _ backRun
  have evaluatedOther := LS_Adv.otherCurrent bodyAdvance exitOld notExit
  have evaluatedExitRow : evaluated.blocks[before.blocks.size + 1]? = some exitBody :=
    bodyAdvance.keep _ exitBody notExit (by rw [setCur_blocks startRun]; exact exitRow)
  have closedExitRow : closed.blocks[before.blocks.size + 1]? = some exitBody :=
    backAdvance.keep _ exitBody evaluatedOther evaluatedExitRow
  have closedStack : closed.stack = before.stack := backAdvance.stack.trans evaluatedStack
  have exitStack := (bodyMaps _ exitOld).2 notExit
  have resumedConfig := closedConfig.setCur (before.blocks.size + 1) exitBody closedExitRow exitOpen (by
    rw [exitStack]
    simp [forkScopeMap, closedStack]) env
  rw [resumeRun] at resumedConfig
  dsimp only at resumedConfig
  exact ⟨nextEntry, nextExit, resumedConfig,
    (forkScopeMap_advance before entry exit).trans startAdvance bodyMaps⟩

theorem storageWalk_loopCondition_flow {slots : Array Slot} {stack : List ScopeId}
    (continueTo : ContKind) {condition : B ValueId}
    (conditionAction : StorageWalkAction slots stack none condition)
    (body : Nat → BlockId → B ValueId)
    (bodyAction : ∀ depth target, StorageWalkAction slots stack
      (some ⟨depth, target, continueTo⟩) (body depth target))
    (env : LEnv) (before : LS) (entry exit : BlockId → List ScopeId)
    (config : StorageWalkConfiguration slots entry exit before) (stackEq : before.stack = stack)
    (headerStack : entry (scopeContinueHeader continueTo) = before.stack)
    (headerBound : scopeContinueHeader continueTo < before.blocks.size)
    {result : Unit} {after : LS}
    (run : scopeLoopCondition continueTo condition body env before = (result, after)) :
    ∃ nextEntry nextExit, StorageWalkConfiguration slots nextEntry nextExit after ∧
      ScopeMapAdvance before entry exit nextEntry nextExit := by
  simp only [scopeLoopCondition, bind_eq] at run
  obtain ⟨value, evaluated, conditionRun, bodyRun⟩ := run
  obtain ⟨middleEntry, middleExit, middleConfig, conditionMaps⟩ :=
    conditionAction.preserves env before entry exit config trivial stackEq
  rw [conditionRun] at middleConfig
  dsimp only at middleConfig
  have conditionAdvance := conditionAction.advance env before _ _ conditionRun
  have middleStack : evaluated.stack = stack := by rw [conditionAdvance.stack]; exact stackEq
  have middleHeader : middleEntry (scopeContinueHeader continueTo) = evaluated.stack := by
    rw [(conditionMaps _ headerBound).1, headerStack]
    exact conditionAdvance.stack.symm
  have middleBound := Nat.lt_of_lt_of_le headerBound conditionAdvance.ext.1
  cases live : evaluated.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at bodyRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj bodyRun
    exact ⟨middleEntry, middleExit, middleConfig, conditionMaps⟩
  | some current =>
    rw [whenLive_some _ _ _ live] at bodyRun
    obtain ⟨afterEntry, afterExit, afterConfig, bodyMaps⟩ :=
      storageWalk_loopBody_flow value continueTo body bodyAction env evaluated middleEntry middleExit middleConfig
        middleStack current live middleHeader middleBound bodyRun
    exact ⟨afterEntry, afterExit, afterConfig, conditionMaps.trans conditionAdvance bodyMaps⟩


private theorem storageWalk_header_advance (types : List VTy) (arguments : List ValueId)
    (allocateAdvance : AdvB (Goose.Lower.newBlock types)) (tail : BlockId → List ValueId → B α)
    (tailAdvance : ∀ header params, AdvB (tail header params)) :
    AdvB (do
      let (header, params) ← Goose.Lower.newBlock types
      Goose.Lower.emitTerm (.br header arguments)
      Goose.Lower.setCur (some header)
      tail header params) := by
  intro env before result after run
  simp only [bind_eq] at run
  obtain ⟨⟨header, params⟩, allocated, allocatedRun, _, branched, branchRun,
    _, selected, selectedRun, tailRun⟩ := run
  have shape := allocatedRun
  rw [scope_newBlock_run] at shape
  have headerId := (Prod.mk.inj (Prod.mk.inj shape).1).1
  have allocatedSize : allocated.blocks.size = before.blocks.size + 1 := by
    rw [← (Prod.mk.inj shape).2]
    simp
  have allocatedAdvance := allocateAdvance env before _ _ allocatedRun
  have branchedAdvance := allocatedAdvance.trans (adv_emitTerm branchRun)
  have headerMine : Mine before header := Or.inr (by rw [← headerId]; exact Nat.le_refl _)
  have headerBound : header < branched.blocks.size := by
    have size := (adv_emitTerm branchRun).ext.1
    rw [← headerId]
    nat_omega
  have selectedAdvance := adv_setCur_step branchedAdvance headerMine headerBound selectedRun
  exact selectedAdvance.trans (tailAdvance header params env selected _ _ tailRun)

theorem StorageWalkAction.header {slots : Array Slot} {stack : List ScopeId}
    {loop : Option LoopCtx} (types : List VTy) (arguments : List ValueId)
    (allocateAdvance : AdvB (Goose.Lower.newBlock types)) (tail : BlockId → List ValueId → B α)
    (tailAdvance : ∀ header params, AdvB (tail header params))
    (tailFlow : ∀ header params env before entry exit,
      StorageWalkConfiguration slots entry exit before →
      ScopeLoopContext loop entry before.stack before.blocks.size → before.stack = stack →
      before.cur = some header → entry header = before.stack → header < before.blocks.size →
      ∀ result after, tail header params env before = (result, after) →
      ∃ nextEntry nextExit, StorageWalkConfiguration slots nextEntry nextExit after ∧
        ScopeMapAdvance before entry exit nextEntry nextExit) :
    StorageWalkAction slots stack loop (do
      let (header, params) ← Goose.Lower.newBlock types
      Goose.Lower.emitTerm (.br header arguments)
      Goose.Lower.setCur (some header)
      tail header params) := by
  refine ⟨storageWalk_header_advance types arguments allocateAdvance tail tailAdvance, ?_⟩
  intro env before entry exit config context stackEq
  generalize run : (do
      let (header, params) ← Goose.Lower.newBlock types
      Goose.Lower.emitTerm (.br header arguments)
      Goose.Lower.setCur (some header)
      tail header params) env before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  simp only [bind_eq] at run
  obtain ⟨⟨header, params⟩, allocated, allocateRun, u1, closed, closeRun,
    u2, started, startRun, tailRun⟩ := run
  let nextEntry := fun block => if block = before.blocks.size then before.stack else entry block
  let nextExit := fun block => if block = before.blocks.size then before.stack else exit block
  have shape := allocateRun
  rw [scope_newBlock_run] at shape
  have headerId := (Prod.mk.inj (Prod.mk.inj shape).1).1
  have allocatedSize : allocated.blocks.size = before.blocks.size + 1 := by
    rw [← (Prod.mk.inj shape).2]
    simp
  have allocatedCurrent : allocated.cur = before.cur := by rw [← (Prod.mk.inj shape).2]
  have allocatedAdvance := allocateAdvance env before _ _ allocateRun
  have allocatedStack := allocatedAdvance.stack
  have allocatedConfig := config.newBlock types env
  rw [allocateRun] at allocatedConfig
  dsimp only at allocatedConfig
  have closedConfig := allocatedConfig.emitTerm (.br header arguments) rfl env (by
    intro destination member
    have same : destination = header := by simpa [Term.successors] using member
    subst destination
    rw [← headerId]
    simp [allocatedStack]) (by
    intro destination member
    have same : destination = header := by simpa [Term.successors] using member
    subst destination
    rw [← headerId, allocatedSize]
    exact Nat.lt_succ_self _)
  rw [closeRun] at closedConfig
  dsimp only at closedConfig
  obtain ⟨headerBody, headerRow, headerOpen⟩ := newBlock_open before env types
  rw [allocateRun] at headerRow
  dsimp only at headerRow
  rw [headerId] at headerRow
  have headerOther : allocated.cur ≠ some header := by
    rw [allocatedCurrent]
    intro current
    have impossible := config.openCurrent.bound header current
    rw [← headerId] at impossible
    exact Nat.lt_irrefl _ impossible
  have closeAdvance := adv_emitTerm closeRun
  have closedRow := closeAdvance.keep header headerBody headerOther headerRow
  have closedStack := closeAdvance.stack.trans allocatedStack
  have startedConfig := closedConfig.setCur header headerBody closedRow headerOpen (by
    rw [← headerId]
    simp [closedStack]) env
  rw [startRun] at startedConfig
  dsimp only at startedConfig
  have prefixAdvance := adv_setCur_step (allocatedAdvance.trans closeAdvance)
    (Or.inr (by rw [← headerId]; exact Nat.le_refl _))
    (by rw [← headerId]; have size := closeAdvance.ext.1; nat_omega) startRun
  have frame : ScopeMapAdvance before entry exit nextEntry nextExit := by
    intro block earlier
    have distinct := Nat.ne_of_lt earlier
    simp [nextEntry, nextExit, distinct]
  have startedContext := ScopeLoopContext.advance context prefixAdvance frame
  have startedCurrent : started.cur = some header := by
    rw [setCur_run] at startRun
    exact congrArg (fun pair => pair.2.cur) startRun.symm
  have startedHeader : nextEntry header = started.stack := by
    rw [← headerId]
    simp [nextEntry, prefixAdvance.stack]
  obtain ⟨afterEntry, afterExit, afterConfig, tailMaps⟩ :=
    tailFlow header params env started nextEntry nextExit startedConfig startedContext
      (by rw [prefixAdvance.stack]; exact stackEq) startedCurrent startedHeader
      (startedConfig.openCurrent.bound header startedCurrent) resultValue after tailRun
  exact ⟨afterEntry, afterExit, afterConfig, frame.trans prefixAdvance tailMaps⟩


#print axioms StorageWalkAction.header
#print axioms StorageWalkConfiguration.loopBack
#print axioms storageWalk_loopBody_flow
#print axioms storageWalk_loopCondition_flow

end Goose.Lower.Validation
