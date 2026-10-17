import Goose.Lower.Validation.StorageWalkControlBase
import Goose.Lower.Validation.StorageWalkFlowFork
import Goose.Lower.Validation.CfgOpenTargets

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageWalkConfiguration.scFork {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : StorageWalkConfiguration slots entry exit before) (isAnd : Bool)
    (value : ValueId) (env : LEnv) :
    StorageWalkConfiguration slots (forkScopeMap before entry) (forkScopeMap before exit)
      (Goose.Lower.scFork isAnd value env before).2 := by
  let first : LS := { before with blocks := before.blocks.push ⟨[], #[]⟩ }
  let firstEntry := fun block => if block = before.blocks.size then before.stack else entry block
  let firstExit := fun block => if block = before.blocks.size then before.stack else exit block
  have one : StorageWalkConfiguration slots firstEntry firstExit first := config.newBlock [] env
  have two := one.newBlock [.data .bool] env
  have neutral : scopeNeutral (.term (scTerm isAnd value before.blocks.size (before.blocks.size + 1))) = true := by
    cases isAnd <;> rfl
  have closed := two.emitTerm (scTerm isAnd value before.blocks.size (before.blocks.size + 1))
      neutral env (by
    intro target member
    cases isAnd <;> simp only [scTerm, Bool.false_eq_true, reduceIte, Term.successors,
      List.mem_cons, List.not_mem_nil, or_false] at member <;>
      rcases member with same | same <;> subst target <;>
      simp [first, firstEntry, newBlock1_run]) (by
    intro target member
    cases isAnd <;> simp only [scTerm, Bool.false_eq_true, reduceIte, Term.successors,
      List.mem_cons, List.not_mem_nil, or_false] at member <;>
      rcases member with same | same <;> subst target <;>
      simp [newBlock1_run, first] <;> nat_omega)
  have entryEq : (fun block => if block = first.blocks.size then first.stack else firstEntry block) =
      forkScopeMap before entry := by simpa [first, firstEntry] using forkScopeMap_nested before entry
  have exitEq : (fun block => if block = first.blocks.size then first.stack else firstExit block) =
      forkScopeMap before exit := by simpa [first, firstExit] using forkScopeMap_nested before exit
  cases isAnd <;>
    simpa only [Goose.Lower.scFork, bind_run, newBlock0_run, newBlock1_run, pure_run,
      scTerm, Bool.false_eq_true, reduceIte, entryEq, exitEq, Array.size_push] using closed

theorem StorageWalkAction.shortCircuit {slots : Array Slot} {stack : List ScopeId}
    {loop : Option LoopCtx} (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (right : StorageWalkAction slots stack loop rhs) :
    StorageWalkAction slots stack loop (Goose.Lower.shortCircuit isAnd value rhs) := by
  refine ⟨advB_shortCircuit isAnd value right.advance, ?_⟩
  intro env before entry exit config context stackEq
  generalize actionRun : Goose.Lower.shortCircuit isAnd value rhs env before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  cases live : before.cur with
  | none =>
    simp only [Goose.Lower.shortCircuit, whenLive_none _ _ _ live] at actionRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj actionRun
    exact ⟨entry, exit, config, ScopeMapAdvance.refl _ _ _⟩
  | some current =>
    simp only [Goose.Lower.shortCircuit, whenLive_some _ _ _ live, bind_eq] at actionRun
    obtain ⟨⟨rb, jb, parameter⟩, forked, forkRun, u1, started, startRun,
      result, evaluated, rhsRun, u2, closed, closeRun, u3, resumed, resumeRun, pureRun⟩ := actionRun
    have ids := scFork_ids forkRun
    obtain ⟨rbId, restIds⟩ := Prod.mk.inj ids.1
    obtain ⟨jbId, parameterId⟩ := Prod.mk.inj restIds
    subst rbId jbId parameterId
    have forkedConfig := config.scFork isAnd value env
    rw [forkRun] at forkedConfig
    dsimp only at forkedConfig
    have forkTargets := scFork_open_targets live (config.openCurrent.bound current live) isAnd value env
    rw [forkRun] at forkTargets
    dsimp only at forkTargets
    obtain ⟨rightBody, rightRow, rightOpen⟩ := forkTargets.1
    obtain ⟨joinBody, joinRow, joinOpen⟩ := forkTargets.2
    have forkAdvance := advB_scFork isAnd value env before _ _ forkRun
    have startedConfig := forkedConfig.setCur before.blocks.size rightBody rightRow rightOpen (by
      simp [forkScopeMap, forkAdvance.stack]) env
    rw [startRun] at startedConfig
    dsimp only at startedConfig
    have startAdvance := adv_setCur_step forkAdvance (Or.inr (Nat.le_refl _))
      (by have size := ids.2; nat_omega) startRun
    have startContext := ScopeLoopContext.advance context startAdvance (forkScopeMap_advance before entry exit)
    obtain ⟨nextEntry, nextExit, evaluatedConfig, rhsMaps⟩ :=
      right.preserves env started (forkScopeMap before entry) (forkScopeMap before exit)
        startedConfig startContext (by rw [startAdvance.stack]; exact stackEq)
    rw [rhsRun] at evaluatedConfig
    dsimp only at evaluatedConfig
    have rhsAdvance := right.advance env started _ _ rhsRun
    have evaluatedStack : evaluated.stack = before.stack := rhsAdvance.stack.trans startAdvance.stack
    have joinOld : before.blocks.size + 1 < started.blocks.size := by
      rw [setCur_blocks startRun]
      have size := ids.2
      nat_omega
    have startedCurrent : started.cur = some before.blocks.size := by
      rw [setCur_run] at startRun
      exact congrArg (fun pair => pair.2.cur) startRun.symm
    have notJoin : started.cur ≠ some (before.blocks.size + 1) := by
      rw [startedCurrent]
      intro same
      have equality := Option.some.inj same
      nat_omega
    have entryJoin := (rhsMaps _ joinOld).1
    have exitJoin := (rhsMaps _ joinOld).2 notJoin
    have joinBound : before.blocks.size + 1 < evaluated.blocks.size :=
      Nat.lt_of_lt_of_le joinOld rhsAdvance.ext.1
    have closedConfig := evaluatedConfig.emitTerm (.br (before.blocks.size + 1) [result]) rfl env (by
      intro destination member
      have same : destination = before.blocks.size + 1 := by simpa [Term.successors] using member
      subst destination
      rw [entryJoin]
      simp [forkScopeMap, evaluatedStack]) (by
      intro destination member
      have same : destination = before.blocks.size + 1 := by simpa [Term.successors] using member
      subst destination
      exact joinBound)
    rw [closeRun] at closedConfig
    dsimp only at closedConfig
    have closeAdvance := adv_emitTerm closeRun
    have evaluatedOther := LS_Adv.otherCurrent rhsAdvance joinOld notJoin
    have evaluatedJoinRow : evaluated.blocks[before.blocks.size + 1]? = some joinBody :=
      rhsAdvance.keep _ joinBody notJoin (by rw [setCur_blocks startRun]; exact joinRow)
    have closedJoinRow : closed.blocks[before.blocks.size + 1]? = some joinBody :=
      closeAdvance.keep _ joinBody evaluatedOther evaluatedJoinRow
    have closedStack : closed.stack = before.stack := closeAdvance.stack.trans evaluatedStack
    have resumedConfig := closedConfig.setCur (before.blocks.size + 1) joinBody closedJoinRow joinOpen (by
      rw [exitJoin]
      simp [forkScopeMap, closedStack]) env
    rw [resumeRun] at resumedConfig
    dsimp only at resumedConfig
    rw [pure_run] at pureRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj pureRun
    exact ⟨nextEntry, nextExit, resumedConfig,
      (forkScopeMap_advance before entry exit).trans startAdvance rhsMaps⟩

theorem StorageWalkAction.ifThen {slots : Array Slot} {stack : List ScopeId}
    {loop : Option LoopCtx} (condition : ValueId) {body : B ValueId}
    (bodyAction : StorageWalkAction slots stack loop body) :
    StorageWalkAction slots stack loop (Goose.Lower.whenLive () fun _ => do
      let (tb, xb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let _ ← body
      Goose.Lower.emitTerm (.br xb [])
      Goose.Lower.setCur (some xb)) := by
  refine ⟨advB_ifS_none_core condition bodyAction.advance, ?_⟩
  intro env before entry exit config context stackEq
  generalize run : (Goose.Lower.whenLive () fun _ => do
      let (tb, xb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let _ ← body
      Goose.Lower.emitTerm (.br xb [])
      Goose.Lower.setCur (some xb)) env before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  cases live : before.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨entry, exit, config, ScopeMapAdvance.refl _ _ _⟩
  | some current =>
    rw [whenLive_some _ _ _ live] at run
    simp only [bind_eq] at run
    obtain ⟨⟨tb, xb⟩, forked, forkRun, u1, started, startRun,
      result, evaluated, bodyRun, u2, closed, closeRun, resumeRun⟩ := run
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
    obtain ⟨joinBody, joinRow, joinOpen⟩ := forkTargets.2
    have forkAdvance := advB_fork condition env before _ _ forkRun
    have startedConfig := forkedConfig.setCur before.blocks.size bodyRow bodyLookup bodyOpen (by
      simp [forkScopeMap, forkAdvance.stack]) env
    rw [startRun] at startedConfig
    dsimp only at startedConfig
    have startAdvance := adv_setCur_step forkAdvance (Or.inr (Nat.le_refl _))
      (by have size := ids.2; nat_omega) startRun
    have startContext := ScopeLoopContext.advance context startAdvance (forkScopeMap_advance before entry exit)
    obtain ⟨nextEntry, nextExit, evaluatedConfig, bodyMaps⟩ :=
      bodyAction.preserves env started (forkScopeMap before entry) (forkScopeMap before exit)
        startedConfig startContext (by rw [startAdvance.stack]; exact stackEq)
    rw [bodyRun] at evaluatedConfig
    dsimp only at evaluatedConfig
    have bodyAdvance := bodyAction.advance env started _ _ bodyRun
    have evaluatedStack : evaluated.stack = before.stack := bodyAdvance.stack.trans startAdvance.stack
    have joinOld : before.blocks.size + 1 < started.blocks.size := by
      rw [setCur_blocks startRun]
      have size := ids.2
      nat_omega
    have startedCurrent : started.cur = some before.blocks.size := by
      rw [setCur_run] at startRun
      exact congrArg (fun pair => pair.2.cur) startRun.symm
    have notJoin : started.cur ≠ some (before.blocks.size + 1) := by
      rw [startedCurrent]
      intro same
      have equality := Option.some.inj same
      nat_omega
    have entryJoin := (bodyMaps _ joinOld).1
    have exitJoin := (bodyMaps _ joinOld).2 notJoin
    have joinBound : before.blocks.size + 1 < evaluated.blocks.size :=
      Nat.lt_of_lt_of_le joinOld bodyAdvance.ext.1
    have closedConfig := evaluatedConfig.emitTerm (.br (before.blocks.size + 1) []) rfl env (by
      intro destination member
      have same : destination = before.blocks.size + 1 := by simpa [Term.successors] using member
      subst destination
      rw [entryJoin]
      simp [forkScopeMap, evaluatedStack]) (by
      intro destination member
      have same : destination = before.blocks.size + 1 := by simpa [Term.successors] using member
      subst destination
      exact joinBound)
    rw [closeRun] at closedConfig
    dsimp only at closedConfig
    have closeAdvance := adv_emitTerm closeRun
    have evaluatedOther := LS_Adv.otherCurrent bodyAdvance joinOld notJoin
    have evaluatedJoinRow : evaluated.blocks[before.blocks.size + 1]? = some joinBody :=
      bodyAdvance.keep _ joinBody notJoin (by rw [setCur_blocks startRun]; exact joinRow)
    have closedJoinRow : closed.blocks[before.blocks.size + 1]? = some joinBody :=
      closeAdvance.keep _ joinBody evaluatedOther evaluatedJoinRow
    have closedStack : closed.stack = before.stack := closeAdvance.stack.trans evaluatedStack
    have resumedConfig := closedConfig.setCur (before.blocks.size + 1) joinBody closedJoinRow joinOpen (by
      rw [exitJoin]
      simp [forkScopeMap, closedStack]) env
    rw [resumeRun] at resumedConfig
    dsimp only at resumedConfig
    exact ⟨nextEntry, nextExit, resumedConfig,
      (forkScopeMap_advance before entry exit).trans startAdvance bodyMaps⟩

theorem StorageWalkAction.assertCore {slots : Array Slot} {stack : List ScopeId}
    {loop : Option LoopCtx} (condition : ValueId) (origin : OriginId) :
    StorageWalkAction slots stack loop (Goose.Lower.whenLive () fun _ => do
      let (pass, fail) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some fail)
      Goose.Lower.emitTerm (.abort .assert (some origin))
      Goose.Lower.setCur (some pass)) := by
  refine ⟨advB_assert_core condition origin, ?_⟩
  intro env before entry exit config context stackEq
  generalize run : (Goose.Lower.whenLive () fun _ => do
      let (pass, fail) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some fail)
      Goose.Lower.emitTerm (.abort .assert (some origin))
      Goose.Lower.setCur (some pass)) env before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  cases live : before.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨entry, exit, config, ScopeMapAdvance.refl _ _ _⟩
  | some current =>
    rw [whenLive_some _ _ _ live] at run
    simp only [bind_eq] at run
    obtain ⟨⟨pass, fail⟩, forked, forkRun, u1, started, startRun, u2, closed, closeRun, resumeRun⟩ := run
    have ids := fork_ids forkRun
    obtain ⟨passId, failId⟩ := Prod.mk.inj ids.1
    subst passId failId
    have forkedConfig := config.fork condition env
    rw [forkRun] at forkedConfig
    dsimp only at forkedConfig
    have forkTargets := fork_open_targets live (config.openCurrent.bound current live) condition env
    rw [forkRun] at forkTargets
    dsimp only at forkTargets
    obtain ⟨passBody, passRow, passOpen⟩ := forkTargets.1
    obtain ⟨failBody, failRow, failOpen⟩ := forkTargets.2
    have forkAdvance := advB_fork condition env before _ _ forkRun
    have startedConfig := forkedConfig.setCur (before.blocks.size + 1) failBody failRow failOpen (by
      simp [forkScopeMap, forkAdvance.stack]) env
    rw [startRun] at startedConfig
    dsimp only at startedConfig
    have startedStack : started.stack = before.stack := by
      rw [setCur_run] at startRun
      rw [← (Prod.mk.inj startRun).2]
      exact forkAdvance.stack
    have closedConfig := startedConfig.emitTerm (.abort .assert (some origin)) rfl env
      (by intro target member; simp [Term.successors] at member)
      (by intro target member; simp [Term.successors] at member)
    rw [closeRun] at closedConfig
    dsimp only at closedConfig
    have closeAdvance := adv_emitTerm closeRun
    have closedStack := closeAdvance.stack.trans startedStack
    have startedPass : started.blocks[before.blocks.size]? = some passBody := by
      rw [setCur_blocks startRun]
      exact passRow
    have other : started.cur ≠ some before.blocks.size := by
      rw [setCur_run] at startRun
      rw [← (Prod.mk.inj startRun).2]
      simp
    have closedPass := closeAdvance.keep _ passBody other startedPass
    have resumedConfig := closedConfig.setCur before.blocks.size passBody closedPass passOpen (by
      simp [forkScopeMap, closedStack]) env
    rw [resumeRun] at resumedConfig
    dsimp only at resumedConfig
    exact ⟨forkScopeMap before entry, forkScopeMap before exit, resumedConfig,
      forkScopeMap_advance before entry exit⟩

end Goose.Lower.Validation
