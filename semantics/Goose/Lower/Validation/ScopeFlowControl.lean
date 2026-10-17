import Goose.Lower.Validation.ScopeFlow
import Goose.Lower.Validation.CfgOpenTargets

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem forkScopeMap_nested (before : LS) (old : BlockId → List ScopeId) :
    (fun block => if block = before.blocks.size + 1 then before.stack
      else if block = before.blocks.size then before.stack else old block) = forkScopeMap before old := by
  funext block
  by_cases first : block = before.blocks.size <;> by_cases second : block = before.blocks.size + 1 <;>
    simp [forkScopeMap, first, second]

theorem ScopeConfiguration.fork {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : ScopeConfiguration parents entry exit before) (condition : ValueId) (env : LEnv) :
    ScopeConfiguration parents (forkScopeMap before entry) (forkScopeMap before exit)
      (Goose.Lower.fork condition env before).2 := by
  let first : LS := { before with blocks := before.blocks.push ⟨[], #[]⟩ }
  let second : LS := { before with blocks := (before.blocks.push ⟨[], #[]⟩).push ⟨[], #[]⟩ }
  let firstEntry := fun block => if block = before.blocks.size then before.stack else entry block
  let firstExit := fun block => if block = before.blocks.size then before.stack else exit block
  have one : ScopeConfiguration parents firstEntry firstExit first := config.newBlock [] env
  have two := one.newBlock [] env
  have closed := two.emitTerm (.condbr condition before.blocks.size [] (before.blocks.size + 1) []) rfl env (by
    intro target member
    simp only [Term.successors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same <;> subst target <;>
      simp [first, firstEntry, newBlock0_run]) (by
    intro target member
    simp only [Term.successors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same <;> subst target <;>
      simp [newBlock0_run, first] <;> nat_omega)
  have entryEq : (fun block => if block = first.blocks.size then first.stack else firstEntry block) =
      forkScopeMap before entry := by simpa [first, firstEntry] using forkScopeMap_nested before entry
  have exitEq : (fun block => if block = first.blocks.size then first.stack else firstExit block) =
      forkScopeMap before exit := by simpa [first, firstExit] using forkScopeMap_nested before exit
  rw [entryEq, exitEq] at closed
  simp only [Goose.Lower.fork, bind_run, newBlock0_run, pure_run]
  simpa only [newBlock0_run, first, Array.size_push] using closed

theorem ScopeConfiguration.scFork {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (config : ScopeConfiguration parents entry exit before) (isAnd : Bool) (value : ValueId) (env : LEnv) :
    ScopeConfiguration parents (forkScopeMap before entry) (forkScopeMap before exit)
      (Goose.Lower.scFork isAnd value env before).2 := by
  let first : LS := { before with blocks := before.blocks.push ⟨[], #[]⟩ }
  let firstEntry := fun block => if block = before.blocks.size then before.stack else entry block
  let firstExit := fun block => if block = before.blocks.size then before.stack else exit block
  have one : ScopeConfiguration parents firstEntry firstExit first := config.newBlock [] env
  have two := one.newBlock [.data .bool] env
  have neutral : scopeNeutral (.term (scTerm isAnd value before.blocks.size (before.blocks.size + 1))) = true := by
    cases isAnd <;> rfl
  have closed := two.emitTerm (scTerm isAnd value before.blocks.size (before.blocks.size + 1)) neutral env (by
    intro target member
    cases isAnd <;> simp only [scTerm, Bool.false_eq_true, reduceIte, Term.successors,
      List.mem_cons, List.not_mem_nil, or_false] at member <;>
      rcases member with same | same <;> subst target <;> simp [first, firstEntry, newBlock1_run]) (by
    intro target member
    cases isAnd <;> simp only [scTerm, Bool.false_eq_true, reduceIte, Term.successors,
      List.mem_cons, List.not_mem_nil, or_false] at member <;>
      rcases member with same | same <;> subst target <;> simp [newBlock1_run, first] <;> nat_omega)
  have entryEq : (fun block => if block = first.blocks.size then first.stack else firstEntry block) =
      forkScopeMap before entry := by simpa [first, firstEntry] using forkScopeMap_nested before entry
  have exitEq : (fun block => if block = first.blocks.size then first.stack else firstExit block) =
      forkScopeMap before exit := by simpa [first, firstExit] using forkScopeMap_nested before exit
  cases isAnd <;>
    simpa only [Goose.Lower.scFork, bind_run, newBlock0_run, newBlock1_run, pure_run,
      scTerm, Bool.false_eq_true, reduceIte, entryEq, exitEq, Array.size_push] using closed

theorem ScopeFlowAction.shortCircuit {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    {loop : Option LoopCtx} (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (right : ScopeFlowAction parents parent loop rhs) :
    ScopeFlowAction parents parent loop (Goose.Lower.shortCircuit isAnd value rhs) := by
  refine ⟨ScopeAction.shortCircuit isAnd value right.scopes, ?_⟩
  intro env before entry exit config context head
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
        startedConfig startContext (by rw [startAdvance.stack]; exact head)
    rw [rhsRun] at evaluatedConfig
    dsimp only at evaluatedConfig
    have rhsAdvance := right.scopes.advance env started _ _ rhsRun
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

theorem ScopeFlowAction.ifThen {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    {loop : Option LoopCtx} (condition : ValueId) {body : B ValueId}
    (bodyAction : ScopeFlowAction parents parent loop body) :
    ScopeFlowAction parents parent loop (whenLive () fun _ => do
      let (tb, xb) ← fork condition
      setCur (some tb)
      let _ ← body
      emitTerm (.br xb [])
      setCur (some xb)) := by
  refine ⟨ScopeAction.ifThen condition bodyAction.scopes, ?_⟩
  intro env before entry exit config context head
  generalize run : (whenLive () fun _ => do
      let (tb, xb) ← fork condition
      setCur (some tb)
      let _ ← body
      emitTerm (.br xb [])
      setCur (some xb)) env before = result
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
        startedConfig startContext (by rw [startAdvance.stack]; exact head)
    rw [bodyRun] at evaluatedConfig
    dsimp only at evaluatedConfig
    have bodyAdvance := bodyAction.scopes.advance env started _ _ bodyRun
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


theorem ScopeFlowAction.whenLive {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    {loop : Option LoopCtx} (default : α) {body : BlockId → B α}
    (bodyAction : ∀ block, ScopeFlowAction parents parent loop (body block)) :
    ScopeFlowAction parents parent loop (Goose.Lower.whenLive default body) := by
  unfold Goose.Lower.whenLive
  apply (ScopeFlowAction.curBlock parents parent loop).bind
  intro current
  cases current with
  | none => exact ScopeFlowAction.pure parents parent loop default
  | some block => exact bodyAction block

theorem ScopeFlowAction.assertCore (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (loop : Option LoopCtx) (condition : ValueId) (origin : OriginId) :
    ScopeFlowAction parents parent loop (Goose.Lower.whenLive () fun _ => do
      let (pass, fail) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some fail)
      Goose.Lower.emitTerm (.abort .assert (some origin))
      Goose.Lower.setCur (some pass)) := by
  refine ⟨ScopeAction.assertCore parents parent condition origin, ?_⟩
  intro env before entry exit config context head
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
