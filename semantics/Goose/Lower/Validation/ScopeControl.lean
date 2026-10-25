import Goose.Lower.Validation.ScopeActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def forkScopeMap (before : LS) (old : BlockId → List ScopeId) : BlockId → List ScopeId :=
  fun block => if block = before.blocks.size ∨ block = before.blocks.size + 1 then before.stack else old block

theorem forkScopeMap_old (before : LS) (old : BlockId → List ScopeId) (block : BlockId)
    (earlier : block < before.blocks.size) : forkScopeMap before old block = old block := by
  have first : block ≠ before.blocks.size := Nat.ne_of_lt earlier
  have second : block ≠ before.blocks.size + 1 := by nat_omega
  simp [forkScopeMap, first, second]

theorem forkScopeMap_advance (before : LS) (entry exit : BlockId → List ScopeId) :
    ScopeMapAdvance before entry exit (forkScopeMap before entry) (forkScopeMap before exit) := by
  intro block earlier
  exact ⟨forkScopeMap_old before entry block earlier,
    fun _ => forkScopeMap_old before exit block earlier⟩

theorem ScopeBuilder.fork {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : ScopeBuilder parents entry exit before) (bound : ScopeLiveBound before)
    (condition : ValueId) (env : LEnv) (block : BlockId) (live : before.cur = some block) :
    ScopeBuilder parents (forkScopeMap before entry) (forkScopeMap before exit)
      (Goose.Lower.fork condition env before).2 := by
  let first : LS := { before with blocks := before.blocks.push ⟨[], #[]⟩ }
  let second : LS := { before with blocks := (before.blocks.push ⟨[], #[]⟩).push ⟨[], #[]⟩ }
  let firstEntry := fun other => if other = before.blocks.size then before.stack else entry other
  let firstExit := fun other => if other = before.blocks.size then before.stack else exit other
  have one : ScopeBuilder parents firstEntry firstExit first := valid.push bound [] before.vals
  have secondBound : ScopeLiveBound first := by
    intro other current
    simpa [first] using Nat.lt_succ_of_lt (bound other current)
  have two := one.push secondBound [] before.vals
  have closed := two.emitNeutralTerm (.condbr condition before.blocks.size [] (before.blocks.size + 1) []) rfl env
  have entryEq : (fun other => if other = first.blocks.size then first.stack else firstEntry other) =
      forkScopeMap before entry := by
    funext other
    by_cases firstId : other = before.blocks.size <;>
      by_cases secondId : other = before.blocks.size + 1 <;>
      simp [first, firstEntry, forkScopeMap, firstId, secondId]
  have exitEq : (fun other => if other = first.blocks.size then first.stack else firstExit other) =
      forkScopeMap before exit := by
    funext other
    by_cases firstId : other = before.blocks.size <;>
      by_cases secondId : other = before.blocks.size + 1 <;>
      simp [first, firstExit, forkScopeMap, firstId, secondId]
  rw [fork_run condition env live]
  rw [emitTerm_run _ _ (ls := second) live] at closed
  simpa only [entryEq, exitEq] using closed

theorem ScopeBuilder.scFork {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : ScopeBuilder parents entry exit before) (bound : ScopeLiveBound before)
    (isAnd : Bool) (value : ValueId) (env : LEnv) (block : BlockId) (live : before.cur = some block) :
    ScopeBuilder parents (forkScopeMap before entry) (forkScopeMap before exit)
      (Goose.Lower.scFork isAnd value env before).2 := by
  let first : LS := { before with blocks := before.blocks.push ⟨[], #[]⟩ }
  let second : LS := { before with blocks := (before.blocks.push ⟨[], #[]⟩).push ⟨[(before.vals.size, .data .bool)], #[]⟩, vals := before.vals.push (some (.data .bool)) }
  let firstEntry := fun other => if other = before.blocks.size then before.stack else entry other
  let firstExit := fun other => if other = before.blocks.size then before.stack else exit other
  have one : ScopeBuilder parents firstEntry firstExit first := valid.push bound [] before.vals
  have secondBound : ScopeLiveBound first := by
    intro other current
    simpa [first] using Nat.lt_succ_of_lt (bound other current)
  have two := one.push secondBound [(before.vals.size, .data .bool)] (before.vals.push (some (.data .bool)))
  have neutral : scopeNeutral (.term (scTerm isAnd value before.blocks.size (before.blocks.size + 1))) = true := by
    cases isAnd <;> rfl
  have closed := two.emitNeutralTerm (scTerm isAnd value before.blocks.size (before.blocks.size + 1)) neutral env
  have entryEq : (fun other => if other = first.blocks.size then first.stack else firstEntry other) =
      forkScopeMap before entry := by
    funext other
    by_cases firstId : other = before.blocks.size <;>
      by_cases secondId : other = before.blocks.size + 1 <;>
      simp [first, firstEntry, forkScopeMap, firstId, secondId]
  have exitEq : (fun other => if other = first.blocks.size then first.stack else firstExit other) =
      forkScopeMap before exit := by
    funext other
    by_cases firstId : other = before.blocks.size <;>
      by_cases secondId : other = before.blocks.size + 1 <;>
      simp [first, firstExit, forkScopeMap, firstId, secondId]
  rw [scFork_run isAnd value env live]
  rw [emitTerm_run _ _ (ls := second) live] at closed
  simpa only [entryEq, exitEq] using closed

theorem ScopeAction.shortCircuit {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    (isAnd : Bool) (value : ValueId) {rhs : B ValueId} (right : ScopeAction parents parent rhs) :
    ScopeAction parents parent (Goose.Lower.shortCircuit isAnd value rhs) := by
  refine ⟨advB_shortCircuit isAnd value right.advance, ?_⟩
  intro env before entry exit valid bound head
  generalize actionRun : Goose.Lower.shortCircuit isAnd value rhs env before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  cases live : before.cur with
  | none =>
    simp only [Goose.Lower.shortCircuit, whenLive_none _ _ _ live] at actionRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj actionRun
    exact ⟨entry, exit, valid, ScopeMapAdvance.refl _ _ _⟩
  | some current =>
    simp only [Goose.Lower.shortCircuit, whenLive_some _ _ _ live, bind_eq] at actionRun
    obtain ⟨⟨rb, jb, parameter⟩, forked, forkRun, u1, started, startRun,
      result, evaluated, rhsRun, u2, closed, closeRun, u3, resumed, resumeRun, pureRun⟩ := actionRun
    have ids := scFork_ids forkRun
    obtain ⟨rbId, restIds⟩ := Prod.mk.inj ids.1
    obtain ⟨jbId, parameterId⟩ := Prod.mk.inj restIds
    subst rbId jbId parameterId
    have forkedValid := valid.scFork bound isAnd value env current live
    rw [forkRun] at forkedValid
    dsimp only at forkedValid
    have forkAdvance := advB_scFork isAnd value env before _ _ forkRun
    have forkStack := forkAdvance.stack
    have startedValid := forkedValid.setCur (some before.blocks.size) (by
      intro block same
      cases same
      simp [forkScopeMap, forkStack]) env
    rw [startRun] at startedValid
    dsimp only at startedValid
    have startAdvance := adv_setCur_step forkAdvance (Or.inr (Nat.le_refl _))
      (by have size := ids.2; nat_omega) startRun
    have startBound := bound.advance startAdvance
    have startHead : started.stack.head? = parent := by rw [startAdvance.stack]; exact head
    obtain ⟨nextEntry, nextExit, evaluatedValid, rhsMaps⟩ :=
      right.preserves env started (forkScopeMap before entry) (forkScopeMap before exit)
        startedValid startBound startHead
    rw [rhsRun] at evaluatedValid
    dsimp only at evaluatedValid
    have rhsAdvance := right.advance env started _ _ rhsRun
    have evaluatedStack : evaluated.stack = before.stack := rhsAdvance.stack.trans startAdvance.stack
    have closedValid := evaluatedValid.emitNeutralTerm (.br (before.blocks.size + 1) [result]) rfl env
    rw [closeRun] at closedValid
    dsimp only at closedValid
    have closeAdvance := adv_emitTerm closeRun
    have closedStack : closed.stack = before.stack := closeAdvance.stack.trans evaluatedStack
    have joinOld : before.blocks.size + 1 < started.blocks.size := by
      have unchanged := setCur_blocks startRun
      rw [unchanged]
      have size := ids.2
      nat_omega
    have notJoin : started.cur ≠ some (before.blocks.size + 1) := by
      rw [setCur_run] at startRun
      obtain ⟨_, state⟩ := Prod.mk.inj startRun
      rw [← state]
      dsimp only
      intro same
      have equality := Option.some.inj same
      nat_omega
    have joinExit := (rhsMaps _ joinOld).2 notJoin
    have resumedValid := closedValid.setCur (some (before.blocks.size + 1)) (by
      intro block same
      cases same
      rw [joinExit]
      simp [forkScopeMap, closedStack]) env
    rw [resumeRun] at resumedValid
    dsimp only at resumedValid
    rw [pure_run] at pureRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj pureRun
    exact ⟨nextEntry, nextExit, resumedValid,
      (forkScopeMap_advance before entry exit).trans startAdvance rhsMaps⟩

theorem ScopeBuilder.patchBrs {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} (join : BlockId) (live : List (BlockId × ValueId))
    (env : LEnv) (before : LS) (valid : ScopeBuilder parents entry exit before) :
    ScopeBuilder parents entry exit (Goose.Lower.patchBrs join live env before).2 ∧
      (Goose.Lower.patchBrs join live env before).2.stack = before.stack ∧
      (Goose.Lower.patchBrs join live env before).2.cur = before.cur := by
  induction live generalizing before with
  | nil => exact ⟨valid, rfl, rfl⟩
  | cons block live ih =>
    simp only [Goose.Lower.patchBrs, bind_run]
    have rest := ih (Goose.Lower.patchTerm block.1 (.br join [block.2]) env before).2
      (valid.patchNeutralTerm block.1 (.br join [block.2]) rfl env)
    simpa only [patchTerm_run] using rest

theorem ScopeBuilder.patchBrs0 {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} (join : BlockId) (live : List BlockId)
    (env : LEnv) (before : LS) (valid : ScopeBuilder parents entry exit before) :
    ScopeBuilder parents entry exit (Goose.Lower.patchBrs0 join live env before).2 ∧
      (Goose.Lower.patchBrs0 join live env before).2.stack = before.stack ∧
      (Goose.Lower.patchBrs0 join live env before).2.cur = before.cur := by
  induction live generalizing before with
  | nil => exact ⟨valid, rfl, rfl⟩
  | cons block live ih =>
    simp only [Goose.Lower.patchBrs0, bind_run]
    have rest := ih (Goose.Lower.patchTerm block (.br join []) env before).2
      (valid.patchNeutralTerm block (.br join []) rfl env)
    simpa only [patchTerm_run] using rest

theorem scope_joinValue {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {env : LEnv} {before after : LS}
    (valid : ScopeBuilder parents entry exit before) (bound : ScopeLiveBound before)
    {endT endF : Option BlockId} {valueT valueF result : ValueId}
    (run : Goose.Lower.joinValue endT valueT endF valueF env before = (result, after)) :
    ∃ nextEntry nextExit, ScopeBuilder parents nextEntry nextExit after ∧
      ScopeMapAdvance before entry exit nextEntry nextExit := by
  unfold Goose.Lower.joinValue at run
  have key : ∀ {live : List (BlockId × ValueId)},
      (do
        let type ← valTy (live.headD (0, 0)).2
        let (join, params) ← Goose.Lower.newBlock [type]
        Goose.Lower.patchBrs join live
        Goose.Lower.setCur (some join)
        Pure.pure (params.headD 0) : B ValueId) env before = (result, after) →
      ∃ nextEntry nextExit, ScopeBuilder parents nextEntry nextExit after ∧
        ScopeMapAdvance before entry exit nextEntry nextExit := by
    intro live run
    simp only [bind_eq] at run
    obtain ⟨type, observed, observeRun, ⟨join, params⟩, allocated, allocateRun,
      u, patched, patchRun, u2, resumed, resumeRun, pureRun⟩ := run
    have observedSame := valTy_eq observeRun
    subst observedSame
    let nextEntry := fun block => if block = observed.blocks.size then observed.stack else entry block
    let nextExit := fun block => if block = observed.blocks.size then observed.stack else exit block
    have allocatedValid := valid.newBlock bound env [type]
    rw [allocateRun] at allocatedValid
    dsimp only at allocatedValid
    have patchedFacts := allocatedValid.patchBrs join live env allocated
    rw [patchRun] at patchedFacts
    dsimp only at patchedFacts
    have shape := allocateRun
    rw [newBlock1_run] at shape
    have joinId := (Prod.mk.inj (Prod.mk.inj shape).1).1
    have allocatedStack : allocated.stack = observed.stack := (adv_newBlock1 allocateRun).stack
    have patchedStack : patched.stack = observed.stack := patchedFacts.2.1.trans allocatedStack
    have resumedValid := patchedFacts.1.setCur (some join) (by
      intro block same
      cases same
      rw [← joinId]
      simp [patchedStack]) env
    rw [resumeRun] at resumedValid
    dsimp only at resumedValid
    rw [pure_run] at pureRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj pureRun
    refine ⟨nextEntry, nextExit, resumedValid, ?_⟩
    intro block earlier
    have distinct : block ≠ observed.blocks.size := Nat.ne_of_lt earlier
    simp [nextEntry, nextExit, distinct]
  cases endT <;> cases endF
  · simp only [bind_eq] at run
    obtain ⟨u, closed, closeRun, pureRun⟩ := run
    have closedValid := valid.setCur none (by simp) env
    rw [closeRun] at closedValid
    dsimp only at closedValid
    rw [pure_run] at pureRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj pureRun
    exact ⟨entry, exit, closedValid, ScopeMapAdvance.refl _ _ _⟩
  · exact key run
  · exact key run
  · exact key run

theorem scope_joinValue_recorded {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {env : LEnv} {before after : LS}
    (valid : ScopeBuilder parents entry exit before) (bound : ScopeLiveBound before)
    {endT endF : Option BlockId} {valueT valueF result : ValueId} (sourceScope : ScopeId)
    (run : (do
      let joined ← Goose.Lower.joinValue endT valueT endF valueF
      Goose.Lower.recordValueRootRecipe joined sourceScope
      (Pure.pure joined : B ValueId)) env before = (result, after)) :
    ∃ nextEntry nextExit, ScopeBuilder parents nextEntry nextExit after ∧
      ScopeMapAdvance before entry exit nextEntry nextExit := by
  simp only [bind_eq] at run
  obtain ⟨joined, joinedState, joinRun, _, recordedState, recipeRun, finalRun⟩ := run
  obtain ⟨nextEntry, nextExit, joinedValid, maps⟩ := scope_joinValue valid bound joinRun
  rw [recordValueRootRecipe_run] at recipeRun
  have stateEq := (Prod.mk.inj recipeRun).2
  have afterEq := (pure_eq.mp finalRun).2.symm
  have recipeBlocks : recordedState.blocks = joinedState.blocks := by
    simpa using (congrArg LS.blocks stateEq).symm
  have recipeCurrent : recordedState.cur = joinedState.cur := by
    simpa using (congrArg LS.cur stateEq).symm
  have recipeStack : recordedState.stack = joinedState.stack := by
    simpa using (congrArg LS.stack stateEq).symm
  have recordedValid : ScopeBuilder parents nextEntry nextExit recordedState := by
    constructor
    · intro block body row
      have joinedRow : joinedState.blocks[block]? = some body := by
        rw [recipeBlocks] at row
        exact row
      exact joinedValid.traces block body joinedRow
    · intro block live
      have joinedLive : joinedState.cur = some block := by
        rw [recipeCurrent] at live
        exact live
      rw [recipeStack]
      exact joinedValid.current block joinedLive
  rw [afterEq]
  exact ⟨nextEntry, nextExit, recordedValid, maps⟩

theorem scope_joinArms {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {env : LEnv} {before after : LS}
    (valid : ScopeBuilder parents entry exit before) (bound : ScopeLiveBound before)
    {endT endF : Option BlockId} {result : Unit}
    (run : Goose.Lower.joinArms endT endF env before = (result, after)) :
    ∃ nextEntry nextExit, ScopeBuilder parents nextEntry nextExit after ∧
      ScopeMapAdvance before entry exit nextEntry nextExit := by
  unfold Goose.Lower.joinArms at run
  have key : ∀ {live : List BlockId},
      (do
        let (join, _) ← Goose.Lower.newBlock []
        Goose.Lower.patchBrs0 join live
        Goose.Lower.setCur (some join) : B Unit) env before = (result, after) →
      ∃ nextEntry nextExit, ScopeBuilder parents nextEntry nextExit after ∧
        ScopeMapAdvance before entry exit nextEntry nextExit := by
    intro live run
    simp only [bind_eq] at run
    obtain ⟨⟨join, params⟩, allocated, allocateRun, u, patched, patchRun, resumeRun⟩ := run
    let nextEntry := fun block => if block = before.blocks.size then before.stack else entry block
    let nextExit := fun block => if block = before.blocks.size then before.stack else exit block
    have allocatedValid := valid.newBlock bound env []
    rw [allocateRun] at allocatedValid
    dsimp only at allocatedValid
    have patchedFacts := allocatedValid.patchBrs0 join live env allocated
    rw [patchRun] at patchedFacts
    dsimp only at patchedFacts
    have shape := allocateRun
    rw [newBlock0_run] at shape
    have joinId := (Prod.mk.inj (Prod.mk.inj shape).1).1
    have allocatedStack : allocated.stack = before.stack := (adv_newBlock0 allocateRun).stack
    have patchedStack : patched.stack = before.stack := patchedFacts.2.1.trans allocatedStack
    have resumedValid := patchedFacts.1.setCur (some join) (by
      intro block same
      cases same
      rw [← joinId]
      simp [patchedStack]) env
    rw [resumeRun] at resumedValid
    dsimp only at resumedValid
    refine ⟨nextEntry, nextExit, resumedValid, ?_⟩
    intro block earlier
    have distinct : block ≠ before.blocks.size := Nat.ne_of_lt earlier
    simp [nextEntry, nextExit, distinct]
  cases endT <;> cases endF
  · dsimp only at run
    have closedValid := valid.setCur none (by simp) env
    rw [run] at closedValid
    dsimp only at closedValid
    exact ⟨entry, exit, closedValid, ScopeMapAdvance.refl _ _ _⟩
  · exact key run
  · exact key run
  · exact key run

theorem scope_ifBranches {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    (condition : ValueId) {first second : B ValueId}
    (firstAction : ScopeAction parents parent first) (secondAction : ScopeAction parents parent second)
    (tail : Option BlockId → ValueId → Option BlockId → ValueId → B α)
    (tailPreserves : ∀ endT valueT endF valueF env before entry exit,
      ScopeBuilder parents entry exit before → ScopeLiveBound before →
      ∀ result after, tail endT valueT endF valueF env before = (result, after) →
      ∃ nextEntry nextExit, ScopeBuilder parents nextEntry nextExit after ∧
        ScopeMapAdvance before entry exit nextEntry nextExit)
    (env : LEnv) (before : LS) (entry exit : BlockId → List ScopeId)
    (valid : ScopeBuilder parents entry exit before) (bound : ScopeLiveBound before)
    (head : before.stack.head? = parent) (current : BlockId) (live : before.cur = some current)
    {result : α} {after : LS}
    (run : (do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← first
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← second
      let endF ← Goose.Lower.curBlock
      tail endT valueT endF valueF) env before = (result, after)) :
    ∃ nextEntry nextExit, ScopeBuilder parents nextEntry nextExit after ∧
      ScopeMapAdvance before entry exit nextEntry nextExit := by
  simp only [bind_eq] at run
  obtain ⟨⟨tb, eb⟩, forked, forkRun, u1, firstStart, firstStartRun,
    valueT, firstEnd, firstRun, endT, firstRead, firstReadRun, u2, secondStart, secondStartRun,
    valueF, secondEnd, secondRun, endF, secondRead, secondReadRun, tailRun⟩ := run
  have ids := fork_ids forkRun
  obtain ⟨tbId, ebId⟩ := Prod.mk.inj ids.1
  subst tbId ebId
  have forkedValid := valid.fork bound condition env current live
  rw [forkRun] at forkedValid
  dsimp only at forkedValid
  have forkAdvance := advB_fork condition env before _ _ forkRun
  have firstStartValid := forkedValid.setCur (some before.blocks.size) (by
    intro block same
    cases same
    simp [forkScopeMap, forkAdvance.stack]) env
  rw [firstStartRun] at firstStartValid
  dsimp only at firstStartValid
  have firstStartAdvance := adv_setCur_step forkAdvance (Or.inr (Nat.le_refl _))
    (by have size := ids.2; nat_omega) firstStartRun
  obtain ⟨firstEntry, firstExit, firstEndValid, firstMaps⟩ :=
    firstAction.preserves env firstStart (forkScopeMap before entry) (forkScopeMap before exit)
      firstStartValid (bound.advance firstStartAdvance) (by rw [firstStartAdvance.stack]; exact head)
  rw [firstRun] at firstEndValid
  dsimp only at firstEndValid
  have firstAdvance := firstAction.advance env firstStart _ _ firstRun
  have firstEndAdvance := firstStartAdvance.trans firstAdvance
  obtain ⟨endTEqual, firstReadEqual⟩ := curBlock_eq firstReadRun
  subst firstRead
  have secondOld : before.blocks.size + 1 < firstStart.blocks.size := by
    rw [setCur_blocks firstStartRun]
    have size := ids.2
    nat_omega
  have firstCurrent : firstStart.cur = some before.blocks.size := by
    rw [setCur_run] at firstStartRun
    exact congrArg (fun pair => pair.2.cur) firstStartRun.symm
  have notSecond : firstStart.cur ≠ some (before.blocks.size + 1) := by
    rw [firstCurrent]
    intro same
    have equality := Option.some.inj same
    nat_omega
  have secondExit := (firstMaps _ secondOld).2 notSecond
  have firstStack : firstEnd.stack = before.stack := firstEndAdvance.stack
  have secondStartValid := firstEndValid.setCur (some (before.blocks.size + 1)) (by
    intro block same
    cases same
    rw [secondExit]
    simp [forkScopeMap, firstStack]) env
  rw [secondStartRun] at secondStartValid
  dsimp only at secondStartValid
  have secondAllocated : before.blocks.size + 1 < firstEnd.blocks.size :=
    Nat.lt_of_lt_of_le secondOld firstAdvance.ext.1
  have secondStartAdvance := adv_setCur_step firstEndAdvance
    (Or.inr (Nat.le_succ_of_le (Nat.le_refl _))) secondAllocated secondStartRun
  obtain ⟨secondEntry, secondExit, secondEndValid, secondMaps⟩ :=
    secondAction.preserves env secondStart firstEntry firstExit secondStartValid
      (bound.advance secondStartAdvance) (by rw [secondStartAdvance.stack]; exact head)
  rw [secondRun] at secondEndValid
  dsimp only at secondEndValid
  have secondAdvance := secondAction.advance env secondStart _ _ secondRun
  have secondEndAdvance := secondStartAdvance.trans secondAdvance
  obtain ⟨endFEqual, secondReadEqual⟩ := curBlock_eq secondReadRun
  subst secondRead
  obtain ⟨afterEntry, afterExit, afterValid, tailMaps⟩ :=
    tailPreserves endT valueT endF valueF env secondEnd secondEntry secondExit
      secondEndValid (bound.advance secondEndAdvance) result after tailRun
  have firstFrame := (forkScopeMap_advance before entry exit).trans firstStartAdvance firstMaps
  have secondFrame := firstFrame.trans secondStartAdvance secondMaps
  exact ⟨afterEntry, afterExit, afterValid, secondFrame.trans secondEndAdvance tailMaps⟩

theorem ScopeAction.ifValue {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    (condition : ValueId) (sourceScope : ScopeId) {first second : B ValueId}
    (firstAction : ScopeAction parents parent first) (secondAction : ScopeAction parents parent second) :
    ScopeAction parents parent (Goose.Lower.whenLive 0 fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← first
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← second
      let endF ← Goose.Lower.curBlock
      let result ← Goose.Lower.joinValue endT valueT endF valueF
      Goose.Lower.recordValueRootRecipe result sourceScope
      (Pure.pure result : B ValueId)) := by
  refine ⟨advB_ifE_core condition sourceScope firstAction.advance secondAction.advance, ?_⟩
  intro env before entry exit valid bound head
  generalize run : (Goose.Lower.whenLive 0 fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← first
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← second
      let endF ← Goose.Lower.curBlock
      let result ← Goose.Lower.joinValue endT valueT endF valueF
      Goose.Lower.recordValueRootRecipe result sourceScope
      (Pure.pure result : B ValueId)) env before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  cases live : before.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨entry, exit, valid, ScopeMapAdvance.refl _ _ _⟩
  | some current =>
    rw [whenLive_some _ _ _ live] at run
    exact scope_ifBranches condition firstAction secondAction
      (fun endT valueT endF valueF => do
        let result ← Goose.Lower.joinValue endT valueT endF valueF
        Goose.Lower.recordValueRootRecipe result sourceScope
        (Pure.pure result : B ValueId))
      (fun _ _ _ _ _ _ _ _ valid bound _ _ run =>
        scope_joinValue_recorded valid bound sourceScope run)
      env before entry exit valid bound head current live run

theorem ScopeAction.ifArms {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    (condition : ValueId) {first second : B ValueId}
    (firstAction : ScopeAction parents parent first) (secondAction : ScopeAction parents parent second) :
    ScopeAction parents parent (Goose.Lower.whenLive () fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let _ ← first
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let _ ← second
      let endF ← Goose.Lower.curBlock
      Goose.Lower.joinArms endT endF) := by
  refine ⟨advB_ifS_some_core condition firstAction.advance secondAction.advance, ?_⟩
  intro env before entry exit valid bound head
  generalize run : (Goose.Lower.whenLive () fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let _ ← first
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let _ ← second
      let endF ← Goose.Lower.curBlock
      Goose.Lower.joinArms endT endF) env before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  cases live : before.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨entry, exit, valid, ScopeMapAdvance.refl _ _ _⟩
  | some current =>
    rw [whenLive_some _ _ _ live] at run
    exact scope_ifBranches condition firstAction secondAction
      (fun endT _ endF _ => Goose.Lower.joinArms endT endF)
      (fun _ _ _ _ _ _ _ _ valid bound _ _ run => scope_joinArms valid bound run)
      env before entry exit valid bound head current live run

theorem ScopeBuilder.forkAny {parents : Array (Option ScopeId)}
    {entry exit : BlockId → List ScopeId} {before : LS}
    (valid : ScopeBuilder parents entry exit before) (bound : ScopeLiveBound before)
    (condition : ValueId) (env : LEnv) :
    ScopeBuilder parents (forkScopeMap before entry) (forkScopeMap before exit)
      (Goose.Lower.fork condition env before).2 := by
  cases live : before.cur with
  | some block => exact valid.fork bound condition env block live
  | none =>
    let first : LS := { before with blocks := before.blocks.push ⟨[], #[]⟩ }
    let firstEntry := fun other => if other = before.blocks.size then before.stack else entry other
    let firstExit := fun other => if other = before.blocks.size then before.stack else exit other
    have one : ScopeBuilder parents firstEntry firstExit first := valid.push bound [] before.vals
    have secondBound : ScopeLiveBound first := by
      intro other current
      rw [live] at current
      cases current
    have two := one.push secondBound [] before.vals
    have entryEq : (fun other => if other = first.blocks.size then first.stack else firstEntry other) =
        forkScopeMap before entry := by
      funext other
      by_cases firstId : other = before.blocks.size <;>
        by_cases secondId : other = before.blocks.size + 1 <;>
        simp [first, firstEntry, forkScopeMap, firstId, secondId]
    have exitEq : (fun other => if other = first.blocks.size then first.stack else firstExit other) =
        forkScopeMap before exit := by
      funext other
      by_cases firstId : other = before.blocks.size <;>
        by_cases secondId : other = before.blocks.size + 1 <;>
        simp [first, firstExit, forkScopeMap, firstId, secondId]
    simp only [Goose.Lower.fork, bind_run, newBlock0_run, pure_run]
    rw [emitTerm_none _ _ (by exact live)]
    simpa only [entryEq, exitEq] using two

theorem ScopeAction.forkResume {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    (condition : ValueId) (body : BlockId → B α)
    (bodyAction : ∀ target, ScopeAction parents parent (body target)) :
    ScopeAction parents parent (do
      let (tb, xb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let _ ← body xb
      Goose.Lower.setCur (some xb)) := by
  refine ⟨?_, ?_⟩
  · exact advB_loopBody condition
      (body := fun _ target => do let _ ← body target; Pure.pure 0) (back := Pure.pure ())
      (fun _ target => AdvB.bind (bodyAction target).advance fun _ => AdvB.pure _) (AdvB.pure _)
  · intro env before entry exit valid bound head
    generalize run : (do
      let (tb, xb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let _ ← body xb
      Goose.Lower.setCur (some xb)) env before = result
    obtain ⟨resultValue, after⟩ := result
    dsimp only
    simp only [bind_eq] at run
    obtain ⟨⟨tb, xb⟩, forked, forkRun, u1, started, startRun, value, evaluated, bodyRun, resumeRun⟩ := run
    have ids := fork_ids forkRun
    obtain ⟨tbId, xbId⟩ := Prod.mk.inj ids.1
    subst tbId xbId
    have forkedValid := valid.forkAny bound condition env
    rw [forkRun] at forkedValid
    dsimp only at forkedValid
    have forkAdvance := advB_fork condition env before _ _ forkRun
    have startedValid := forkedValid.setCur (some before.blocks.size) (by
      intro block same
      cases same
      simp [forkScopeMap, forkAdvance.stack]) env
    rw [startRun] at startedValid
    dsimp only at startedValid
    have startAdvance := adv_setCur_step forkAdvance (Or.inr (Nat.le_refl _))
      (by have size := ids.2; nat_omega) startRun
    obtain ⟨nextEntry, nextExit, evaluatedValid, bodyMaps⟩ :=
      (bodyAction (before.blocks.size + 1)).preserves env started
        (forkScopeMap before entry) (forkScopeMap before exit) startedValid
        (bound.advance startAdvance) (by rw [startAdvance.stack]; exact head)
    rw [bodyRun] at evaluatedValid
    dsimp only at evaluatedValid
    have bodyAdvance := (bodyAction (before.blocks.size + 1)).advance env started _ _ bodyRun
    have evaluatedStack : evaluated.stack = before.stack := bodyAdvance.stack.trans startAdvance.stack
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
    have exitStack := (bodyMaps _ exitOld).2 notExit
    have resumedValid := evaluatedValid.setCur (some (before.blocks.size + 1)) (by
      intro block same
      cases same
      rw [exitStack]
      simp [forkScopeMap, evaluatedStack]) env
    rw [resumeRun] at resumedValid
    dsimp only at resumedValid
    exact ⟨nextEntry, nextExit, resumedValid,
      (forkScopeMap_advance before entry exit).trans startAdvance bodyMaps⟩

theorem ScopeAction.whenLive {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    (default : α) {body : BlockId → B α} (bodyAction : ∀ block, ScopeAction parents parent (body block)) :
    ScopeAction parents parent (Goose.Lower.whenLive default body) := by
  unfold Goose.Lower.whenLive
  refine (ScopeAction.curBlock parents parent).bind fun current => ?_
  cases current with
  | none => exact ScopeAction.pure parents parent _
  | some block => exact bodyAction block

theorem ScopeAction.ifThen {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    (condition : ValueId) {body : B ValueId} (bodyAction : ScopeAction parents parent body) :
    ScopeAction parents parent (Goose.Lower.whenLive () fun _ => do
      let (tb, xb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let _ ← body
      Goose.Lower.emitTerm (.br xb [])
      Goose.Lower.setCur (some xb)) := by
  apply ScopeAction.whenLive
  intro block
  exact ScopeAction.forkResume condition (fun target => do let _ ← body; Goose.Lower.emitTerm (.br target []))
    (fun target => bodyAction.bind fun _ => ScopeAction.emitNeutralTerm parents parent (.br target []) rfl)

theorem ScopeAction.loopBody {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    (condition : ValueId) {body : Nat → BlockId → B ValueId} {back : B Unit}
    (bodyAction : ∀ depth target, ScopeAction parents parent (body depth target))
    (backAction : ScopeAction parents parent back) :
    ScopeAction parents parent (Goose.Lower.loopBody condition body back) := by
  unfold Goose.Lower.loopBody
  exact (ScopeAction.get parents parent).bind fun before =>
    ScopeAction.forkResume condition (fun target => do let _ ← body before.stack.length target; back)
      (fun target => (bodyAction before.stack.length target).bind fun _ => backAction)

theorem ScopeAction.rangeBack (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (type : IntTy) (counter : ValueId) (header : BlockId) :
    ScopeAction parents parent (Goose.Lower.rangeBack type counter header) := by
  unfold Goose.Lower.rangeBack
  refine (ScopeAction.isLive parents parent).bind fun live => ?_
  cases live
  · exact ScopeAction.pure parents parent _
  · exact (ScopeAction.emitDef parents parent _).bind fun value =>
      ScopeAction.emitNeutralTerm parents parent (.br header [value]) rfl

theorem scope_newBlock_run (types : List VTy) (env : LEnv) (before : LS) :
    Goose.Lower.newBlock types env before =
      ((before.blocks.size, (List.range types.length).map (before.vals.size + ·)),
        { before with blocks := before.blocks.push ⟨((List.range types.length).map (before.vals.size + ·)).zip types, #[]⟩, vals := types.foldl (fun vals type => vals.push (some type)) before.vals }) := rfl

theorem ScopeAction.header {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    (types : List VTy) (arguments : List ValueId) (allocateAdvance : AdvB (Goose.Lower.newBlock types))
    {tail : BlockId → List ValueId → B α}
    (tailAction : ∀ header params, ScopeAction parents parent (tail header params)) :
    ScopeAction parents parent (do
      let (header, params) ← Goose.Lower.newBlock types
      Goose.Lower.emitTerm (.br header arguments)
      Goose.Lower.setCur (some header)
      tail header params) := by
  have advancePrefix : ∀ {env before allocated closed started header params u1 u2},
      Goose.Lower.newBlock types env before = ((header, params), allocated) →
      Goose.Lower.emitTerm (.br header arguments) env allocated = (u1, closed) →
      Goose.Lower.setCur (some header) env closed = (u2, started) → before.Adv started := by
    intro env before allocated closed started header params u1 u2 allocateRun closeRun startRun
    have shape := allocateRun
    rw [scope_newBlock_run] at shape
    have headerId := (Prod.mk.inj (Prod.mk.inj shape).1).1
    have allocatedSize : allocated.blocks.size = before.blocks.size + 1 := by
      rw [← (Prod.mk.inj shape).2]
      simp
    have first := allocateAdvance env before _ _ allocateRun
    have second := first.trans (adv_emitTerm closeRun)
    have closedSize := (adv_emitTerm closeRun).ext.1
    apply adv_setCur_step second (Or.inr (by rw [← headerId]; exact Nat.le_refl _)) _ startRun
    rw [← headerId]
    nat_omega
  refine ⟨?_, ?_⟩
  · intro env before result after run
    simp only [bind_eq] at run
    obtain ⟨⟨header, params⟩, allocated, allocateRun, u1, closed, closeRun,
      u2, started, startRun, tailRun⟩ := run
    exact (advancePrefix allocateRun closeRun startRun).trans
      ((tailAction header params).advance env started _ _ tailRun)
  · intro env before entry exit valid bound head
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
    have allocatedValid := valid.newBlock bound env types
    rw [allocateRun] at allocatedValid
    dsimp only at allocatedValid
    have closedValid := allocatedValid.emitNeutralTerm (.br header arguments) rfl env
    rw [closeRun] at closedValid
    dsimp only at closedValid
    have shape := allocateRun
    rw [scope_newBlock_run] at shape
    have headerId := (Prod.mk.inj (Prod.mk.inj shape).1).1
    have allocatedStack := (allocateAdvance env before _ _ allocateRun).stack
    have closedStack := (adv_emitTerm closeRun).stack.trans allocatedStack
    have startedValid := closedValid.setCur (some header) (by
      intro block same
      cases same
      rw [← headerId]
      simp [closedStack]) env
    rw [startRun] at startedValid
    dsimp only at startedValid
    have startedAdvance := advancePrefix allocateRun closeRun startRun
    obtain ⟨afterEntry, afterExit, afterValid, tailMaps⟩ :=
      (tailAction header params).preserves env started nextEntry nextExit startedValid
        (bound.advance startedAdvance) (by rw [startedAdvance.stack]; exact head)
    rw [tailRun] at afterValid
    dsimp only at afterValid
    refine ⟨afterEntry, afterExit, afterValid, ScopeMapAdvance.trans startedAdvance ?_ tailMaps⟩
    intro block earlier
    have distinct : block ≠ before.blocks.size := Nat.ne_of_lt earlier
    simp [nextEntry, nextExit, distinct]

theorem ScopeAction.lowerWhile {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    (header : BlockId) {condition : B ValueId} {body : Nat → BlockId → B ValueId}
    (conditionAction : ScopeAction parents parent condition)
    (bodyAction : ∀ depth target, ScopeAction parents parent (body depth target)) :
    ScopeAction parents parent (Goose.Lower.lowerWhile header condition body) := by
  unfold Goose.Lower.lowerWhile
  exact conditionAction.bind fun value => ScopeAction.whenLive () fun _ =>
    ScopeAction.loopBody value bodyAction (ScopeAction.emitNeutralTerm parents parent (.br header []) rfl)

theorem ScopeAction.lowerRange {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    (type : IntTy) (counter bound : ValueId) (header : BlockId)
    {body : Nat → BlockId → B ValueId}
    (bodyAction : ∀ depth target, ScopeAction parents parent (body depth target)) :
    ScopeAction parents parent (Goose.Lower.lowerRange type counter bound header body) := by
  unfold Goose.Lower.lowerRange
  exact (ScopeAction.emitDef parents parent _).bind fun condition =>
    ScopeAction.loopBody condition bodyAction (ScopeAction.rangeBack parents parent type counter header)

theorem ScopeAction.lowerEach {parents : Array (Option ScopeId)} {parent : Option ScopeId}
    (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (header : BlockId) (counter : ValueId)
    {body : Nat → BlockId → B ValueId}
    (bodyAction : ∀ depth target, ScopeAction parents parent (body depth target)) :
    ScopeAction parents parent (Goose.Lower.lowerEach regrow owner sampled header counter body) := by
  unfold Goose.Lower.lowerEach
  exact (ScopeAction.eachLen parents parent regrow owner sampled).bind fun length =>
    (ScopeAction.emitDef parents parent _).bind fun condition =>
      ScopeAction.loopBody condition bodyAction (ScopeAction.rangeBack parents parent .i64 counter header)

theorem ScopeAction.assertCore (parents : Array (Option ScopeId)) (parent : Option ScopeId)
    (condition : ValueId) (origin : OriginId) :
    ScopeAction parents parent (Goose.Lower.whenLive () fun _ => do
      let (pass, fail) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some fail)
      Goose.Lower.emitTerm (.abort .assert (some origin))
      Goose.Lower.setCur (some pass)) := by
  refine ⟨advB_assert_core condition origin, ?_⟩
  intro env before entry exit valid bound head
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
    exact ⟨entry, exit, valid, ScopeMapAdvance.refl _ _ _⟩
  | some current =>
    rw [whenLive_some _ _ _ live] at run
    simp only [bind_eq] at run
    obtain ⟨⟨pass, fail⟩, forked, forkRun, u1, started, startRun, u2, closed, closeRun, resumeRun⟩ := run
    have ids := fork_ids forkRun
    obtain ⟨passId, failId⟩ := Prod.mk.inj ids.1
    subst passId failId
    have forkedValid := valid.fork bound condition env current live
    rw [forkRun] at forkedValid
    dsimp only at forkedValid
    have forkStack := (advB_fork condition env before _ _ forkRun).stack
    have startedValid := forkedValid.setCur (some (before.blocks.size + 1)) (by
      intro block same
      cases same
      simp [forkScopeMap, forkStack]) env
    rw [startRun] at startedValid
    dsimp only at startedValid
    have startedStack : started.stack = before.stack := by
      rw [setCur_run] at startRun
      rw [← (Prod.mk.inj startRun).2]
      exact forkStack
    have closedValid := startedValid.emitNeutralTerm (.abort .assert (some origin)) rfl env
    rw [closeRun] at closedValid
    dsimp only at closedValid
    have closedStack := (adv_emitTerm closeRun).stack.trans startedStack
    have resumedValid := closedValid.setCur (some before.blocks.size) (by
      intro block same
      cases same
      simp [forkScopeMap, closedStack]) env
    rw [resumeRun] at resumedValid
    dsimp only at resumedValid
    exact ⟨forkScopeMap before entry, forkScopeMap before exit, resumedValid,
      forkScopeMap_advance before entry exit⟩

end Goose.Lower.Validation
