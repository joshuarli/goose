import Goose.Lower.Validation.StorageWalkControlBranches
import Goose.Lower.Validation.CfgOpenTargets
import Goose.Lower.Validation.ScopeFlowJoin

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem StorageWalkBuilder.patchBrs {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} (before : LS)
    (join : BlockId) (incoming : List (BlockId × ValueId)) (env : LEnv)
    (builder : StorageWalkBuilder slots entry exit before) :
    StorageWalkBuilder slots entry exit (Goose.Lower.patchBrs join incoming env before).2 ∧
      (Goose.Lower.patchBrs join incoming env before).2.stack = before.stack ∧
      (Goose.Lower.patchBrs join incoming env before).2.cur = before.cur := by
  induction incoming generalizing before with
  | nil => exact ⟨builder, rfl, rfl⟩
  | cons pair incoming ih =>
    simp only [Goose.Lower.patchBrs, bind_run]
    have rest := ih (Goose.Lower.patchTerm pair.1 (.br join [pair.2]) env before).2
      (builder.patchNeutralTerm pair.1 (.br join [pair.2]) rfl env)
    simpa only [patchTerm_run] using rest

theorem StorageWalkBuilder.patchBrs0 {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} (before : LS)
    (join : BlockId) (incoming : List BlockId) (env : LEnv)
    (builder : StorageWalkBuilder slots entry exit before) :
    StorageWalkBuilder slots entry exit (Goose.Lower.patchBrs0 join incoming env before).2 ∧
      (Goose.Lower.patchBrs0 join incoming env before).2.stack = before.stack ∧
      (Goose.Lower.patchBrs0 join incoming env before).2.cur = before.cur := by
  induction incoming generalizing before with
  | nil => exact ⟨builder, rfl, rfl⟩
  | cons block incoming ih =>
    simp only [Goose.Lower.patchBrs0, bind_run]
    have rest := ih (Goose.Lower.patchTerm block (.br join []) env before).2
      (builder.patchNeutralTerm block (.br join []) rfl env)
    simpa only [patchTerm_run] using rest

theorem storageWalk_joinLive_flow {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {env : LEnv} {before after : LS}
    (config : StorageWalkConfiguration slots entry exit before) (incoming : List (BlockId × ValueId))
    (facts : ∀ pair ∈ incoming, pair.1 < before.blocks.size ∧ exit pair.1 = before.stack)
    (run : (do
      let type ← valTy (incoming.headD (0, 0)).2
      let (join, params) ← newBlock [type]
      patchBrs join incoming
      setCur (some join)
      pure (params.headD 0) : B ValueId) env before = (result, after)) :
    ∃ nextEntry nextExit, StorageWalkConfiguration slots nextEntry nextExit after ∧
      ScopeMapAdvance before entry exit nextEntry nextExit := by
  have openness := joinLive_currentOpen incoming (fun pair member => (facts pair member).1) env
  dsimp only at openness
  rw [run] at openness
  dsimp only at openness
  simp only [bind_eq] at run
  obtain ⟨type, observed, observeRun, ⟨join, params⟩, allocated, allocateRun,
    u1, patched, patchRun, u2, resumed, resumeRun, pureRun⟩ := run
  have observedSame := valTy_eq observeRun
  subst observedSame
  let nextEntry := fun block => if block = observed.blocks.size then observed.stack else entry block
  let nextExit := fun block => if block = observed.blocks.size then observed.stack else exit block
  have allocatedConfig := config.newBlock [type] env
  rw [allocateRun] at allocatedConfig
  dsimp only at allocatedConfig
  have shape := allocateRun
  rw [newBlock1_run] at shape
  have joinId := (Prod.mk.inj (Prod.mk.inj shape).1).1
  have allocatedSize : allocated.blocks.size = observed.blocks.size + 1 := by
    rw [← (Prod.mk.inj shape).2]
    simp
  have allocatedStack := (adv_newBlock1 allocateRun).stack
  have patchedBuilder := StorageWalkBuilder.patchBrs allocated join incoming env allocatedConfig.builder
  rw [patchRun] at patchedBuilder
  dsimp only at patchedBuilder
  have patchedStack := patchedBuilder.2.1.trans allocatedStack
  have patchedBounded := allocatedConfig.bounded.patchBrs join incoming env allocated (by
    rw [← joinId]
    nat_omega)
  rw [patchRun] at patchedBounded
  dsimp only at patchedBounded
  have patchedEdges := allocatedConfig.edges.patchBrs join incoming env allocated (by
    intro pair member
    have old := (facts pair member).1
    have distinct : pair.1 ≠ observed.blocks.size := Nat.ne_of_lt old
    rw [← joinId]
    simp only [ite_true, distinct, ite_false]
    exact (facts pair member).2.symm)
  rw [patchRun] at patchedEdges
  dsimp only at patchedEdges
  have resumedBuilder := patchedBuilder.1.setCur (some join) (by
    intro block same
    cases same
    rw [← joinId]
    simp [patchedStack]) env
  rw [resumeRun] at resumedBuilder
  dsimp only at resumedBuilder
  have resumedBounded := patchedBounded.setCur (some join) env
  rw [resumeRun] at resumedBounded
  dsimp only at resumedBounded
  have resumedEdges := patchedEdges.of_blocks (setCur_blocks resumeRun)
  rw [pure_run] at pureRun
  obtain ⟨_, rfl⟩ := Prod.mk.inj pureRun
  refine ⟨nextEntry, nextExit, ⟨resumedBuilder, openness, resumedBounded, resumedEdges⟩, ?_⟩
  intro block earlier
  have distinct : block ≠ observed.blocks.size := Nat.ne_of_lt earlier
  simp [nextEntry, nextExit, distinct]

theorem storageWalk_joinValue_flow {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {env : LEnv} {before after : LS}
    (config : StorageWalkConfiguration slots entry exit before)
    {endT endF : Option BlockId} {valueT valueF result : ValueId}
    (thenFacts : ∀ block, endT = some block → block < before.blocks.size ∧ exit block = before.stack)
    (elseFacts : ∀ block, endF = some block → block < before.blocks.size ∧ exit block = before.stack)
    (run : joinValue endT valueT endF valueF env before = (result, after)) :
    ∃ nextEntry nextExit, StorageWalkConfiguration slots nextEntry nextExit after ∧
      ScopeMapAdvance before entry exit nextEntry nextExit := by
  have facts : ∀ pair ∈ (endT.map (fun block => (block, valueT))).toList ++
      (endF.map (fun block => (block, valueF))).toList,
      pair.1 < before.blocks.size ∧ exit pair.1 = before.stack := by
    intro pair member
    rcases List.mem_append.mp member with member | member
    · cases endT with
      | none => simp at member
      | some block =>
        simp only [Option.map_some, Option.toList_some, List.mem_singleton] at member
        subst pair
        exact thenFacts block rfl
    · cases endF with
      | none => simp at member
      | some block =>
        simp only [Option.map_some, Option.toList_some, List.mem_singleton] at member
        subst pair
        exact elseFacts block rfl
  unfold joinValue at run
  cases endT <;> cases endF
  · simp only [bind_eq] at run
    obtain ⟨u, closed, closeRun, pureRun⟩ := run
    have closedConfig := config.setNone env
    rw [closeRun] at closedConfig
    dsimp only at closedConfig
    rw [pure_run] at pureRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj pureRun
    exact ⟨entry, exit, closedConfig, ScopeMapAdvance.refl _ _ _⟩
  · exact storageWalk_joinLive_flow config _ facts run
  · exact storageWalk_joinLive_flow config _ facts run
  · exact storageWalk_joinLive_flow config _ facts run

theorem storageWalk_joinEmpty_flow {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {env : LEnv} {before after : LS}
    (config : StorageWalkConfiguration slots entry exit before) (incoming : List BlockId)
    (facts : ∀ block ∈ incoming, block < before.blocks.size ∧ exit block = before.stack)
    (run : (do
      let (join, _) ← newBlock []
      patchBrs0 join incoming
      setCur (some join) : B Unit) env before = (result, after)) :
    ∃ nextEntry nextExit, StorageWalkConfiguration slots nextEntry nextExit after ∧
      ScopeMapAdvance before entry exit nextEntry nextExit := by
  have openness := joinEmpty_currentOpen before incoming (fun block member => (facts block member).1) env
  dsimp only at openness
  rw [run] at openness
  dsimp only at openness
  simp only [bind_eq] at run
  obtain ⟨⟨join, params⟩, allocated, allocateRun, u, patched, patchRun, resumeRun⟩ := run
  let nextEntry := fun block => if block = before.blocks.size then before.stack else entry block
  let nextExit := fun block => if block = before.blocks.size then before.stack else exit block
  have allocatedConfig := config.newBlock [] env
  rw [allocateRun] at allocatedConfig
  dsimp only at allocatedConfig
  have shape := allocateRun
  rw [newBlock0_run] at shape
  have joinId := (Prod.mk.inj (Prod.mk.inj shape).1).1
  have allocatedSize : allocated.blocks.size = before.blocks.size + 1 := by
    rw [← (Prod.mk.inj shape).2]
    simp
  have allocatedStack := (adv_newBlock0 allocateRun).stack
  have patchedBuilder := StorageWalkBuilder.patchBrs0 allocated join incoming env allocatedConfig.builder
  rw [patchRun] at patchedBuilder
  dsimp only at patchedBuilder
  have patchedStack := patchedBuilder.2.1.trans allocatedStack
  have patchedBounded := allocatedConfig.bounded.patchBrs0 join incoming env allocated (by
    rw [← joinId]
    nat_omega)
  rw [patchRun] at patchedBounded
  dsimp only at patchedBounded
  have patchedEdges := allocatedConfig.edges.patchBrs0 join incoming env allocated (by
    intro block member
    have distinct : block ≠ before.blocks.size := Nat.ne_of_lt (facts block member).1
    rw [← joinId]
    simp only [ite_true, distinct, ite_false]
    exact (facts block member).2.symm)
  rw [patchRun] at patchedEdges
  dsimp only at patchedEdges
  have resumedBuilder := patchedBuilder.1.setCur (some join) (by
    intro block same
    cases same
    rw [← joinId]
    simp [patchedStack]) env
  rw [resumeRun] at resumedBuilder
  dsimp only at resumedBuilder
  have resumedBounded := patchedBounded.setCur (some join) env
  rw [resumeRun] at resumedBounded
  dsimp only at resumedBounded
  have resumedEdges := patchedEdges.of_blocks (setCur_blocks resumeRun)
  refine ⟨nextEntry, nextExit, ⟨resumedBuilder, openness, resumedBounded, resumedEdges⟩, ?_⟩
  intro block earlier
  have distinct : block ≠ before.blocks.size := Nat.ne_of_lt earlier
  simp [nextEntry, nextExit, distinct]

theorem storageWalk_joinArms_flow {slots : Array Slot}
    {entry exit : BlockId → List ScopeId} {env : LEnv} {before after : LS}
    (config : StorageWalkConfiguration slots entry exit before)
    {endT endF : Option BlockId} {result : Unit}
    (thenFacts : ∀ block, endT = some block → block < before.blocks.size ∧ exit block = before.stack)
    (elseFacts : ∀ block, endF = some block → block < before.blocks.size ∧ exit block = before.stack)
    (run : joinArms endT endF env before = (result, after)) :
    ∃ nextEntry nextExit, StorageWalkConfiguration slots nextEntry nextExit after ∧
      ScopeMapAdvance before entry exit nextEntry nextExit := by
  have facts : ∀ block ∈ endT.toList ++ endF.toList,
      block < before.blocks.size ∧ exit block = before.stack := by
    intro block member
    rcases List.mem_append.mp member with member | member
    · have same : endT = some block := by simpa using member
      exact thenFacts block same
    · have same : endF = some block := by simpa using member
      exact elseFacts block same
  unfold joinArms at run
  cases endT <;> cases endF
  · dsimp only at run
    have closedConfig := config.setNone env
    rw [run] at closedConfig
    dsimp only at closedConfig
    exact ⟨entry, exit, closedConfig, ScopeMapAdvance.refl _ _ _⟩
  · exact storageWalk_joinEmpty_flow config _ facts run
  · exact storageWalk_joinEmpty_flow config _ facts run
  · exact storageWalk_joinEmpty_flow config _ facts run

theorem storageWalk_flowIfBranches {slots : Array Slot} {stack : List ScopeId}
    {loop : Option LoopCtx} (condition : ValueId) {first second : B ValueId}
    (firstAction : StorageWalkAction slots stack loop first)
    (secondAction : StorageWalkAction slots stack loop second)
    (tail : Option BlockId → ValueId → Option BlockId → ValueId → B α)
    (tailPreserves : ∀ endT valueT endF valueF env before entry exit,
      StorageWalkConfiguration slots entry exit before →
      (∀ block, endT = some block → block < before.blocks.size ∧ exit block = before.stack) →
      (∀ block, endF = some block → block < before.blocks.size ∧ exit block = before.stack) →
      ∀ result after, tail endT valueT endF valueF env before = (result, after) →
      ∃ nextEntry nextExit, StorageWalkConfiguration slots nextEntry nextExit after ∧
        ScopeMapAdvance before entry exit nextEntry nextExit)
    (env : LEnv) (before : LS) (entry exit : BlockId → List ScopeId)
    (config : StorageWalkConfiguration slots entry exit before)
    (context : ScopeLoopContext loop entry before.stack before.blocks.size)
    (stackEq : before.stack = stack) (current : BlockId) (live : before.cur = some current)
    {result : α} {after : LS}
    (run : (do
      let (tb, eb) ← fork condition
      setCur (some tb)
      let valueT ← first
      let endT ← curBlock
      setCur (some eb)
      let valueF ← second
      let endF ← curBlock
      tail endT valueT endF valueF) env before = (result, after)) :
    ∃ nextEntry nextExit, StorageWalkConfiguration slots nextEntry nextExit after ∧
      ScopeMapAdvance before entry exit nextEntry nextExit := by
  simp only [bind_eq] at run
  obtain ⟨⟨tb, eb⟩, forked, forkRun, u1, firstStart, firstStartRun,
    valueT, firstEnd, firstRun, endT, firstRead, firstReadRun, u2, secondStart, secondStartRun,
    valueF, secondEnd, secondRun, endF, secondRead, secondReadRun, tailRun⟩ := run
  have ids := fork_ids forkRun
  obtain ⟨tbId, ebId⟩ := Prod.mk.inj ids.1
  subst tbId ebId
  have forkedConfig := config.fork condition env
  rw [forkRun] at forkedConfig
  dsimp only at forkedConfig
  have forkTargets := fork_open_targets live (config.openCurrent.bound current live) condition env
  rw [forkRun] at forkTargets
  dsimp only at forkTargets
  obtain ⟨thenBody, thenRow, thenOpen⟩ := forkTargets.1
  obtain ⟨elseBody, elseRow, elseOpen⟩ := forkTargets.2
  have forkAdvance := advB_fork condition env before _ _ forkRun
  have firstStartConfig := forkedConfig.setCur before.blocks.size thenBody thenRow thenOpen (by
    simp [forkScopeMap, forkAdvance.stack]) env
  rw [firstStartRun] at firstStartConfig
  dsimp only at firstStartConfig
  have firstStartAdvance := adv_setCur_step forkAdvance (Or.inr (Nat.le_refl _))
    (by have size := ids.2; nat_omega) firstStartRun
  have firstContext := ScopeLoopContext.advance context firstStartAdvance (forkScopeMap_advance before entry exit)
  obtain ⟨firstEntry, firstExit, firstEndConfig, firstMaps⟩ :=
    firstAction.preserves env firstStart (forkScopeMap before entry) (forkScopeMap before exit)
      firstStartConfig firstContext (by rw [firstStartAdvance.stack]; exact stackEq)
  rw [firstRun] at firstEndConfig
  dsimp only at firstEndConfig
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
  have firstEndOther := LS_Adv.otherCurrent firstAdvance secondOld notSecond
  have secondRow : firstEnd.blocks[before.blocks.size + 1]? = some elseBody :=
    firstAdvance.keep _ elseBody notSecond (by rw [setCur_blocks firstStartRun]; exact elseRow)
  have secondStartConfig := firstEndConfig.setCur (before.blocks.size + 1) elseBody secondRow elseOpen (by
    rw [secondExit]
    simp [forkScopeMap, firstStack]) env
  rw [secondStartRun] at secondStartConfig
  dsimp only at secondStartConfig
  have secondAllocated : before.blocks.size + 1 < firstEnd.blocks.size :=
    Nat.lt_of_lt_of_le secondOld firstAdvance.ext.1
  have secondStartAdvance := adv_setCur_step firstEndAdvance
    (Or.inr (Nat.le_succ_of_le (Nat.le_refl _))) secondAllocated secondStartRun
  have secondContext := ScopeLoopContext.advance context secondStartAdvance
    ((forkScopeMap_advance before entry exit).trans firstStartAdvance firstMaps)
  obtain ⟨secondEntry, secondExit, secondEndConfig, secondMaps⟩ :=
    secondAction.preserves env secondStart firstEntry firstExit secondStartConfig secondContext
      (by rw [secondStartAdvance.stack]; exact stackEq)
  rw [secondRun] at secondEndConfig
  dsimp only at secondEndConfig
  have secondAdvance := secondAction.advance env secondStart _ _ secondRun
  have secondEndAdvance := secondStartAdvance.trans secondAdvance
  obtain ⟨endFEqual, secondReadEqual⟩ := curBlock_eq secondReadRun
  subst secondRead
  have thenFacts : ∀ block, endT = some block →
      block < secondEnd.blocks.size ∧ secondExit block = secondEnd.stack := by
    intro block endpoint
    have firstLive : firstEnd.cur = some block := endTEqual.symm.trans endpoint
    have firstBound := firstEndConfig.openCurrent.bound block firstLive
    have firstExitStack := firstEndConfig.builder.current block firstLive
    have secondBound : block < secondStart.blocks.size := by rw [setCur_blocks secondStartRun]; exact firstBound
    have notCurrent : secondStart.cur ≠ some block := by
      rw [setCur_run] at secondStartRun
      rw [← (Prod.mk.inj secondStartRun).2]
      dsimp only
      intro same
      have equality := Option.some.inj same
      rw [← equality] at firstLive
      exact firstEndOther firstLive
    refine ⟨Nat.lt_of_lt_of_le secondBound secondAdvance.ext.1, ?_⟩
    rw [(secondMaps block secondBound).2 notCurrent, firstExitStack]
    exact firstEndAdvance.stack.trans secondEndAdvance.stack.symm
  have elseFacts : ∀ block, endF = some block →
      block < secondEnd.blocks.size ∧ secondExit block = secondEnd.stack := by
    intro block endpoint
    have finalLive : secondEnd.cur = some block := endFEqual.symm.trans endpoint
    exact ⟨secondEndConfig.openCurrent.bound block finalLive, secondEndConfig.builder.current block finalLive⟩
  obtain ⟨afterEntry, afterExit, afterConfig, tailMaps⟩ :=
    tailPreserves endT valueT endF valueF env secondEnd secondEntry secondExit
      secondEndConfig thenFacts elseFacts result after tailRun
  have firstFrame := (forkScopeMap_advance before entry exit).trans firstStartAdvance firstMaps
  have secondFrame := firstFrame.trans secondStartAdvance secondMaps
  exact ⟨afterEntry, afterExit, afterConfig, secondFrame.trans secondEndAdvance tailMaps⟩

theorem StorageWalkAction.ifValue {slots : Array Slot} {stack : List ScopeId}
    {loop : Option LoopCtx} (condition : ValueId) {first second : B ValueId}
    (firstAction : StorageWalkAction slots stack loop first)
    (secondAction : StorageWalkAction slots stack loop second) :
    StorageWalkAction slots stack loop (Goose.Lower.whenLive 0 fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← first
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← second
      let endF ← Goose.Lower.curBlock
      joinValue endT valueT endF valueF) := by
  refine ⟨advB_ifE_core condition firstAction.advance secondAction.advance, ?_⟩
  intro env before entry exit config context stackEq
  generalize run : (Goose.Lower.whenLive 0 fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let valueT ← first
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let valueF ← second
      let endF ← Goose.Lower.curBlock
      joinValue endT valueT endF valueF) env before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  cases live : before.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨entry, exit, config, ScopeMapAdvance.refl _ _ _⟩
  | some current =>
    rw [whenLive_some _ _ _ live] at run
    exact storageWalk_flowIfBranches condition firstAction secondAction
      (fun endT valueT endF valueF => joinValue endT valueT endF valueF)
      (fun _ _ _ _ _ _ _ _ config thenFacts elseFacts _ _ run =>
        storageWalk_joinValue_flow config thenFacts elseFacts run)
      env before entry exit config context stackEq current live run

theorem StorageWalkAction.ifArms {slots : Array Slot} {stack : List ScopeId}
    {loop : Option LoopCtx} (condition : ValueId) {first second : B ValueId}
    (firstAction : StorageWalkAction slots stack loop first)
    (secondAction : StorageWalkAction slots stack loop second) :
    StorageWalkAction slots stack loop (Goose.Lower.whenLive () fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let _ ← first
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let _ ← second
      let endF ← Goose.Lower.curBlock
      joinArms endT endF) := by
  refine ⟨advB_ifS_some_core condition firstAction.advance secondAction.advance, ?_⟩
  intro env before entry exit config context stackEq
  generalize run : (Goose.Lower.whenLive () fun _ => do
      let (tb, eb) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some tb)
      let _ ← first
      let endT ← Goose.Lower.curBlock
      Goose.Lower.setCur (some eb)
      let _ ← second
      let endF ← Goose.Lower.curBlock
      joinArms endT endF) env before = result
  obtain ⟨resultValue, after⟩ := result
  dsimp only
  cases live : before.cur with
  | none =>
    rw [whenLive_none _ _ _ live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨entry, exit, config, ScopeMapAdvance.refl _ _ _⟩
  | some current =>
    rw [whenLive_some _ _ _ live] at run
    exact storageWalk_flowIfBranches condition firstAction secondAction
      (fun endT _ endF _ => joinArms endT endF)
      (fun _ _ _ _ _ _ _ _ config thenFacts elseFacts _ _ run =>
        storageWalk_joinArms_flow config thenFacts elseFacts run)
      env before entry exit config context stackEq current live run

end Goose.Lower.Validation
