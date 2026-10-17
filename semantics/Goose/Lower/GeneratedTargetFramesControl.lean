import Goose.Lower.GeneratedTargetFrames

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Lower.Validation

theorem generatedTargetFrame_recordValueRootRecipe (loop : Option LoopCtx)
    (value : ValueId) (sourceScope : ScopeId) :
    GeneratedTargetFrameRun loop (recordValueRootRecipe value sourceScope) := by
  intro base env current result after baseCurrent frames terms run
  rw [recordValueRootRecipe_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨terms, .refl _⟩

theorem generatedTargetFrame_curBlock (loop : Option LoopCtx) :
    GeneratedTargetFrameRun loop curBlock := by
  intro base env current result after baseCurrent frames terms run
  rw [curBlock_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨terms, .refl _⟩

theorem generatedTargetFrame_isLive (loop : Option LoopCtx) :
    GeneratedTargetFrameRun loop isLive := by
  unfold isLive
  exact GeneratedTargetFrameRun.bind (generatedTargetFrame_curBlock loop) fun _ =>
    generatedTargetFrame_pure loop _

theorem generatedTargetFrame_whenLive (loop : Option LoopCtx) (fallback : α)
    {action : BlockId → B α}
    (body : ∀ block, GeneratedTargetFrameRun loop (action block)) :
    GeneratedTargetFrameRun loop (whenLive fallback action) := by
  unfold whenLive
  exact GeneratedTargetFrameRun.bind (generatedTargetFrame_curBlock loop) fun current =>
    match current with
    | none => generatedTargetFrame_pure loop fallback
    | some block => body block

theorem newBlock_fresh {base state : LS} {types : List VTy}
    {env : LEnv} {result : BlockId × List ValueId} {after : LS}
    (baseState : base.Ext state)
    (run : newBlock types env state = (result, after)) :
    base.blocks.size ≤ result.1 := by
  rw [newBlock_run_general] at run
  rcases Prod.mk.inj run with ⟨resultEq, _⟩
  have id := congrArg Prod.fst resultEq
  rw [← id]
  exact baseState.1

theorem newBlock_params {types : List VTy} {env : LEnv} {before after : LS}
    {result : BlockId × List ValueId}
    (run : newBlock types env before = (result, after)) :
    ∃ block, after.blocks[result.1]? = some block ∧ block.params = result.2.zip types := by
  rw [newBlock_run_general] at run
  rcases Prod.mk.inj run with ⟨rfl, rfl⟩
  refine ⟨⟨(paramIds types before.vals).zip types, #[]⟩, ?_, rfl⟩
  simp

theorem fork_emptyRows {condition : ValueId} {env : LEnv} {before after : LS}
    {result : BlockId × BlockId}
    (run : fork condition env before = (result, after)) :
    (∃ body, after.blocks[result.1]? = some body ∧ body.params = []) ∧
      (∃ exit, after.blocks[result.2]? = some exit ∧ exit.params = []) := by
  unfold fork at run
  simp only [bind_eq] at run
  obtain ⟨⟨body, bodyParams⟩, first, firstRun, tail⟩ := run
  obtain ⟨⟨exit, exitParams⟩, second, secondRun, tail⟩ := tail
  obtain ⟨ignored, branched, branchRun, finished⟩ := tail
  rw [pure_run] at finished
  obtain ⟨resultEq, afterEq⟩ := Prod.mk.inj finished
  have bodyParamsEmpty : bodyParams = [] := by
    rw [newBlock_run_general] at firstRun
    have resultEq := (Prod.mk.inj firstRun).1
    simpa [paramIds] using (congrArg Prod.snd resultEq).symm
  have exitParamsEmpty : exitParams = [] := by
    rw [newBlock_run_general] at secondRun
    have resultEq := (Prod.mk.inj secondRun).1
    simpa [paramIds] using (congrArg Prod.snd resultEq).symm
  have firstExt := (advB_newBlock0 env before (body, bodyParams) first firstRun).ext
  have secondExt := (advB_newBlock0 env first (exit, exitParams) second secondRun).ext
  have branchExt := (advB_emitTerm (.condbr condition body [] exit []) env second () branched branchRun).ext
  subst result
  subst after
  obtain ⟨bodyBlock, bodyAt, bodyShape⟩ := newBlock_params firstRun
  obtain ⟨exitBlock, exitAt, exitShape⟩ := newBlock_params secondRun
  have bodyAt' : first.blocks[body]? = some bodyBlock := by simpa using bodyAt
  have exitAt' : second.blocks[exit]? = some exitBlock := by simpa using exitAt
  have bodyFinal := (secondExt.trans branchExt).2 body bodyBlock bodyAt'
  have exitFinal := branchExt.2 exit exitBlock exitAt'
  rcases bodyFinal with ⟨bodyAfter, bodyAt', bodyEq, _⟩
  rcases exitFinal with ⟨exitAfter, exitAt', exitEq, _⟩
  exact ⟨⟨bodyAfter, bodyAt', bodyEq.trans (by simpa [bodyParamsEmpty] using bodyShape)⟩,
    ⟨exitAfter, exitAt', exitEq.trans (by simpa [exitParamsEmpty] using exitShape)⟩⟩

theorem generatedTargetFrame_fork (loop : Option LoopCtx) (condition : ValueId) :
    GeneratedTargetFrameRun loop (fork condition) := by
  intro base env current result after baseCurrent frames terms run
  unfold fork at run
  simp only [bind_eq] at run
  obtain ⟨⟨yes, yesParams⟩, first, firstRun, tail⟩ := run
  obtain ⟨⟨no, noParams⟩, second, secondRun, tail⟩ := tail
  obtain ⟨ignored, branched, branchRun, finished⟩ := tail
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  have firstChecked := generatedTargetFrame_newBlock loop [] base env current (yes, yesParams)
    first baseCurrent frames terms firstRun
  have secondChecked := generatedTargetFrame_newBlock loop [] base env first (no, noParams)
    second (baseCurrent.trans firstChecked.2) frames firstChecked.1 secondRun
  have yesFresh := newBlock_fresh baseCurrent firstRun
  have noFresh := newBlock_fresh (baseCurrent.trans firstChecked.2) secondRun
  have branchFrames := secondChecked.1.emitTermAt branchRun (by
    intro target successor targetBound
    simp only [Term.successors] at successor
    simp only [List.mem_cons, List.not_mem_nil, or_false] at successor
    rcases successor with isYes | isNo
    · subst target
      exact False.elim (Nat.not_lt_of_ge (by simpa using yesFresh) targetBound)
    · subst target
      exact False.elim (Nat.not_lt_of_ge (by simpa using noFresh) targetBound))
  have branchExt := (advB_emitTerm (.condbr condition yes [] no []) env second () branched branchRun).ext
  exact ⟨branchFrames,
    firstChecked.2.trans (secondChecked.2.trans branchExt)⟩

theorem generatedTargetFrame_forkFresh {base current after : LS} {env : LEnv}
    {condition : ValueId} {result : BlockId × BlockId}
    (baseCurrent : base.Ext current)
    (run : fork condition env current = (result, after)) :
    base.blocks.size ≤ result.1 ∧ base.blocks.size ≤ result.2 := by
  unfold fork at run
  simp only [bind_eq] at run
  obtain ⟨⟨yes, yesParams⟩, first, firstRun, tail⟩ := run
  obtain ⟨⟨no, _⟩, second, secondRun, tail⟩ := tail
  obtain ⟨ignored, branched, branchRun, finished⟩ := tail
  rw [pure_run] at finished
  obtain ⟨resultEq, _⟩ := Prod.mk.inj finished
  have firstFresh := newBlock_fresh baseCurrent firstRun
  have firstExt := (advB_newBlock0 env current (yes, yesParams) first firstRun).ext
  have secondFresh := newBlock_fresh (baseCurrent.trans firstExt) secondRun
  have resultYes : result.1 = yes := (congrArg Prod.fst resultEq).symm
  have resultNo : result.2 = no := (congrArg Prod.snd resultEq).symm
  exact ⟨resultYes ▸ firstFresh, resultNo ▸ secondFresh⟩

theorem generatedTargetFrame_scFork (loop : Option LoopCtx) (isAnd : Bool)
    (value : ValueId) : GeneratedTargetFrameRun loop (scFork isAnd value) := by
  cases isAnd <;> {
  intro base env current result after baseCurrent frames terms run
  have runOriginal := run
  unfold scFork at run
  simp only [bind_eq, Bool.false_eq_true, ite_false, ite_true] at run
  obtain ⟨⟨rhs, rhsParams⟩, first, firstRun, ⟨join, joinParams⟩, second, secondRun,
    ignored, closed, closedRun, finished⟩ := run
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  have firstChecked := generatedTargetFrame_newBlock loop [] base env current
    (rhs, rhsParams) first baseCurrent frames terms firstRun
  have secondChecked := generatedTargetFrame_newBlock loop [.data .bool] base env first
    (join, joinParams) second (baseCurrent.trans firstChecked.2) frames firstChecked.1 secondRun
  have rhsFresh := newBlock_fresh baseCurrent firstRun
  have joinFresh := newBlock_fresh (baseCurrent.trans firstChecked.2) secondRun
  have closedChecked := secondChecked.1.emitTermAt closedRun (by
    intro target successor targetBound
    simp only [Term.successors] at successor
    simp only [List.mem_cons, List.not_mem_nil, or_false] at successor
    have fresh : base.blocks.size ≤ target := by
      rcases successor with h | h <;>
        first | simpa [h] using rhsFresh | simpa [h] using joinFresh
    exact False.elim (Nat.not_lt_of_ge fresh targetBound))
  exact ⟨closedChecked, (advB_scFork _ value env current result closed runOriginal).ext⟩
  }

theorem generatedTargetFrame_scForkFresh {base current after : LS} {env : LEnv}
    {isAnd : Bool} {value : ValueId} {result : BlockId × BlockId × ValueId}
    (baseCurrent : base.Ext current)
    (run : scFork isAnd value env current = (result, after)) :
    base.blocks.size ≤ result.1 ∧ base.blocks.size ≤ result.2.1 := by
  obtain ⟨resultEq, _⟩ := scFork_ids run
  have rhsId : result.1 = current.blocks.size := by simpa using congrArg Prod.fst resultEq
  have joinId : result.2.1 = current.blocks.size + 1 := by
    simpa using congrArg (fun values : BlockId × BlockId × ValueId => values.2.1) resultEq
  constructor
  · rw [rhsId]
    exact baseCurrent.1
  · rw [joinId]
    exact Nat.le_trans baseCurrent.1 (Nat.le_succ _)

theorem generatedTargetFrame_shortCircuit (loop : Option LoopCtx) (isAnd : Bool)
    (value : ValueId) {rhs : B ValueId}
    (rhsRun : GeneratedTargetFrameRun loop rhs) :
    GeneratedTargetFrameRun loop (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  refine generatedTargetFrame_whenLive loop 0 fun _ => ?_
  intro base env current result after baseCurrent frames terms run
  have runOriginal := run
  simp only [bind_eq] at run
  obtain ⟨⟨rhsBlock, join, parameter⟩, forked, forkRun,
    ignored, selected, selectedRun, rhsValue, body, bodyRun,
    ignored', closed, closedRun, ignored'', final, finalRun, finished⟩ := run
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  have forkChecked := generatedTargetFrame_scFork loop isAnd value base env current
    (rhsBlock, join, parameter) forked baseCurrent frames terms forkRun
  have selectedChecked := generatedTargetFrame_setCur loop (some rhsBlock) base env forked ()
    selected (baseCurrent.trans forkChecked.2) frames forkChecked.1 selectedRun
  have baseSelected := baseCurrent.trans (forkChecked.2.trans selectedChecked.2)
  have currentSelected := forkChecked.2.trans selectedChecked.2
  have bodyChecked := rhsRun base env selected rhsValue body baseSelected frames
    selectedChecked.1 bodyRun
  have joinFresh := (generatedTargetFrame_scForkFresh baseCurrent forkRun).2
  have closedChecked := bodyChecked.1.emitTermAt closedRun (by
    intro target successor targetBound
    simp only [Term.successors, List.mem_singleton] at successor
    subst target
    exact False.elim (Nat.not_lt_of_ge joinFresh targetBound))
  have closedExt := (advB_emitTerm (.br join [rhsValue]) env body () closed closedRun).ext
  have baseClosed := baseSelected.trans (bodyChecked.2.trans closedExt)
  have finalChecked := generatedTargetFrame_setCur loop (some join) base env closed () final
    baseClosed frames closedChecked finalRun
  exact ⟨finalChecked.1,
    currentSelected.trans (bodyChecked.2.trans (closedExt.trans finalChecked.2))⟩

theorem TermEdgesFramed.patchBrsAt {loop : Option LoopCtx} {base before after : LS}
    {env : LEnv} {result : Unit} {join : BlockId} {pending : List (BlockId × ValueId)}
    (oldFrames : TermEdgesFramed loop base before)
    (run : patchBrs join pending env before = (result, after))
    (joinFresh : base.blocks.size ≤ join) :
    TermEdgesFramed loop base after ∧ before.Ext after := by
  induction pending generalizing before result after with
  | nil =>
      rw [patchBrs, pure_run] at run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
      exact ⟨oldFrames, .refl _⟩
  | cons head rest ih =>
      simp only [patchBrs, bind_eq] at run
      obtain ⟨ignored, middle, patched, tail⟩ := run
      have patchedFrames := oldFrames.patchTermAt patched (by
        intro target successor targetBound
        simp only [Term.successors, List.mem_singleton] at successor
        subst target
        exact False.elim (Nat.not_lt_of_ge joinFresh targetBound))
      have patchedExt := patchTerm_ext patched
      rcases ih patchedFrames tail with ⟨frames, ext⟩
      exact ⟨frames, patchedExt.trans ext⟩

theorem TermEdgesFramed.patchBrs0At {loop : Option LoopCtx} {base before after : LS}
    {env : LEnv} {result : Unit} {join : BlockId} {pending : List BlockId}
    (oldFrames : TermEdgesFramed loop base before)
    (run : patchBrs0 join pending env before = (result, after))
    (joinFresh : base.blocks.size ≤ join) :
    TermEdgesFramed loop base after ∧ before.Ext after := by
  induction pending generalizing before result after with
  | nil =>
      rw [patchBrs0, pure_run] at run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
      exact ⟨oldFrames, .refl _⟩
  | cons block rest ih =>
      simp only [patchBrs0, bind_eq] at run
      obtain ⟨ignored, middle, patched, tail⟩ := run
      have patchedFrames := oldFrames.patchTermAt patched (by
        intro target successor targetBound
        simp only [Term.successors, List.mem_singleton] at successor
        subst target
        exact False.elim (Nat.not_lt_of_ge joinFresh targetBound))
      have patchedExt := patchTerm_ext patched
      rcases ih patchedFrames tail with ⟨frames, ext⟩
      exact ⟨frames, patchedExt.trans ext⟩

theorem generatedTargetFrame_joinAt (loop : Option LoopCtx) (pending : List (BlockId × ValueId))
    (ty : VTy) : GeneratedTargetFrameRun loop (do
      let (join, params) ← newBlock [ty]
      patchBrs join pending
      setCur (some join)
      pure (params.headD 0)) := by
  intro base env current result after baseCurrent frames terms run
  simp only [bind_eq] at run
  obtain ⟨⟨join, params⟩, allocatedState, allocated, tail⟩ := run
  obtain ⟨ignored, patchedState, patched, tail⟩ := tail
  obtain ⟨ignored', selectedState, selected, finished⟩ := tail
  rw [pure_run] at finished
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj finished
  have allocatedChecked := generatedTargetFrame_newBlock loop [ty] base env current
    (join, params) allocatedState baseCurrent frames terms allocated
  have patchChecked := TermEdgesFramed.patchBrsAt allocatedChecked.1 patched
    (newBlock_fresh baseCurrent allocated)
  have setChecked := generatedTargetFrame_setCur loop (some join) base env patchedState ()
    selectedState (baseCurrent.trans (allocatedChecked.2.trans patchChecked.2))
    frames patchChecked.1 selected
  exact ⟨setChecked.1,
    allocatedChecked.2.trans (patchChecked.2.trans setChecked.2)⟩

theorem generatedTargetFrame_valTy (loop : Option LoopCtx) (value : ValueId) :
    GeneratedTargetFrameRun loop (valTy value) := by
  intro base env current result after baseCurrent frames terms run
  have same := valTy_run value env current
  rw [run] at same
  change after = current at same
  subst after
  exact ⟨terms, .refl _⟩

theorem generatedTargetFrame_joinValue (loop : Option LoopCtx) (yes no : Option BlockId)
    (yesValue noValue : ValueId) : GeneratedTargetFrameRun loop
      (joinValue yes yesValue no noValue) := by
  unfold joinValue
  split
  · exact GeneratedTargetFrameRun.bind (generatedTargetFrame_setCur loop none) fun _ =>
      generatedTargetFrame_pure loop _
  · exact GeneratedTargetFrameRun.bind (generatedTargetFrame_valTy loop _) fun ty =>
      generatedTargetFrame_joinAt loop
        ((yes.map fun block => (block, yesValue)).toList ++
          (no.map fun block => (block, noValue)).toList) ty

theorem generatedTargetFrame_joinArmsAt (loop : Option LoopCtx) (pending : List BlockId) :
    GeneratedTargetFrameRun loop (do
      let (join, _) ← newBlock []
      patchBrs0 join pending
      setCur (some join)) := by
  intro base env current result after baseCurrent frames terms run
  simp only [bind_eq] at run
  obtain ⟨⟨join, ids⟩, allocatedState, allocated, tail⟩ := run
  obtain ⟨ignored, patchedState, patched, selected⟩ := tail
  have allocatedChecked := generatedTargetFrame_newBlock loop [] base env current
    (join, ids) allocatedState baseCurrent frames terms allocated
  have patchChecked := TermEdgesFramed.patchBrs0At allocatedChecked.1 patched
    (newBlock_fresh baseCurrent allocated)
  have setChecked := generatedTargetFrame_setCur loop (some join) base env patchedState ()
    after (baseCurrent.trans (allocatedChecked.2.trans patchChecked.2))
    frames patchChecked.1 selected
  exact ⟨setChecked.1,
    allocatedChecked.2.trans (patchChecked.2.trans setChecked.2)⟩

theorem generatedTargetFrame_joinArms (loop : Option LoopCtx) (yes no : Option BlockId) :
    GeneratedTargetFrameRun loop (joinArms yes no) := by
  unfold joinArms
  split
  · exact generatedTargetFrame_setCur loop none
  · exact generatedTargetFrame_joinArmsAt loop
      (yes.toList ++ no.toList)

theorem generatedTargetFrame_ifS_none_core (loop : Option LoopCtx) (condition : ValueId)
    {yes : B Unit} (yesRun : GeneratedTargetFrameRun loop yes) :
    GeneratedTargetFrameRun loop (whenLive () fun _ => do
      let (yesBlock, join) ← fork condition
      setCur (some yesBlock)
      let _ ← yes
      emitTerm (.br join [])
      setCur (some join)) := by
  refine generatedTargetFrame_whenLive loop () fun _ => ?_
  intro base env current result after baseCurrent frames terms run
  simp only [bind_eq] at run
  obtain ⟨⟨yesBlock, join⟩, forked, forkRun, ignored, selected, selectRun,
    value, body, bodyRun, ignored', closed, closedRun, finalRun⟩ := run
  have forkChecked := generatedTargetFrame_fork loop condition base env current
    (yesBlock, join) forked baseCurrent frames terms forkRun
  have selectedChecked := generatedTargetFrame_setCur loop (some yesBlock) base env forked ()
    selected (baseCurrent.trans forkChecked.2) frames forkChecked.1 selectRun
  have currentSelected := forkChecked.2.trans selectedChecked.2
  have baseSelected := baseCurrent.trans currentSelected
  have bodyChecked := yesRun base env selected value body baseSelected frames
    selectedChecked.1 bodyRun
  have joinFresh := (generatedTargetFrame_forkFresh baseCurrent forkRun).2
  have closedChecked := bodyChecked.1.emitTermAt closedRun (by
    intro target successor targetBound
    simp only [Term.successors, List.mem_singleton] at successor
    subst target
    exact False.elim (Nat.not_lt_of_ge joinFresh targetBound))
  have closedExt := (advB_emitTerm (.br join []) env body () closed closedRun).ext
  have finalChecked := generatedTargetFrame_setCur loop (some join) base env closed () after
    (baseSelected.trans
      (bodyChecked.2.trans closedExt)) frames closedChecked finalRun
  exact ⟨finalChecked.1,
    currentSelected.trans (bodyChecked.2.trans (closedExt.trans finalChecked.2))⟩

theorem generatedTargetFrame_ifE_recorded_core (loop : Option LoopCtx) (condition : ValueId) (sourceScope : ScopeId)
    {yes no : B ValueId} (yesRun : GeneratedTargetFrameRun loop yes)
    (noRun : GeneratedTargetFrameRun loop no) :
    GeneratedTargetFrameRun loop (whenLive 0 fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let yesValue ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let noValue ← no
      let noEnd ← curBlock
      let value ← joinValue yesEnd yesValue noEnd noValue
      recordValueRootRecipe value sourceScope
      pure value) := by
  refine generatedTargetFrame_whenLive loop _ fun _ => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_fork loop condition) fun blocks => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_setCur loop _) fun _ => ?_
  refine GeneratedTargetFrameRun.bind yesRun fun yesValue => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_curBlock loop) fun yesEnd => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_setCur loop _) fun _ => ?_
  refine GeneratedTargetFrameRun.bind noRun fun noValue => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_curBlock loop) fun noEnd => ?_
  exact GeneratedTargetFrameRun.bind (generatedTargetFrame_joinValue loop yesEnd noEnd yesValue noValue) fun value =>
    GeneratedTargetFrameRun.bind (generatedTargetFrame_recordValueRootRecipe loop value sourceScope) fun _ =>
      generatedTargetFrame_pure loop value

theorem generatedTargetFrame_ifE_core (loop : Option LoopCtx) (condition : ValueId)
    {yes no : B ValueId} (yesRun : GeneratedTargetFrameRun loop yes)
    (noRun : GeneratedTargetFrameRun loop no) :
    GeneratedTargetFrameRun loop (whenLive 0 fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let yesValue ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let noValue ← no
      let noEnd ← curBlock
      joinValue yesEnd yesValue noEnd noValue) := by
  refine generatedTargetFrame_whenLive loop _ fun _ => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_fork loop condition) fun blocks => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_setCur loop _) fun _ => ?_
  refine GeneratedTargetFrameRun.bind yesRun fun yesValue => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_curBlock loop) fun yesEnd => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_setCur loop _) fun _ => ?_
  refine GeneratedTargetFrameRun.bind noRun fun noValue => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_curBlock loop) fun noEnd => ?_
  exact generatedTargetFrame_joinValue loop yesEnd noEnd yesValue noValue

theorem generatedTargetFrame_ifS_some_core (loop : Option LoopCtx) (condition : ValueId)
    {yes no : B ValueId} (yesRun : GeneratedTargetFrameRun loop yes)
    (noRun : GeneratedTargetFrameRun loop no) :
    GeneratedTargetFrameRun loop (whenLive () fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let _ ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let _ ← no
      let noEnd ← curBlock
      joinArms yesEnd noEnd) := by
  refine generatedTargetFrame_whenLive loop _ fun _ => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_fork loop condition) fun blocks => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_setCur loop _) fun _ => ?_
  refine GeneratedTargetFrameRun.bind yesRun fun _ => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_curBlock loop) fun yesEnd => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_setCur loop _) fun _ => ?_
  refine GeneratedTargetFrameRun.bind noRun fun _ => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_curBlock loop) fun noEnd => ?_
  exact generatedTargetFrame_joinArms loop yesEnd noEnd

theorem generatedTargetFrame_assert_core (loop : Option LoopCtx) (condition : ValueId)
    (origin : OriginId) : GeneratedTargetFrameRun loop (whenLive () fun _ => do
      let (success, failure) ← fork condition
      setCur (some failure)
      emitTerm (.abort .assert (some origin))
      setCur (some success)) := by
  refine generatedTargetFrame_whenLive loop _ fun _ => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_fork loop condition) fun blocks => ?_
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_setCur loop _) fun _ => ?_
  refine GeneratedTargetFrameRun.bind
      (generatedTargetFrame_emitTerm loop (.abort .assert (some origin)) (by simp [Term.successors]))
      fun _ => ?_
  exact generatedTargetFrame_setCur loop _

theorem generatedTargetFrame_inScope {loop : Option LoopCtx} {action : B α} (scope : ScopeId)
    (body : GeneratedTargetFrameRun loop action) :
    GeneratedTargetFrameRun loop (inScope scope action) := by
  intro base env current result after baseCurrent frames terms run
  unfold inScope at run
  simp only [bind_eq] at run
  obtain ⟨ignored, entered, pushed, value, middle, bodyRun, ignored', left, popped, finished⟩ := run
  rw [pushScope_run] at pushed
  obtain ⟨_, rfl⟩ := Prod.mk.inj pushed
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  rw [popScope_run] at popped
  obtain ⟨_, rfl⟩ := Prod.mk.inj popped
  have inputFrames := terms.of_blocks (before := current)
    (after := { current with stack := scope :: current.stack }) (by rfl)
  have inputExt : current.Ext { current with stack := scope :: current.stack } := by
    exact .refl current
  have checked := body base env { current with stack := scope :: current.stack } value middle
    (baseCurrent.trans inputExt)
    frames inputFrames bodyRun
  have outputFrames := checked.1.of_blocks (before := middle)
    (after := { middle with stack := List.drop 1 middle.stack }) (by rfl)
  have outputExt : middle.Ext { middle with stack := List.drop 1 middle.stack } := by
    exact .refl middle
  exact ⟨outputFrames, inputExt.trans (checked.2.trans outputExt)⟩

theorem generatedTargetFrame_intTyOf (loop : Option LoopCtx) (value : ValueId) :
    GeneratedTargetFrameRun loop (intTyOf value) := by
  unfold intTyOf
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_valTy loop value) fun ty => ?_
  cases ty with
  | data ty => cases ty <;> first | exact generatedTargetFrame_pure loop _ | exact generatedTargetFrame_pure loop _
  | view _ _ => exact generatedTargetFrame_pure loop _

theorem generatedTargetFrame_freezeTo (loop : Option LoopCtx) (mutability : Mutability)
    (value : ValueId) : GeneratedTargetFrameRun loop (freezeTo mutability value) := by
  unfold freezeTo
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_valTy loop value) fun ty => ?_
  cases mutability <;> cases ty <;> first
    | exact generatedTargetFrame_pure loop _
    | (rename_i ty; cases ty <;> first
        | exact generatedTargetFrame_pure loop _
        | (rename_i m' _; cases m' <;> first
            | exact generatedTargetFrame_pure loop _
            | exact generatedTargetFrame_emitDef loop _))

theorem generatedTargetFrame_borrowTo (loop : Option LoopCtx) (mutability : Mutability)
    (value : ValueId) : GeneratedTargetFrameRun loop (borrowTo mutability value) := by
  unfold borrowTo
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_read loop) fun env =>
    GeneratedTargetFrameRun.bind (generatedTargetFrame_valTy loop value) fun ty => ?_
  split <;> dsimp only <;> split <;> first
    | exact generatedTargetFrame_emitDef loop _
    | exact generatedTargetFrame_freezeTo loop mutability value

theorem generatedTargetFrame_coerceTo (loop : Option LoopCtx) (target : Ty)
    (value : ValueId) (origin : OriginId) :
    GeneratedTargetFrameRun loop (coerceTo target value origin) := by
  unfold coerceTo
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_valTy loop value) fun source => ?_
  split
  · exact generatedTargetFrame_emitDef loop _
  · exact GeneratedTargetFrameRun.bind (generatedTargetFrame_emitDef loop _) fun _ =>
      generatedTargetFrame_emitDef loop _
  · exact generatedTargetFrame_pure loop _

theorem generatedTargetFrame_coerceSlot (loop : Option LoopCtx) (slot : SlotId)
    (value : ValueId) (origin : OriginId) :
    GeneratedTargetFrameRun loop (coerceSlot slot value origin) := by
  unfold coerceSlot
  exact GeneratedTargetFrameRun.bind (generatedTargetFrame_read loop) fun env =>
    match env.slots[slot]? with
    | none => generatedTargetFrame_pure loop _
    | some destination => generatedTargetFrame_coerceTo loop destination.ty value origin

theorem generatedTargetFrame_coerceResult (loop : Option LoopCtx) (value : ValueId)
    (origin : OriginId) : GeneratedTargetFrameRun loop (coerceResult value origin) := by
  unfold coerceResult
  exact GeneratedTargetFrameRun.bind (generatedTargetFrame_read loop) fun env =>
    match env.results.head? with
    | none => generatedTargetFrame_pure loop _
    | some destination => generatedTargetFrame_coerceTo loop destination value origin

theorem generatedTargetFrame_growOwner (loop : Option LoopCtx) (value : ValueId) :
    GeneratedTargetFrameRun loop (growOwner value) := by
  unfold growOwner
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_valTy loop value) fun ty => ?_
  cases ty with
  | data ty => cases ty with
    | ref _ referent => cases referent with
      | grow _ => exact generatedTargetFrame_pure loop true
      | growshrink _ => exact generatedTargetFrame_pure loop true
      | _ => exact generatedTargetFrame_pure loop false
    | _ => exact generatedTargetFrame_pure loop false
  | view _ _ => exact generatedTargetFrame_pure loop false

theorem generatedTargetFrame_regrowOf (loop : Option LoopCtx) (owner : Option ValueId) :
    GeneratedTargetFrameRun loop (regrowOf owner) := by
  cases owner with
  | none => exact generatedTargetFrame_pure loop false
  | some owner => exact generatedTargetFrame_growOwner loop owner

theorem generatedTargetFrame_eachSampled (loop : Option LoopCtx) (regrow : Bool)
    (view : ValueId) : GeneratedTargetFrameRun loop (eachSampled regrow view) := by
  cases regrow
  · exact generatedTargetFrame_emitDef loop _
  · exact generatedTargetFrame_pure loop _

theorem generatedTargetFrame_eachLen (loop : Option LoopCtx) (regrow : Bool)
    (owner : Option ValueId) (sampled : ValueId) :
    GeneratedTargetFrameRun loop (eachLen regrow owner sampled) := by
  cases regrow
  · exact generatedTargetFrame_pure loop _
  · exact generatedTargetFrame_emitDef loop _

theorem generatedTargetFrame_eachElemValue (loop : Option LoopCtx) (slot : VarId)
    (byRef : Bool) (element : ValueId) :
    GeneratedTargetFrameRun loop (eachElemValue slot byRef element) := by
  unfold eachElemValue
  cases byRef
  · exact generatedTargetFrame_emitDef loop _
  · refine GeneratedTargetFrameRun.bind (generatedTargetFrame_read loop) fun env => ?_
    cases env.vars[slot]? with
    | none => exact generatedTargetFrame_pure loop _
    | some declaration =>
      dsimp only
      cases declaration.ty <;> first
        | exact generatedTargetFrame_pure loop _
        | exact generatedTargetFrame_borrowTo loop _ _

theorem generatedTargetFrame_leaveAll (loop : Option LoopCtx) : ∀ scopes,
    GeneratedTargetFrameRun loop (leaveAll scopes)
  | [] => generatedTargetFrame_pure loop _
  | scope :: rest => by
      unfold leaveAll
      exact GeneratedTargetFrameRun.bind (generatedTargetFrame_emitEffect loop _) fun _ =>
        generatedTargetFrame_leaveAll loop rest

theorem generatedTargetFrame_leaveTo (loop : Option LoopCtx) (depth : Nat) :
    GeneratedTargetFrameRun loop (leaveTo depth) := by
  unfold leaveTo
  exact GeneratedTargetFrameRun.bind (generatedTargetFrame_get loop) fun state =>
    generatedTargetFrame_leaveAll loop _

theorem generatedTargetFrame_initSlots (loop : Option LoopCtx) : ∀ slots,
    GeneratedTargetFrameRun loop (initSlots slots)
  | [] => generatedTargetFrame_pure loop _
  | slot :: rest => by
      unfold initSlots
      exact GeneratedTargetFrameRun.bind (generatedTargetFrame_emitEffect loop _) fun _ =>
        generatedTargetFrame_initSlots loop rest

end Goose.Lower
