import Goose.Lower.GeneratedTargets

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Lower.Validation

theorem generatedTargets_newBlock_bound {types : List VTy} {env : LEnv} {before after : LS}
    {result : BlockId × List ValueId} (run : newBlock types env before = (result, after)) :
    result.1 < after.blocks.size := by
  rw [newBlock_run_general] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  simp

theorem generatedTargets_curBlock (loop : Option LoopCtx) : GeneratedTargetRun loop curBlock := by
  apply GeneratedTargetRun.unchanged
  intros
  rw [curBlock_run]

theorem generatedTargets_isLive (loop : Option LoopCtx) : GeneratedTargetRun loop isLive := by
  apply GeneratedTargetRun.unchanged
  intros
  rfl

theorem generatedTargets_whenLive (loop : Option LoopCtx) (fallback : α) {action : BlockId → B α}
    (body : ∀ block, GeneratedTargetRun loop (action block)) :
    GeneratedTargetRun loop (whenLive fallback action) := by
  unfold whenLive
  refine GeneratedTargetRun.bind (generatedTargets_curBlock loop) fun current => ?_
  cases current with
  | none => exact generatedTargets_pure loop fallback
  | some block => exact body block

theorem generatedTargets_regrowOf (loop : Option LoopCtx) (owner : Option ValueId) :
    GeneratedTargetRun loop (regrowOf owner) := by
  cases owner with
  | none => exact generatedTargets_pure loop false
  | some owner => exact generatedTargets_growOwner loop owner

theorem generatedTargets_eachSampled (loop : Option LoopCtx) (regrow : Bool) (view : ValueId) :
    GeneratedTargetRun loop (eachSampled regrow view) := by
  cases regrow
  · exact generatedTargets_emitDef loop _
  · exact generatedTargets_pure loop _

theorem generatedTargets_eachLen (loop : Option LoopCtx) (regrow : Bool) (owner : Option ValueId)
    (sampled : ValueId) : GeneratedTargetRun loop (eachLen regrow owner sampled) := by
  cases regrow
  · exact generatedTargets_pure loop _
  · exact generatedTargets_emitDef loop _

theorem generatedTargets_eachElemValue (loop : Option LoopCtx) (slot : VarId) (byRef : Bool)
    (element : ValueId) : GeneratedTargetRun loop (eachElemValue slot byRef element) := by
  unfold eachElemValue
  cases byRef
  · exact generatedTargets_emitDef loop _
  · refine GeneratedTargetRun.bind (generatedTargets_read loop) fun env => ?_
    cases env.vars[slot]? with
    | none => exact generatedTargets_pure loop _
    | some declaration =>
      dsimp only
      cases declaration.ty <;> first
        | exact generatedTargets_pure loop _
        | exact generatedTargets_borrowTo loop _ _

theorem generatedTargets_fork (loop : Option LoopCtx) (condition : ValueId) :
    GeneratedTargetRun loop (fork condition) := by
  intro env before result after run bounded targets
  have finalTargets := targets.mono (advB_fork condition env before result after run).ext.1
  refine ⟨?_, finalTargets⟩
  simp only [fork, bind_eq] at run
  obtain ⟨⟨yes, yesParams⟩, first, yesRun, ⟨no, noParams⟩, second, noRun,
    unit, third, branched, finished⟩ := run
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  have firstBounded := (generatedTargets_newBlock loop [] env before _ first yesRun bounded targets).1
  have secondResult := generatedTargets_newBlock loop [] env first _ second noRun firstBounded
    (targets.mono (adv_newBlock0 yesRun).ext.1)
  have yesBound := Nat.lt_of_lt_of_le (generatedTargets_newBlock_bound yesRun) (adv_newBlock0 noRun).ext.1
  have noBound := generatedTargets_newBlock_bound noRun
  have closed := secondResult.1.emitTerm (.condbr condition yes [] no []) (by
    intro target member
    simp only [Term.successors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact yesBound
    · exact noBound) env
  rw [branched] at closed
  exact closed

theorem generatedTargets_patchBrs (loop : Option LoopCtx) (join : BlockId) :
    ∀ (pending : List (BlockId × ValueId)) env before result after,
    patchBrs join pending env before = (result, after) →
    TargetsBounded before → LoopBuilderTargets loop before → join < before.blocks.size →
    TargetsBounded after ∧ LoopBuilderTargets loop after
  | [], env, before, result, after, run, bounded, targets, joinBound => by
    rw [patchBrs, pure_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨bounded, targets⟩
  | (block, value) :: pending, env, before, result, after, run, bounded, targets, joinBound => by
    simp only [patchBrs, bind_eq] at run
    obtain ⟨ignored, middle, patched, tail⟩ := run
    have patchedBounded := bounded.patchTerm block (.br join [value]) (by simpa [Term.successors]) env
    rw [patched] at patchedBounded
    have sizeEq : middle.blocks.size = before.blocks.size := by
      rw [patchTerm_run] at patched
      obtain ⟨_, rfl⟩ := Prod.mk.inj patched
      simp
    exact generatedTargets_patchBrs loop join pending env middle result after tail patchedBounded
      (targets.mono (Nat.le_of_eq sizeEq.symm)) (sizeEq ▸ joinBound)

theorem generatedTargets_patchBrs0 (loop : Option LoopCtx) (join : BlockId) :
    ∀ (pending : List BlockId) env before result after,
    patchBrs0 join pending env before = (result, after) →
    TargetsBounded before → LoopBuilderTargets loop before → join < before.blocks.size →
    TargetsBounded after ∧ LoopBuilderTargets loop after
  | [], env, before, result, after, run, bounded, targets, joinBound => by
    rw [patchBrs0, pure_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨bounded, targets⟩
  | block :: pending, env, before, result, after, run, bounded, targets, joinBound => by
    simp only [patchBrs0, bind_eq] at run
    obtain ⟨ignored, middle, patched, tail⟩ := run
    have patchedBounded := bounded.patchTerm block (.br join []) (by simpa [Term.successors]) env
    rw [patched] at patchedBounded
    have sizeEq : middle.blocks.size = before.blocks.size := by
      rw [patchTerm_run] at patched
      obtain ⟨_, rfl⟩ := Prod.mk.inj patched
      simp
    exact generatedTargets_patchBrs0 loop join pending env middle result after tail patchedBounded
      (targets.mono (Nat.le_of_eq sizeEq.symm)) (sizeEq ▸ joinBound)

theorem generatedTargets_newBlock_then (loop : Option LoopCtx) (types : List VTy)
    {next : (BlockId × List ValueId) → B α}
    (continuation : ∀ block ids env before result after,
      next (block, ids) env before = (result, after) → TargetsBounded before →
      LoopBuilderTargets loop before → block < before.blocks.size →
      TargetsBounded after ∧ LoopBuilderTargets loop after) :
    GeneratedTargetRun loop (newBlock types >>= next) := by
  intro env before result after run bounded targets
  obtain ⟨⟨block, ids⟩, middle, created, tail⟩ := bind_eq.mp run
  have checked := generatedTargets_newBlock loop types env before _ middle created bounded targets
  exact continuation block ids env middle result after tail checked.1 checked.2
    (generatedTargets_newBlock_bound created)

theorem generatedTargets_joinValue (loop : Option LoopCtx) (yes no : Option BlockId)
    (yesValue noValue : ValueId) : GeneratedTargetRun loop (joinValue yes yesValue no noValue) := by
  unfold joinValue
  split
  · exact GeneratedTargetRun.bind (generatedTargets_setCur loop none) fun _ => generatedTargets_pure loop _
  · apply GeneratedTargetRun.bind (generatedTargets_valTy loop _)
    intro ty
    apply generatedTargets_newBlock_then loop [ty]
    intro join ids env before result after run bounded targets joinBound
    simp only [bind_eq] at run
    obtain ⟨ignored, patched, patchRun, ignored', selected, selectRun, finished⟩ := run
    rw [pure_run] at finished
    obtain ⟨_, rfl⟩ := Prod.mk.inj finished
    have patchedChecked := generatedTargets_patchBrs loop join _ env before _ patched patchRun
      bounded targets joinBound
    exact generatedTargets_setCur loop (some join) env patched _ selected selectRun
      patchedChecked.1 patchedChecked.2

theorem generatedTargets_joinArms (loop : Option LoopCtx) (yes no : Option BlockId) :
    GeneratedTargetRun loop (joinArms yes no) := by
  unfold joinArms
  split
  · exact generatedTargets_setCur loop none
  · apply generatedTargets_newBlock_then loop []
    intro join ids env before result after run bounded targets joinBound
    obtain ⟨ignored, patched, patchRun, selectRun⟩ := bind_eq.mp run
    have patchedChecked := generatedTargets_patchBrs0 loop join _ env before _ patched patchRun
      bounded targets joinBound
    exact generatedTargets_setCur loop (some join) env patched result after selectRun
      patchedChecked.1 patchedChecked.2

theorem generatedTargets_fork_then (loop : Option LoopCtx) (condition : ValueId)
    {next : (BlockId × BlockId) → B α}
    (continuation : ∀ yes no env before result after,
      next (yes, no) env before = (result, after) → TargetsBounded before →
      LoopBuilderTargets loop before → yes < before.blocks.size → no < before.blocks.size →
      TargetsBounded after ∧ LoopBuilderTargets loop after) :
    GeneratedTargetRun loop (fork condition >>= next) := by
  intro env before result after run bounded targets
  obtain ⟨⟨yes, no⟩, middle, forked, tail⟩ := bind_eq.mp run
  have checked := generatedTargets_fork loop condition env before _ middle forked bounded targets
  obtain ⟨ids, size⟩ := fork_ids forked
  have yesId := congrArg Prod.fst ids
  have noId := congrArg Prod.snd ids
  exact continuation yes no env middle result after tail checked.1 checked.2 (by simp_all) (by simp_all)

theorem generatedTargets_ifE_core (loop : Option LoopCtx) (condition : ValueId)
    {yes no : B ValueId} (yesRun : GeneratedTargetRun loop yes) (noRun : GeneratedTargetRun loop no) :
    GeneratedTargetRun loop (whenLive 0 fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let yesValue ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let noValue ← no
      let noEnd ← curBlock
      joinValue yesEnd yesValue noEnd noValue) := by
  refine generatedTargets_whenLive loop _ fun _ => ?_
  refine GeneratedTargetRun.bind (generatedTargets_fork loop condition) fun blocks => ?_
  refine GeneratedTargetRun.bind (generatedTargets_setCur loop _) fun _ => ?_
  refine GeneratedTargetRun.bind yesRun fun yesValue => ?_
  refine GeneratedTargetRun.bind (generatedTargets_curBlock loop) fun yesEnd => ?_
  refine GeneratedTargetRun.bind (generatedTargets_setCur loop _) fun _ => ?_
  refine GeneratedTargetRun.bind noRun fun noValue => ?_
  refine GeneratedTargetRun.bind (generatedTargets_curBlock loop) fun noEnd => ?_
  exact generatedTargets_joinValue loop yesEnd noEnd yesValue noValue

theorem generatedTargets_ifE_recorded_core (loop : Option LoopCtx) (condition : ValueId) (sourceScope : ScopeId)
    {yes no : B ValueId} (yesRun : GeneratedTargetRun loop yes) (noRun : GeneratedTargetRun loop no) :
    GeneratedTargetRun loop (whenLive 0 fun _ => do
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
  refine generatedTargets_whenLive loop _ fun _ => ?_
  refine GeneratedTargetRun.bind (generatedTargets_fork loop condition) fun blocks => ?_
  refine GeneratedTargetRun.bind (generatedTargets_setCur loop _) fun _ => ?_
  refine GeneratedTargetRun.bind yesRun fun yesValue => ?_
  refine GeneratedTargetRun.bind (generatedTargets_curBlock loop) fun yesEnd => ?_
  refine GeneratedTargetRun.bind (generatedTargets_setCur loop _) fun _ => ?_
  refine GeneratedTargetRun.bind noRun fun noValue => ?_
  refine GeneratedTargetRun.bind (generatedTargets_curBlock loop) fun noEnd => ?_
  refine GeneratedTargetRun.bind (generatedTargets_joinValue loop yesEnd noEnd yesValue noValue) fun value => ?_
  exact GeneratedTargetRun.bind (generatedTargets_recordValueRootRecipe loop value sourceScope) fun _ => generatedTargets_pure loop value

theorem generatedTargets_ifS_some_core (loop : Option LoopCtx) (condition : ValueId)
    {yes no : B ValueId} (yesRun : GeneratedTargetRun loop yes) (noRun : GeneratedTargetRun loop no) :
    GeneratedTargetRun loop (whenLive () fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let _ ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let _ ← no
      let noEnd ← curBlock
      joinArms yesEnd noEnd) := by
  refine generatedTargets_whenLive loop _ fun _ => ?_
  refine GeneratedTargetRun.bind (generatedTargets_fork loop condition) fun blocks => ?_
  refine GeneratedTargetRun.bind (generatedTargets_setCur loop _) fun _ => ?_
  refine GeneratedTargetRun.bind yesRun fun yesValue => ?_
  refine GeneratedTargetRun.bind (generatedTargets_curBlock loop) fun yesEnd => ?_
  refine GeneratedTargetRun.bind (generatedTargets_setCur loop _) fun _ => ?_
  refine GeneratedTargetRun.bind noRun fun noValue => ?_
  refine GeneratedTargetRun.bind (generatedTargets_curBlock loop) fun noEnd => ?_
  exact generatedTargets_joinArms loop yesEnd noEnd

theorem generatedTargets_assert_core (loop : Option LoopCtx) (condition : ValueId) (origin : OriginId) :
    GeneratedTargetRun loop (whenLive () fun _ => do
      let (success, failure) ← fork condition
      setCur (some failure)
      emitTerm (.abort .assert (some origin))
      setCur (some success)) := by
  refine generatedTargets_whenLive loop _ fun _ => ?_
  refine GeneratedTargetRun.bind (generatedTargets_fork loop condition) fun blocks => ?_
  refine GeneratedTargetRun.bind (generatedTargets_setCur loop _) fun _ => ?_
  refine GeneratedTargetRun.bind (generatedTargets_emitTerm loop _ (by simp [Term.successors])) fun _ => ?_
  exact generatedTargets_setCur loop _

theorem generatedTargets_ifS_none_core (loop : Option LoopCtx) (condition : ValueId)
    {yes : B ValueId} (yesRun : GeneratedTargetRun loop yes) (yesAdvance : AdvB yes) :
    GeneratedTargetRun loop (whenLive () fun _ => do
      let (yesBlock, join) ← fork condition
      setCur (some yesBlock)
      let _ ← yes
      emitTerm (.br join [])
      setCur (some join)) := by
  refine generatedTargets_whenLive loop _ fun _ => ?_
  apply generatedTargets_fork_then loop condition
  intro yesBlock join env before result after run bounded targets yesBound joinBound
  simp only [bind_eq] at run
  obtain ⟨ignored, selected, selectedRun, value, body, bodyRun, ignored', closed, closedRun, last⟩ := run
  have selectedChecked := generatedTargets_setCur loop _ env before _ selected selectedRun bounded targets
  have bodyChecked := yesRun env selected value body bodyRun selectedChecked.1 selectedChecked.2
  have selectedSize : selected.blocks.size = before.blocks.size := by rw [setCur_blocks selectedRun]
  have bodyJoin : join < body.blocks.size := Nat.lt_of_lt_of_le (selectedSize ▸ joinBound)
    (yesAdvance env selected value body bodyRun).ext.1
  have closedChecked := bodyChecked.1.emitTerm (.br join []) (by simpa [Term.successors]) env
  rw [closedRun] at closedChecked
  exact generatedTargets_setCur loop _ env closed result after last closedChecked
    (bodyChecked.2.mono (adv_emitTerm closedRun).ext.1)

theorem generatedTargets_scFork (loop : Option LoopCtx) (isAnd : Bool) (value : ValueId) :
    GeneratedTargetRun loop (scFork isAnd value) := by
  intro env before result after run bounded targets
  have finalTargets := targets.mono (advB_scFork isAnd value env before result after run).ext.1
  refine ⟨?_, finalTargets⟩
  have expression : scFork isAnd value = (do
      let (rhs, _) ← newBlock []
      let (join, parameters) ← newBlock [.data .bool]
      emitTerm (if isAnd then .condbr value rhs [] join [value] else .condbr value join [value] rhs [])
      pure (rhs, join, parameters.headD 0)) := by cases isAnd <;> rfl
  rw [expression] at run
  simp only [bind_eq] at run
  obtain ⟨⟨rhs, rhsParams⟩, first, rhsRun, ⟨join, joinParams⟩, second, joinRun,
    ignored, closed, closedRun, finished⟩ := run
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  have firstResult := generatedTargets_newBlock loop [] env before _ first rhsRun bounded targets
  have secondResult := generatedTargets_newBlock loop [.data .bool] env first _ second joinRun firstResult.1 firstResult.2
  have rhsBound := Nat.lt_of_lt_of_le (generatedTargets_newBlock_bound rhsRun) (adv_newBlock1 joinRun).ext.1
  have joinBound := generatedTargets_newBlock_bound joinRun
  have closedChecked := secondResult.1.emitTerm
    (if isAnd then .condbr value rhs [] join [value] else .condbr value join [value] rhs []) (by
      cases isAnd <;> simp [Term.successors, rhsBound, joinBound]) env
  rw [closedRun] at closedChecked
  exact closedChecked

theorem generatedTargets_shortCircuit (loop : Option LoopCtx) (isAnd : Bool) (value : ValueId)
    {rhs : B ValueId} (rhsRun : GeneratedTargetRun loop rhs) (rhsAdvance : AdvB rhs) :
    GeneratedTargetRun loop (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  refine generatedTargets_whenLive loop _ fun _ => ?_
  intro env before result after run bounded targets
  simp only [bind_eq] at run
  obtain ⟨⟨rhsBlock, join, parameter⟩, forked, forkRun, ignored, selected, selectedRun,
    rhsValue, body, bodyRun, ignored', closed, closedRun, ignored'', final, finalRun, finished⟩ := run
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  have forkChecked := generatedTargets_scFork loop isAnd value env before _ forked forkRun bounded targets
  have selectedChecked := generatedTargets_setCur loop _ env forked _ selected selectedRun forkChecked.1 forkChecked.2
  have bodyChecked := rhsRun env selected rhsValue body bodyRun selectedChecked.1 selectedChecked.2
  obtain ⟨ids, size⟩ := scFork_ids forkRun
  have joinId := congrArg (fun value => value.2.1) ids
  have joinBound : join < selected.blocks.size := by
    rw [setCur_blocks selectedRun]
    simp_all
  have bodyJoin := Nat.lt_of_lt_of_le joinBound (rhsAdvance env selected rhsValue body bodyRun).ext.1
  have closedChecked := bodyChecked.1.emitTerm (.br join [rhsValue]) (by simpa [Term.successors]) env
  rw [closedRun] at closedChecked
  exact generatedTargets_setCur loop _ env closed _ final finalRun closedChecked
    (bodyChecked.2.mono (adv_emitTerm closedRun).ext.1)

end Goose.Lower
