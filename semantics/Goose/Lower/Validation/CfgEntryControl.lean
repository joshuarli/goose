import Goose.Lower.Validation.CfgEntryActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Lower.Validation

theorem entry_newBlock_bound {types : List VTy} {env : LEnv} {before after : LS}
    {result : BlockId × List ValueId} (run : newBlock types env before = (result, after)) (nonempty : 0 < before.blocks.size) :
    result.1 ≠ 0 := by
  rw [entry_newBlock_run] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  exact Nat.ne_of_gt nonempty

theorem entry_curBlock (loop : Option LoopCtx) : EntryRun loop curBlock := by
  apply EntryRun.unchanged
  intros
  rw [curBlock_run]

theorem entry_isLive (loop : Option LoopCtx) : EntryRun loop isLive := by
  apply EntryRun.unchanged
  intros
  rfl

theorem entry_whenLive (loop : Option LoopCtx) (fallback : α) {action : BlockId → B α}
    (body : ∀ block, EntryRun loop (action block)) :
    EntryRun loop (whenLive fallback action) := by
  unfold whenLive
  refine EntryRun.bind (entry_curBlock loop) fun current => ?_
  cases current with
  | none => exact entry_pure loop fallback
  | some block => exact body block

theorem entry_regrowOf (loop : Option LoopCtx) (owner : Option ValueId) :
    EntryRun loop (regrowOf owner) := by
  cases owner with
  | none => exact entry_pure loop false
  | some owner => exact entry_growOwner loop owner

theorem entry_eachSampled (loop : Option LoopCtx) (regrow : Bool) (view : ValueId) :
    EntryRun loop (eachSampled regrow view) := by
  cases regrow
  · exact entry_emitDef loop _
  · exact entry_pure loop _

theorem entry_eachLen (loop : Option LoopCtx) (regrow : Bool) (owner : Option ValueId)
    (sampled : ValueId) : EntryRun loop (eachLen regrow owner sampled) := by
  cases regrow
  · exact entry_pure loop _
  · exact entry_emitDef loop _

theorem entry_eachElemValue (loop : Option LoopCtx) (slot : VarId) (byRef : Bool)
    (element : ValueId) : EntryRun loop (eachElemValue slot byRef element) := by
  unfold eachElemValue
  cases byRef
  · exact entry_emitDef loop _
  · refine EntryRun.bind (entry_read loop) fun env => ?_
    cases env.vars[slot]? with
    | none => exact entry_pure loop _
    | some declaration =>
      dsimp only
      cases declaration.ty <;> first
        | exact entry_pure loop _
        | exact entry_borrowTo loop _ _

theorem entry_fork (loop : Option LoopCtx) (condition : ValueId) :
    EntryRun loop (fork condition) := by
  intro env before result after run bounded targets
  have finalTargets := targets
  refine ⟨?_, finalTargets⟩
  simp only [fork, bind_eq] at run
  obtain ⟨⟨yes, yesParams⟩, first, yesRun, ⟨no, noParams⟩, second, noRun,
    ignoredTerm, third, branched, finished⟩ := run
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  have firstBounded := (entry_newBlock loop [] env before _ first yesRun bounded targets).1
  have secondResult := entry_newBlock loop [] env first _ second noRun firstBounded
    (targets)
  have yesBound := (entry_newBlock_bound yesRun bounded.positive)
  have noBound := entry_newBlock_bound noRun firstBounded.positive
  have closed := secondResult.1.emitTerm (.condbr condition yes [] no []) (by
    intro target member
    simp only [Term.successors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact yesBound
    · exact noBound) env
  rw [branched] at closed
  exact closed

theorem entry_patchBrs (loop : Option LoopCtx) (join : BlockId) :
    ∀ (pending : List (BlockId × ValueId)) env before result after,
    patchBrs join pending env before = (result, after) →
    EntryTargets before → LoopEntryTargets loop → join ≠ 0 →
    EntryTargets after ∧ LoopEntryTargets loop
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
    exact entry_patchBrs loop join pending env middle result after tail patchedBounded
      (targets) (joinBound)

theorem entry_patchBrs0 (loop : Option LoopCtx) (join : BlockId) :
    ∀ (pending : List BlockId) env before result after,
    patchBrs0 join pending env before = (result, after) →
    EntryTargets before → LoopEntryTargets loop → join ≠ 0 →
    EntryTargets after ∧ LoopEntryTargets loop
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
    exact entry_patchBrs0 loop join pending env middle result after tail patchedBounded
      (targets) (joinBound)

theorem entry_newBlock_then (loop : Option LoopCtx) (types : List VTy)
    {next : (BlockId × List ValueId) → B α}
    (continuation : ∀ block ids env before result after,
      next (block, ids) env before = (result, after) → EntryTargets before →
      LoopEntryTargets loop → block ≠ 0 →
      EntryTargets after ∧ LoopEntryTargets loop) :
    EntryRun loop (newBlock types >>= next) := by
  intro env before result after run bounded targets
  obtain ⟨⟨block, ids⟩, middle, created, tail⟩ := bind_eq.mp run
  have checked := entry_newBlock loop types env before _ middle created bounded targets
  exact continuation block ids env middle result after tail checked.1 checked.2
    (entry_newBlock_bound created bounded.positive)

theorem entry_joinValue (loop : Option LoopCtx) (yes no : Option BlockId)
    (yesValue noValue : ValueId) : EntryRun loop (joinValue yes yesValue no noValue) := by
  unfold joinValue
  split
  · exact EntryRun.bind (entry_setCur loop none) fun _ => entry_pure loop _
  · apply EntryRun.bind (entry_valTy loop _)
    intro ty
    apply entry_newBlock_then loop [ty]
    intro join ids env before result after run bounded targets joinBound
    simp only [bind_eq] at run
    obtain ⟨ignored, patched, patchRun, ignored', selected, selectRun, finished⟩ := run
    rw [pure_run] at finished
    obtain ⟨_, rfl⟩ := Prod.mk.inj finished
    have patchedChecked := entry_patchBrs loop join _ env before _ patched patchRun
      bounded targets joinBound
    exact entry_setCur loop (some join) env patched _ selected selectRun
      patchedChecked.1 patchedChecked.2

theorem entry_joinArms (loop : Option LoopCtx) (yes no : Option BlockId) :
    EntryRun loop (joinArms yes no) := by
  unfold joinArms
  split
  · exact entry_setCur loop none
  · apply entry_newBlock_then loop []
    intro join ids env before result after run bounded targets joinBound
    obtain ⟨ignored, patched, patchRun, selectRun⟩ := bind_eq.mp run
    have patchedChecked := entry_patchBrs0 loop join _ env before _ patched patchRun
      bounded targets joinBound
    exact entry_setCur loop (some join) env patched result after selectRun
      patchedChecked.1 patchedChecked.2

theorem entry_fork_then (loop : Option LoopCtx) (condition : ValueId)
    {next : (BlockId × BlockId) → B α}
    (continuation : ∀ yes no env before result after,
      next (yes, no) env before = (result, after) → EntryTargets before →
      LoopEntryTargets loop → yes ≠ 0 → no ≠ 0 →
      EntryTargets after ∧ LoopEntryTargets loop) :
    EntryRun loop (fork condition >>= next) := by
  intro env before result after run bounded targets
  obtain ⟨⟨yes, no⟩, middle, forked, tail⟩ := bind_eq.mp run
  have checked := entry_fork loop condition env before _ middle forked bounded targets
  obtain ⟨ids, size⟩ := fork_ids forked
  have yesId := congrArg Prod.fst ids
  have noId := congrArg Prod.snd ids
  exact continuation yes no env middle result after tail checked.1 checked.2 (by have positive := bounded.positive; dsimp only at yesId; nat_omega)
    (by dsimp only at noId; nat_omega)

theorem entry_ifE_core (loop : Option LoopCtx) (condition : ValueId) (sourceScope : ScopeId)
    {yes no : B ValueId} (yesRun : EntryRun loop yes) (noRun : EntryRun loop no) :
    EntryRun loop (whenLive 0 fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let yesValue ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let noValue ← no
      let noEnd ← curBlock
      let result ← joinValue yesEnd yesValue noEnd noValue
      recordValueRootRecipe result sourceScope
      pure result) := by
  refine entry_whenLive loop _ fun _ => ?_
  refine EntryRun.bind (entry_fork loop condition) fun blocks => ?_
  refine EntryRun.bind (entry_setCur loop _) fun _ => ?_
  refine EntryRun.bind yesRun fun yesValue => ?_
  refine EntryRun.bind (entry_curBlock loop) fun yesEnd => ?_
  refine EntryRun.bind (entry_setCur loop _) fun _ => ?_
  refine EntryRun.bind noRun fun noValue => ?_
  refine EntryRun.bind (entry_curBlock loop) fun noEnd => ?_
  refine EntryRun.bind (entry_joinValue loop yesEnd noEnd yesValue noValue) fun result => ?_
  exact EntryRun.bind (entry_recordValueRootRecipe loop result sourceScope) fun _ => entry_pure loop result

theorem entry_ifS_some_core (loop : Option LoopCtx) (condition : ValueId)
    {yes no : B ValueId} (yesRun : EntryRun loop yes) (noRun : EntryRun loop no) :
    EntryRun loop (whenLive () fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let _ ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let _ ← no
      let noEnd ← curBlock
      joinArms yesEnd noEnd) := by
  refine entry_whenLive loop _ fun _ => ?_
  refine EntryRun.bind (entry_fork loop condition) fun blocks => ?_
  refine EntryRun.bind (entry_setCur loop _) fun _ => ?_
  refine EntryRun.bind yesRun fun yesValue => ?_
  refine EntryRun.bind (entry_curBlock loop) fun yesEnd => ?_
  refine EntryRun.bind (entry_setCur loop _) fun _ => ?_
  refine EntryRun.bind noRun fun noValue => ?_
  refine EntryRun.bind (entry_curBlock loop) fun noEnd => ?_
  exact entry_joinArms loop yesEnd noEnd

theorem entry_assert_core (loop : Option LoopCtx) (condition : ValueId) (origin : OriginId) :
    EntryRun loop (whenLive () fun _ => do
      let (success, failure) ← fork condition
      setCur (some failure)
      emitTerm (.abort .assert (some origin))
      setCur (some success)) := by
  refine entry_whenLive loop _ fun _ => ?_
  refine EntryRun.bind (entry_fork loop condition) fun blocks => ?_
  refine EntryRun.bind (entry_setCur loop _) fun _ => ?_
  refine EntryRun.bind (entry_emitTerm loop _ (by simp [Term.successors])) fun _ => ?_
  exact entry_setCur loop _

theorem entry_ifS_none_core (loop : Option LoopCtx) (condition : ValueId)
    {yes : B ValueId} (yesRun : EntryRun loop yes) (_yesAdvance : AdvB yes) :
    EntryRun loop (whenLive () fun _ => do
      let (yesBlock, join) ← fork condition
      setCur (some yesBlock)
      let _ ← yes
      emitTerm (.br join [])
      setCur (some join)) := by
  refine entry_whenLive loop _ fun _ => ?_
  apply entry_fork_then loop condition
  intro yesBlock join env before result after run bounded targets yesBound joinBound
  simp only [bind_eq] at run
  obtain ⟨ignored, selected, selectedRun, value, body, bodyRun, ignored', closed, closedRun, last⟩ := run
  have selectedChecked := entry_setCur loop _ env before _ selected selectedRun bounded targets
  have bodyChecked := yesRun env selected value body bodyRun selectedChecked.1 selectedChecked.2
  have selectedSize : selected.blocks.size = before.blocks.size := by rw [setCur_blocks selectedRun]
  have bodyJoin : join ≠ 0 := (joinBound)
  have closedChecked := bodyChecked.1.emitTerm (.br join []) (by simpa [Term.successors]) env
  rw [closedRun] at closedChecked
  exact entry_setCur loop _ env closed result after last closedChecked
    (bodyChecked.2)

theorem entry_scFork (loop : Option LoopCtx) (isAnd : Bool) (value : ValueId) :
    EntryRun loop (scFork isAnd value) := by
  intro env before result after run bounded targets
  have finalTargets := targets
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
  have firstResult := entry_newBlock loop [] env before _ first rhsRun bounded targets
  have secondResult := entry_newBlock loop [.data .bool] env first _ second joinRun firstResult.1 firstResult.2
  have rhsBound := (entry_newBlock_bound rhsRun bounded.positive)
  have joinBound := entry_newBlock_bound joinRun firstResult.1.positive
  have closedChecked := secondResult.1.emitTerm
    (if isAnd then .condbr value rhs [] join [value] else .condbr value join [value] rhs []) (by
      cases isAnd <;> simp [Term.successors, rhsBound, joinBound]) env
  rw [closedRun] at closedChecked
  exact closedChecked

theorem entry_shortCircuit (loop : Option LoopCtx) (isAnd : Bool) (value : ValueId)
    {rhs : B ValueId} (rhsRun : EntryRun loop rhs) (_rhsAdvance : AdvB rhs) :
    EntryRun loop (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  refine entry_whenLive loop _ fun _ => ?_
  intro env before result after run bounded targets
  simp only [bind_eq] at run
  obtain ⟨⟨rhsBlock, join, parameter⟩, forked, forkRun, ignored, selected, selectedRun,
    rhsValue, body, bodyRun, ignored', closed, closedRun, ignored'', final, finalRun, finished⟩ := run
  rw [pure_run] at finished
  obtain ⟨_, rfl⟩ := Prod.mk.inj finished
  have forkChecked := entry_scFork loop isAnd value env before _ forked forkRun bounded targets
  have selectedChecked := entry_setCur loop _ env forked _ selected selectedRun forkChecked.1 forkChecked.2
  have bodyChecked := rhsRun env selected rhsValue body bodyRun selectedChecked.1 selectedChecked.2
  obtain ⟨ids, size⟩ := scFork_ids forkRun
  have joinId := congrArg (fun value => value.2.1) ids
  have joinBound : join ≠ 0 := by
    dsimp only at joinId
    nat_omega
  have bodyJoin := joinBound
  have closedChecked := bodyChecked.1.emitTerm (.br join [rhsValue]) (by simpa [Term.successors]) env
  rw [closedRun] at closedChecked
  exact entry_setCur loop _ env closed _ final finalRun closedChecked
    (bodyChecked.2)

end Goose.Lower.Validation
