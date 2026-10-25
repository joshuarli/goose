import Goose.Lower.GeneratedTargetsControl

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Lower.Validation

theorem generatedTargets_rangeBack (ty : IntTy) (counter header : ValueId)
    {env : LEnv} {before after : LS} {result : Unit}
    (run : rangeBack ty counter header env before = (result, after))
    (bounded : TargetsBounded before) (headerBound : header < before.blocks.size) :
    TargetsBounded after := by
  unfold rangeBack at run
  obtain ⟨live, middle, tested, tail⟩ := bind_eq.mp run
  have same : middle = before := by
    have stable : (isLive env before).2 = before := rfl
    rw [tested] at stable
    exact stable
  subst middle
  cases live
  · simp only [Bool.false_eq_true, ite_false, pure_run] at tail
    obtain ⟨_, rfl⟩ := Prod.mk.inj tail
    exact bounded
  · simp only [ite_true, bind_eq] at tail
    obtain ⟨value, middle, emitted, branched⟩ := tail
    have checked := bounded.emitDef (.next ty counter) env
    rw [emitted] at checked
    have bound := Nat.lt_of_lt_of_le headerBound (adv_emitDef emitted).ext.1
    have closed := checked.emitTerm (.br header [value]) (by simpa [Term.successors]) env
    rw [branched] at closed
    exact closed

theorem generatedTargets_loopBody (header condition : ValueId) {body : Nat → BlockId → B ValueId}
    {back : B Unit} (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyChecked : ∀ depth exit env before result after,
      body depth exit env before = (result, after) → TargetsBounded before →
      header < before.blocks.size → exit < before.blocks.size → TargetsBounded after)
    (backChecked : ∀ env before result after, back env before = (result, after) →
      TargetsBounded before → header < before.blocks.size → TargetsBounded after)
    {env : LEnv} {before after : LS} {result : Unit}
    (run : loopBody condition body back env before = (result, after))
    (bounded : TargetsBounded before) (headerBound : header < before.blocks.size) :
    TargetsBounded after := by
  unfold loopBody at run
  simp only [bind_eq] at run
  obtain ⟨saved, first, savedRun, ⟨bodyBlock, exit⟩, forked, forkRun, ignored, selected, selectedRun,
    value, bodyEnd, bodyRun, ignored', backEnd, backRun, selectExit⟩ := run
  rw [get_apply] at savedRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj savedRun
  have forkChecked := generatedTargets_fork none condition env before _ forked forkRun bounded trivial
  have selectedChecked := generatedTargets_setCur none _ env forked _ selected selectedRun forkChecked.1 trivial
  have forkAdvance := advB_fork condition env before _ forked forkRun
  have selectedSize := setCur_blocks selectedRun
  have headerSelected : header < selected.blocks.size := by
    rw [selectedSize]
    exact Nat.lt_of_lt_of_le headerBound forkAdvance.ext.1
  obtain ⟨ids, size⟩ := fork_ids forkRun
  have exitId := congrArg Prod.snd ids
  have exitSelected : exit < selected.blocks.size := by rw [selectedSize]; simp_all
  have bodyResult := bodyChecked before.stack.length exit env selected value bodyEnd bodyRun
    selectedChecked.1 headerSelected exitSelected
  have bodyHeader := Nat.lt_of_lt_of_le headerSelected
    (bodyAdvance before.stack.length exit env selected value bodyEnd bodyRun).ext.1
  have backResult := backChecked env bodyEnd _ backEnd backRun bodyResult bodyHeader
  exact (generatedTargets_setCur none _ env backEnd result after selectExit backResult trivial).1

theorem generatedTargets_lowerWhile (header : BlockId) {condition : B ValueId}
    {body : Nat → BlockId → B ValueId} (conditionChecked : GeneratedTargetRun none condition)
    (conditionAdvance : AdvB condition) (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyChecked : ∀ depth exit env before result after,
      body depth exit env before = (result, after) → TargetsBounded before →
      header < before.blocks.size → exit < before.blocks.size → TargetsBounded after)
    {env : LEnv} {before after : LS} {result : Unit}
    (run : lowerWhile header condition body env before = (result, after))
    (bounded : TargetsBounded before) (headerBound : header < before.blocks.size) :
    TargetsBounded after := by
  unfold lowerWhile at run
  obtain ⟨value, middle, conditionRun, tail⟩ := bind_eq.mp run
  have checked := conditionChecked env before value middle conditionRun bounded trivial
  have bound := Nat.lt_of_lt_of_le headerBound (conditionAdvance env before value middle conditionRun).ext.1
  cases current : middle.cur with
  | none =>
    rw [whenLive_none _ _ env current] at tail
    obtain ⟨_, rfl⟩ := Prod.mk.inj tail
    exact checked.1
  | some block =>
    rw [whenLive_some _ _ env current] at tail
    apply generatedTargets_loopBody header value bodyAdvance bodyChecked ?_ tail checked.1 bound
    intro env state result after run bounded headerBound
    have branched := bounded.emitTerm (.br header []) (by simpa [Term.successors]) env
    rw [run] at branched
    exact branched

theorem generatedTargets_lowerRange (hint : IntTy) (counter bound header : ValueId)
    {body : Nat → BlockId → B ValueId} (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyChecked : ∀ depth exit env before result after,
      body depth exit env before = (result, after) → TargetsBounded before →
      header < before.blocks.size → exit < before.blocks.size → TargetsBounded after)
    {env : LEnv} {before after : LS} {result : Unit}
    (run : lowerRange hint counter bound header body env before = (result, after))
    (bounded : TargetsBounded before) (headerBound : header < before.blocks.size) :
    TargetsBounded after := by
  unfold lowerRange at run
  obtain ⟨condition, middle, compareRun, tail⟩ := bind_eq.mp run
  have checked := bounded.emitDef (.cmp .lt hint counter bound) env
  rw [compareRun] at checked
  have bound := Nat.lt_of_lt_of_le headerBound (adv_emitDef compareRun).ext.1
  exact generatedTargets_loopBody header condition bodyAdvance bodyChecked
    (fun _ _ _ _ run bounded bound => generatedTargets_rangeBack hint counter header run bounded bound)
    tail checked bound

theorem generatedTargets_lowerEach (regrow : Bool) (owner : Option ValueId)
    (sampled header counter : ValueId) {body : Nat → BlockId → B ValueId}
    (bodyAdvance : ∀ depth exit, AdvB (body depth exit))
    (bodyChecked : ∀ depth exit env before result after,
      body depth exit env before = (result, after) → TargetsBounded before →
      header < before.blocks.size → exit < before.blocks.size → TargetsBounded after)
    {env : LEnv} {before after : LS} {result : Unit}
    (run : lowerEach regrow owner sampled header counter body env before = (result, after))
    (bounded : TargetsBounded before) (headerBound : header < before.blocks.size) :
    TargetsBounded after := by
  unfold lowerEach at run
  simp only [bind_eq] at run
  obtain ⟨length, measured, lengthRun, condition, compared, compareRun, tail⟩ := run
  have measuredChecked := generatedTargets_eachLen none regrow owner sampled env before length measured
    lengthRun bounded trivial
  have measuredHeader := Nat.lt_of_lt_of_le headerBound
    (advB_eachLen regrow owner sampled env before length measured lengthRun).ext.1
  have comparedChecked := measuredChecked.1.emitDef (.cmp .lt .i64 counter length) env
  rw [compareRun] at comparedChecked
  have comparedHeader := Nat.lt_of_lt_of_le measuredHeader (adv_emitDef compareRun).ext.1
  exact generatedTargets_loopBody header condition bodyAdvance bodyChecked
    (fun _ _ _ _ run bounded bound => generatedTargets_rangeBack .i64 counter header run bounded bound)
    tail comparedChecked comparedHeader

theorem generatedTargets_header0 (loop : Option LoopCtx) {tail : BlockId → B Unit}
    (advance : ∀ header, AdvB (tail header))
    (checked : ∀ header env before result after,
      tail header env before = (result, after) → TargetsBounded before →
      header < before.blocks.size → TargetsBounded after) :
    GeneratedTargetRun loop (do
      let (header, _) ← newBlock []
      emitTerm (.br header [])
      setCur (some header)
      tail header) := by
  apply GeneratedTargetRun.withLoop (loop := loop) (advance := advB_header0 advance)
  apply generatedTargets_newBlock_then none []
  intro header ids env before result after run bounded targets headerBound
  simp only [bind_eq] at run
  obtain ⟨ignored, branched, branchRun, ignored', selected, selectRun, tailRun⟩ := run
  have branchChecked := bounded.emitTerm (.br header []) (by simpa [Term.successors]) env
  rw [branchRun] at branchChecked
  have branchBound := Nat.lt_of_lt_of_le headerBound (adv_emitTerm branchRun).ext.1
  have selectedChecked := generatedTargets_setCur none _ env branched _ selected selectRun branchChecked trivial
  have selectedBound : header < selected.blocks.size := by
    rw [setCur_blocks selectRun]
    exact branchBound
  exact ⟨checked header env selected result after tailRun selectedChecked.1 selectedBound, trivial⟩

theorem generatedTargets_header1 (loop : Option LoopCtx) (ty : VTy) (initial : ValueId)
    {tail : BlockId → ValueId → B Unit}
    (advance : ∀ header counter, AdvB (tail header counter))
    (checked : ∀ header counter env before result after,
      tail header counter env before = (result, after) → TargetsBounded before →
      header < before.blocks.size → TargetsBounded after) :
    GeneratedTargetRun loop (do
      let (header, ids) ← newBlock [ty]
      let counter := ids.headD 0
      emitTerm (.br header [initial])
      setCur (some header)
      tail header counter) := by
  apply GeneratedTargetRun.withLoop (loop := loop) (advance := advB_header1 ty initial advance)
  apply generatedTargets_newBlock_then none [ty]
  intro header ids env before result after run bounded targets headerBound
  simp only [bind_eq] at run
  obtain ⟨ignored, branched, branchRun, ignored', selected, selectRun, tailRun⟩ := run
  have branchChecked := bounded.emitTerm (.br header [initial]) (by simpa [Term.successors]) env
  rw [branchRun] at branchChecked
  have branchBound := Nat.lt_of_lt_of_le headerBound (adv_emitTerm branchRun).ext.1
  have selectedChecked := generatedTargets_setCur none _ env branched _ selected selectRun branchChecked trivial
  have selectedBound : header < selected.blocks.size := by
    rw [setCur_blocks selectRun]
    exact branchBound
  exact ⟨checked header (ids.headD 0) env selected result after tailRun selectedChecked.1 selectedBound, trivial⟩

end Goose.Lower
