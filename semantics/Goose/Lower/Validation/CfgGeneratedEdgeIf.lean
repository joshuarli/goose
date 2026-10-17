import Goose.Lower.Validation.CfgGeneratedEdgeActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem generated_edge_ifE_core (env : LEnv) (context : Option LoopCtx) (condition : ValueId) (ty : VTy)
    {yes no : B ValueId} (yesEdges : GeneratedEdgeRun env context yes) (noEdges : GeneratedEdgeRun env context no)
    (yesTyped : ∀ before value after, yes env before = (value, after) → GeneratedBuilderState before →
      after.cur.isSome = true → after.vals[value]? = some (some ty))
    (noTyped : ∀ before value after, no env before = (value, after) → GeneratedBuilderState before →
      after.cur.isSome = true → after.vals[value]? = some (some ty)) :
    GeneratedEdgeRun env context (whenLive 0 fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let yesValue ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let noValue ← no
      let noEnd ← curBlock
      joinValue yesEnd yesValue noEnd noValue) := by
  intro before result after run generated loop checked
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨generated, .refl before, checked⟩
  | some block =>
    rw [whenLive_some _ _ env current] at run
    simp only [bind_eq] at run
    obtain ⟨⟨yesBlock, noBlock⟩, forked, forkRun, ignored, selectedYes, selectYes,
      yesValue, yesEnd, yesRun, yesCurrent, savedYes, saveYes, ignored', selectedNo, selectNo,
      noValue, noEnd, noRun, noCurrent, savedNo, saveNo, joined⟩ := run
    rw [curBlock_run] at saveYes
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj saveYes
    rw [curBlock_run] at saveNo
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj saveNo
    obtain ⟨forkedGenerated, forkExtension, forkChecked⟩ :=
      generated_edge_fork env context condition before _ forked forkRun generated loop checked
    obtain ⟨ids, size⟩ := fork_ids forkRun
    have yesId := congrArg Prod.fst ids
    have noId := congrArg Prod.snd ids
    have yesBound : yesBlock < forked.blocks.size := by dsimp only at yesId; nat_omega
    have noBound : noBlock < forked.blocks.size := by dsimp only at noId; nat_omega
    obtain ⟨selectedYesGenerated, selectYesExtension, selectedYesChecked⟩ :=
      generated_edge_setCur_at (some yesBlock) env forked selectedYes ignored selectYes forkedGenerated forkChecked
        (by intro target same; have equal := Option.some.inj same; simpa [← equal] using yesBound)
    have firstExtension := forkExtension.trans selectYesExtension
    obtain ⟨yesGenerated, yesExtension, yesChecked⟩ :=
      yesEdges selectedYes yesValue yesEnd yesRun selectedYesGenerated (loop.extend firstExtension) selectedYesChecked
    have throughYes := selectYesExtension.trans yesExtension
    have noStillBound : noBlock < yesEnd.blocks.size := Nat.lt_of_lt_of_le noBound throughYes.blocks.1
    obtain ⟨selectedNoGenerated, selectNoExtension, selectedNoChecked⟩ :=
      generated_edge_setCur_at (some noBlock) env yesEnd selectedNo ignored' selectNo yesGenerated yesChecked
        (by intro target same; have equal := Option.some.inj same; simpa [← equal] using noStillBound)
    have beforeNo := firstExtension.trans (yesExtension.trans selectNoExtension)
    obtain ⟨noGenerated, noExtension, noChecked⟩ :=
      noEdges selectedNo noValue noEnd noRun selectedNoGenerated (loop.extend beforeNo) selectedNoChecked
    have yesToFinal := selectNoExtension.trans noExtension
    have yesResult : ∀ target, yesEnd.cur = some target → noEnd.vals[yesValue]? = some (some ty) := by
      intro target live
      apply yesToFinal.types
      exact yesTyped selectedYes yesValue yesEnd yesRun selectedYesGenerated (by simp [live])
    have noResult : ∀ target, noEnd.cur = some target → noEnd.vals[noValue]? = some (some ty) := by
      intro target live
      exact noTyped selectedNo noValue noEnd noRun selectedNoGenerated (by simp [live])
    obtain ⟨joinExtension, joinChecked, _⟩ := edge_joinValue_at yesEnd.cur noEnd.cur yesValue noValue ty
      env noEnd after result joined noChecked yesResult noResult
    have afterGenerated := noGenerated.joinValue yesEnd.cur yesValue noEnd.cur noValue joined
    exact ⟨afterGenerated, firstExtension.trans (yesExtension.trans (selectNoExtension.trans (noExtension.trans joinExtension))), joinChecked⟩

theorem generated_edge_ifS_some_core (env : LEnv) (context : Option LoopCtx) (condition : ValueId)
    {yes no : B ValueId} (yesEdges : GeneratedEdgeRun env context yes) (noEdges : GeneratedEdgeRun env context no)
:
    GeneratedEdgeRun env context (whenLive () fun _ => do
      let (yesBlock, noBlock) ← fork condition
      setCur (some yesBlock)
      let _ ← yes
      let yesEnd ← curBlock
      setCur (some noBlock)
      let _ ← no
      let noEnd ← curBlock
      joinArms yesEnd noEnd) := by
  intro before result after run generated loop checked
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨generated, .refl before, checked⟩
  | some block =>
    rw [whenLive_some _ _ env current] at run
    simp only [bind_eq] at run
    obtain ⟨⟨yesBlock, noBlock⟩, forked, forkRun, ignored, selectedYes, selectYes,
      yesValue, yesEnd, yesRun, yesCurrent, savedYes, saveYes, ignored', selectedNo, selectNo,
      noValue, noEnd, noRun, noCurrent, savedNo, saveNo, joined⟩ := run
    rw [curBlock_run] at saveYes
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj saveYes
    rw [curBlock_run] at saveNo
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj saveNo
    obtain ⟨forkedGenerated, forkExtension, forkChecked⟩ :=
      generated_edge_fork env context condition before _ forked forkRun generated loop checked
    obtain ⟨ids, size⟩ := fork_ids forkRun
    have yesId := congrArg Prod.fst ids
    have noId := congrArg Prod.snd ids
    have yesBound : yesBlock < forked.blocks.size := by dsimp only at yesId; nat_omega
    have noBound : noBlock < forked.blocks.size := by dsimp only at noId; nat_omega
    obtain ⟨selectedYesGenerated, selectYesExtension, selectedYesChecked⟩ :=
      generated_edge_setCur_at (some yesBlock) env forked selectedYes ignored selectYes forkedGenerated forkChecked
        (by intro target same; have equal := Option.some.inj same; simpa [← equal] using yesBound)
    have firstExtension := forkExtension.trans selectYesExtension
    obtain ⟨yesGenerated, yesExtension, yesChecked⟩ :=
      yesEdges selectedYes yesValue yesEnd yesRun selectedYesGenerated (loop.extend firstExtension) selectedYesChecked
    have throughYes := selectYesExtension.trans yesExtension
    have noStillBound : noBlock < yesEnd.blocks.size := Nat.lt_of_lt_of_le noBound throughYes.blocks.1
    obtain ⟨selectedNoGenerated, selectNoExtension, selectedNoChecked⟩ :=
      generated_edge_setCur_at (some noBlock) env yesEnd selectedNo ignored' selectNo yesGenerated yesChecked
        (by intro target same; have equal := Option.some.inj same; simpa [← equal] using noStillBound)
    have beforeNo := firstExtension.trans (yesExtension.trans selectNoExtension)
    obtain ⟨noGenerated, noExtension, noChecked⟩ :=
      noEdges selectedNo noValue noEnd noRun selectedNoGenerated (loop.extend beforeNo) selectedNoChecked
    have beforeJoin := beforeNo.trans noExtension
    obtain ⟨afterGenerated, joinExtension, joinChecked⟩ :=
      generated_edge_joinArms env context yesEnd.cur noEnd.cur noEnd result after joined noGenerated
        (loop.extend beforeJoin) noChecked
    exact ⟨afterGenerated, beforeJoin.trans joinExtension, joinChecked⟩

theorem generated_edge_ifS_none_core (env : LEnv) (context : Option LoopCtx) (condition : ValueId)
    {yes : B ValueId} (yesEdges : GeneratedEdgeRun env context yes) :
    GeneratedEdgeRun env context (whenLive () fun _ => do
      let (yesBlock, join) ← fork condition
      setCur (some yesBlock)
      let _ ← yes
      emitTerm (.br join [])
      setCur (some join)) := by
  intro before result after run generated loop checked
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨generated, .refl before, checked⟩
  | some block =>
    rw [whenLive_some _ _ env current] at run
    simp only [bind_eq] at run
    obtain ⟨⟨yesBlock, join⟩, forked, forkRun, ignored, selected, selectRun,
      value, bodyEnd, yesRun, ignored', closed, closedRun, finalRun⟩ := run
    obtain ⟨forkedGenerated, forkExtension, forkChecked⟩ :=
      generated_edge_fork env context condition before _ forked forkRun generated loop checked
    have forkArguments := edgeArguments_fork current (generated.live block current) condition env
    rw [forkRun] at forkArguments
    have yesEdge : EdgeArguments forked yesBlock [] := forkArguments.1
    have joinEdge : EdgeArguments forked join [] := forkArguments.2
    obtain ⟨selectedGenerated, selectExtension, selectedChecked⟩ :=
      generated_edge_setCur_at (some yesBlock) env forked selected ignored selectRun forkedGenerated forkChecked
        (by intro target same; have equal := Option.some.inj same; simpa [← equal] using yesEdge.bound)
    have beforeBody := forkExtension.trans selectExtension
    obtain ⟨bodyGenerated, bodyExtension, bodyChecked⟩ := yesEdges selected value bodyEnd yesRun selectedGenerated
      (loop.extend beforeBody) selectedChecked
    have bodyJoin := joinEdge.extend (selectExtension.trans bodyExtension)
    obtain ⟨closedGenerated, closedExtension, closedChecked⟩ := generated_edge_emitTerm_at (.br join [])
      env bodyEnd closed ignored' closedRun bodyGenerated bodyChecked bodyJoin
    have closedJoin := bodyJoin.extend closedExtension
    obtain ⟨afterGenerated, finalExtension, afterChecked⟩ := generated_edge_setCur_at (some join)
      env closed after result finalRun closedGenerated closedChecked
        (by intro target same; have equal := Option.some.inj same; simpa [← equal] using closedJoin.bound)
    exact ⟨afterGenerated, beforeBody.trans (bodyExtension.trans (closedExtension.trans finalExtension)), afterChecked⟩

theorem generated_edge_assert_core (env : LEnv) (context : Option LoopCtx) (condition : ValueId) (origin : OriginId) :
    GeneratedEdgeRun env context (whenLive () fun _ => do
      let (success, failure) ← fork condition
      setCur (some failure)
      emitTerm (.abort .assert (some origin))
      setCur (some success)) := by
  intro before result after run generated loop checked
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨generated, .refl before, checked⟩
  | some block =>
    rw [whenLive_some _ _ env current] at run
    simp only [bind_eq] at run
    obtain ⟨⟨success, failure⟩, forked, forkRun, ignored, selected, selectRun,
      ignored', closed, closedRun, finalRun⟩ := run
    obtain ⟨forkedGenerated, forkExtension, forkChecked⟩ :=
      generated_edge_fork env context condition before _ forked forkRun generated loop checked
    have forkArguments := edgeArguments_fork current (generated.live block current) condition env
    rw [forkRun] at forkArguments
    have successEdge : EdgeArguments forked success [] := forkArguments.1
    have failureEdge : EdgeArguments forked failure [] := forkArguments.2
    obtain ⟨selectedGenerated, selectExtension, selectedChecked⟩ :=
      generated_edge_setCur_at (some failure) env forked selected ignored selectRun forkedGenerated forkChecked
        (by intro target same; have equal := Option.some.inj same; simpa [← equal] using failureEdge.bound)
    obtain ⟨closedGenerated, closedExtension, closedChecked⟩ := generated_edge_emitTerm_at (.abort .assert (some origin))
      env selected closed ignored' closedRun selectedGenerated selectedChecked trivial
    have closedSuccess := successEdge.extend (selectExtension.trans closedExtension)
    obtain ⟨afterGenerated, finalExtension, afterChecked⟩ := generated_edge_setCur_at (some success)
      env closed after result finalRun closedGenerated closedChecked
        (by intro target same; have equal := Option.some.inj same; simpa [← equal] using closedSuccess.bound)
    exact ⟨afterGenerated, forkExtension.trans (selectExtension.trans (closedExtension.trans finalExtension)), afterChecked⟩

end Goose.Lower.Validation
