import Goose.Lower.Validation.PermissionPreservationBodyTransfer
import Goose.Lower.Validation.PermissionInstructionStorageSourceBase
import Goose.Lower.Validation.PermissionPreservationControlEffects
import Goose.Lower.Validation.PermissionInstructionControl
import Goose.Lower.Finish

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem permission_types_finishFunction (impl : Core.Impl) (value : ValueId) :
    TypeRun (finishFunction impl value) := by
  unfold finishFunction
  refine TypeRun.bind types_read fun env => TypeRun.bind types_isLive fun live => ?_
  cases live with
  | false => exact TypeRun.pure _
  | true =>
    simp only [ite_true]
    split
    · exact TypeRun.bind (types_newBlock []) fun pair =>
        TypeRun.bind (types_emitTerm _) fun _ => TypeRun.bind (types_setCur _) fun _ => types_emitTerm _
    · exact types_emitTerm _

theorem permission_frame_finishFunction (loop : Option LoopCtx) (impl : Core.Impl) (value : ValueId) :
    GeneratedTargetFrameRun loop (finishFunction impl value) := by
  unfold finishFunction
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_read loop) fun env =>
    GeneratedTargetFrameRun.bind (generatedTargetFrame_isLive loop) fun live => ?_
  cases live with
  | false => exact generatedTargetFrame_pure loop _
  | true =>
    simp only [ite_true]
    split
    · apply generatedTargetFrame_header0 loop (tail := fun sink => emitTerm (.br sink []))
      intro header base env current after result extension frames framed fresh headerRow run
      refine ⟨framed.emitTermAt run ?_, (advB_emitTerm _ _ _ _ _ run).ext⟩
      intro target successor bounded
      have same : target = header := by simpa [Term.successors] using successor
      subst target
      exact (Nat.not_lt_of_ge fresh bounded).elim
    · exact generatedTargetFrame_emitNoSuccessors loop _ (by simp [Term.successors])

theorem newPermissions_finishFunction {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Unit} {impl : Core.Impl} {value : ValueId}
    (run : finishFunction impl value le before = (result, after))
    (generated : GeneratedBuilderState before)
    (transfer : before.cur.isSome = true → ∀ entry ∈ func.results.zip
        (if impl.body.value.isSome then [value] else []),
      PermissionTransfer module.profile (FreshWritableEvidence le first before)
        (FreshContentsEvidence le first before) entry.2 entry.1) :
    NewPermissionInstructions module func le first before after := by
  cases current : before.cur with
  | none =>
    simp only [finishFunction, bind_run, read_apply, isLive_none current, Bool.false_eq_true,
      ite_false, pure_run] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact .of_blocks_eq rfl
  | some source =>
    simp only [finishFunction, bind_run, read_apply, isLive_run current, ite_true] at run
    change ((if !impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn then
      (do
        let (sink, _) ← newBlock []
        emitTerm (.br sink [])
        setCur (some sink)
        emitTerm (.br sink []) : B Unit)
      else emitTerm (.ret (if impl.body.value.isSome then [value] else []) none)) le before) = (result, after) at run
    cases synthetic : (!impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn) with
    | false =>
      simp only [synthetic, Bool.false_eq_true, ite_false] at run
      exact NewPermissionInstructions.emitTerm run (fun _ => .ret (fun entry member =>
        (transfer (by simp [current]) entry member).fresh_of_framed_run run
          (dense_emitTerm _) (advB_emitTerm _) (types_emitTerm _)
          (generatedTargetFrame_emitNoSuccessors none _ (by simp [Term.successors])) generated trivial))
    | true =>
      simp only [synthetic, ite_true] at run
      obtain ⟨⟨sink, parameters⟩, allocated, allocatedRun, _, branched, branchRun,
        _, selected, selectedRun, finalRun⟩ := (by simpa only [bind_eq] using run)
      have allocatedGenerated := generated.newBlock [] allocatedRun
      have sinkAllocated := newBlock_params allocatedRun
      obtain ⟨sinkBody, sinkRow, empty⟩ := sinkAllocated
      have allocatedBound := (Array.getElem?_eq_some_iff.mp sinkRow).1
      have branchedGenerated := allocatedGenerated.emitTerm _ (by
        intro target member
        have same : target = sink := by simpa [Term.successors] using member
        subst target
        exact allocatedBound) branchRun
      have branchedExtension := (advB_emitTerm _ _ _ _ _ branchRun).ext
      obtain ⟨branchedBody, branchedRow, branchedParams, _⟩ := branchedExtension.2 sink sinkBody sinkRow
      have sinkBound := (Array.getElem?_eq_some_iff.mp branchedRow).1
      have selectedGenerated := branchedGenerated.setCur (some sink)
        (by intro actual same; cases same; exact sinkBound) selectedRun
      have selectedRow : selected.blocks[sink]? = some branchedBody := by
        rw [setCur_blocks selectedRun]
        exact branchedRow
      have selectedEmpty : branchedBody.params = [] := by
        simpa using branchedParams.trans empty
      let loop : Option LoopCtx := some ⟨0, sink, .jump sink⟩
      have frames : LoopBuilderFrames loop selected := by
        exact ⟨⟨branchedBody, selectedRow, selectedEmpty⟩, ⟨branchedBody, selectedRow, selectedEmpty⟩⟩
      have sequence : NewPermissionInstructions module func le first allocated selected :=
        (NewPermissionInstructions.branch branchRun).append_setCur selectedRun
      have finished := sequence.compose_framed (NewPermissionInstructions.branch finalRun) finalRun
        (dense_emitTerm _) (advB_emitTerm _) (types_emitTerm _)
        (generatedTargetFrame_emitTerm loop _ (by
          intro base target member bounded
          have same : target = sink := by simpa [Term.successors] using member
          subst target
          exact Or.inl rfl)) selectedGenerated frames
      exact finished.prepend_newBlock allocatedRun

#print axioms permission_types_finishFunction
#print axioms permission_frame_finishFunction
#print axioms newPermissions_finishFunction

end Goose.Lower.Validation
