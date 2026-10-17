import Goose.Lower.Validation.SnapshotContentsBuilder

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem SnapshotSourceTrace.finishFunction {le : LEnv} {first : ValueId} {before : LS}
    (trace : SnapshotSourceTrace le first before before) (generated : GeneratedBuilderState before)
    (impl : Core.Impl) (value : ValueId) :
    SnapshotSourceTrace le first (Goose.Lower.finishFunction impl value le before).2
      (Goose.Lower.finishFunction impl value le before).2 := by
  have state : (Goose.Lower.finishFunction impl value le before).2 =
      if before.cur.isSome then
        if !impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn then
          ((do
            let (sink, _) ← Goose.Lower.newBlock []
            Goose.Lower.emitTerm (.br sink [])
            Goose.Lower.setCur (some sink)
            Goose.Lower.emitTerm (.br sink []) : B Unit) le before).2
        else (Goose.Lower.emitTerm (.ret (if impl.body.value.isSome then [value] else []) none) le before).2
      else before := by
    have test : isLive le before = (before.cur.isSome, before) := by
      simp [isLive, bind_run, curBlock_run, pure_run]
    simp only [Goose.Lower.finishFunction, bind_run, read_apply, test]
    by_cases active : before.cur.isSome = true
    · simp only [active, reduceIte]
      by_cases sink : (!impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn) = true
      · simp only [sink, reduceIte, bind_run]
      · simp only [sink, Bool.false_eq_true, reduceIte]
    · simp only [active, Bool.false_eq_true, reduceIte, pure_run]
  rw [state]
  cases active : before.cur.isSome
  · exact trace
  · simp only [reduceIte]
    by_cases sink : (!impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn) = true
    · simp only [sink, reduceIte, bind_run]
      let allocated := Goose.Lower.newBlock [] le before
      let closed := Goose.Lower.emitTerm (.br allocated.1.1 []) le allocated.2
      let selected := Goose.Lower.setCur (some allocated.1.1) le closed.2
      have allocatedTrace := trace.newBlock [] generated (show Goose.Lower.newBlock [] le before = allocated from rfl)
      have allocatedGenerated : GeneratedBuilderState allocated.2 := generated.newBlock (env := le) [] rfl
      have allocatedRow : allocated.2.blocks[allocated.1.1]? = some ⟨[], #[]⟩ := by
        simp [allocated, newBlock0_run]
      have frames : LoopBuilderFrames (some ⟨0, allocated.1.1, .jump allocated.1.1⟩) allocated.2 :=
        loopBuilderFrames_jump allocatedRow rfl allocatedRow rfl
      have target : LoopBuilderFrameTarget (some ⟨0, allocated.1.1, .jump allocated.1.1⟩) allocated.1.1 := Or.inr rfl
      have closedTrace := allocatedTrace.emitTerm_loop allocatedGenerated frames
        (term := .br allocated.1.1 []) (fun destination member => by
          have same : destination = allocated.1.1 := by simpa [Term.successors] using member
          subst destination
          exact target) rfl
      have closedGenerated : GeneratedBuilderState closed.2 := allocatedGenerated.emitTerm
        (.br allocated.1.1 []) (by simpa [Term.successors] using frames.targetBound target) rfl
      have closedFrames := frames.mono (advB_emitTerm (.br allocated.1.1 []) le allocated.2 _ _ rfl).ext
      have selectedTrace := closedTrace.setCur_full (current := some allocated.1.1) rfl
      have selectedGenerated : GeneratedBuilderState selected.2 := closedGenerated.setCur (env := le) _
        (by intro block same; cases Option.some.inj same; exact closedFrames.targetBound target) rfl
      have selectedFrames : LoopBuilderFrames (some ⟨0, allocated.1.1, .jump allocated.1.1⟩) selected.2 :=
        closedFrames.of_blocks rfl
      exact selectedTrace.emitTerm_loop selectedGenerated selectedFrames
        (term := .br allocated.1.1 []) (fun destination member => by
          have same : destination = allocated.1.1 := by simpa [Term.successors] using member
          subst destination
          exact target) rfl
    · rw [ite_eq_right sink]
      exact trace.emitTerm_before_full generated rfl (by
        intro edge member
        simp [Term.permissionEdges] at member)

end Goose.Lower.Validation
