import Goose.Lower.GeneratedIntervalFramesSource

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Lower.Validation

theorem GeneratedIntervalFrameRun.shortCircuit {loop : Option LoopCtx} {deferred : List BlockId}
    (isAnd : Bool) (condition : ValueId) {rhs : B ValueId}
    (rhsFrames : ∀ join, GeneratedIntervalFrameRun loop (join :: deferred) rhs) :
    GeneratedIntervalFrameRun loop deferred (Goose.Lower.shortCircuit isAnd condition rhs) := by
  intro before captured env current result after extension frames avoids terms run
  cases live : current.cur with
  | none =>
    rw [Goose.Lower.shortCircuit, whenLive_none _ _ _ live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact ⟨terms, .refl _⟩
  | some currentBlock =>
    rw [Goose.Lower.shortCircuit, whenLive_some _ _ _ live] at run
    simp only [bind_eq] at run
    obtain ⟨⟨rhsBlock, join, parameter⟩, forked, forkRun,
      ignored, selected, selectedRun, rhsValue, body, bodyRun,
      ignored', closed, closedRun, ignored'', final, finalRun, finished⟩ := run
    obtain ⟨_, rfl⟩ := pure_eq.mp finished
    obtain ⟨forkTerms, forkExtension⟩ := (GeneratedIntervalFrameRun.of_frames
      (generatedTargetFrame_scFork loop isAnd condition) deferred)
      before captured env current _ forked extension frames avoids terms forkRun
    obtain ⟨selectedTerms, selectedExtension⟩ := (GeneratedIntervalFrameRun.setCur loop deferred (some rhsBlock))
      before captured env forked _ selected (extension.trans forkExtension) (frames.mono forkExtension) avoids forkTerms selectedRun
    have currentSelected := forkExtension.trans selectedExtension
    have joinFresh : current.blocks.size ≤ join :=
      (generatedTargetFrame_scForkFresh (LS.Ext.refl current) forkRun).2
    have joinOutside : captured.blocks.size ≤ join := Nat.le_trans extension.1 joinFresh
    have scopedAvoids : IntervalTargetsAvoid before captured ((join :: deferred) ++ LoopBuilderFrameTargets loop) :=
      avoids.cons (Or.inr joinOutside)
    obtain ⟨bodyTerms, bodyExtension⟩ := rhsFrames join before captured env selected rhsValue body
      (extension.trans currentSelected) (frames.mono currentSelected) scopedAvoids selectedTerms bodyRun
    have closedTerms := bodyTerms.emitTermAt closedRun (by
      intro target successor
      have same : target = join := by simpa [Term.successors] using successor
      subst target
      exact Or.inr joinOutside)
    have closedExtension := (advB_emitTerm (.br join [rhsValue]) env body _ closed closedRun).ext
    have currentClosed := currentSelected.trans (bodyExtension.trans closedExtension)
    obtain ⟨finalTerms, finalExtension⟩ := (GeneratedIntervalFrameRun.setCur loop deferred (some join))
      before captured env closed _ final (extension.trans currentClosed) (frames.mono currentClosed) avoids closedTerms finalRun
    exact ⟨finalTerms, currentClosed.trans finalExtension⟩

end Goose.Lower
