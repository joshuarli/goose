import Goose.Lower.GeneratedIntervalFramesShortCircuit

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Lower.Validation

theorem GeneratedIntervalFrameRun.ifThen {loop : Option LoopCtx} {deferred : List BlockId}
    (condition : ValueId) {yes : B Unit}
    (yesFrames : ∀ join, GeneratedIntervalFrameRun loop (join :: deferred) yes) :
    GeneratedIntervalFrameRun loop deferred (Goose.Lower.whenLive () fun _ => do
      let (yesBlock, join) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some yesBlock)
      let _ ← yes
      Goose.Lower.emitTerm (.br join [])
      Goose.Lower.setCur (some join)) := by
  apply GeneratedIntervalFrameRun.whenLive
  intro currentBlock before captured env current result after extension frames avoids terms run
  simp only [bind_eq] at run
  obtain ⟨⟨yesBlock, join⟩, forked, forkRun, ignored, selected, selectRun,
    value, body, bodyRun, ignored', closed, closedRun, finalRun⟩ := run
  obtain ⟨forkTerms, forkExtension⟩ := (GeneratedIntervalFrameRun.fork loop deferred condition)
    before captured env current _ forked extension frames avoids terms forkRun
  obtain ⟨selectedTerms, selectedExtension⟩ := (GeneratedIntervalFrameRun.setCur loop deferred (some yesBlock))
    before captured env forked _ selected (extension.trans forkExtension) (frames.mono forkExtension) avoids forkTerms selectRun
  have currentSelected := forkExtension.trans selectedExtension
  have joinFresh : current.blocks.size ≤ join :=
    (generatedTargetFrame_forkFresh (LS.Ext.refl current) forkRun).2
  have joinOutside : captured.blocks.size ≤ join := Nat.le_trans extension.1 joinFresh
  have scopedAvoids : IntervalTargetsAvoid before captured ((join :: deferred) ++ LoopBuilderFrameTargets loop) :=
    avoids.cons (Or.inr joinOutside)
  obtain ⟨bodyTerms, bodyExtension⟩ := yesFrames join before captured env selected value body
    (extension.trans currentSelected) (frames.mono currentSelected) scopedAvoids selectedTerms bodyRun
  have closedTerms := bodyTerms.emitTermAt closedRun (by
    intro target successor
    have same : target = join := by simpa [Term.successors] using successor
    subst target
    exact Or.inr joinOutside)
  have closedExtension := (advB_emitTerm (.br join []) env body _ closed closedRun).ext
  have currentClosed := currentSelected.trans (bodyExtension.trans closedExtension)
  obtain ⟨finalTerms, finalExtension⟩ := (GeneratedIntervalFrameRun.setCur loop deferred (some join))
    before captured env closed _ after (extension.trans currentClosed) (frames.mono currentClosed) avoids closedTerms finalRun
  exact ⟨finalTerms, currentClosed.trans finalExtension⟩

theorem GeneratedIntervalFrameRun.header {loop : Option LoopCtx} {deferred : List BlockId}
    (types : List VTy) (arguments : List ValueId) {tail : BlockId → List ValueId → B α}
    (tailFrames : ∀ header parameters, GeneratedIntervalFrameRun loop (header :: deferred) (tail header parameters)) :
    GeneratedIntervalFrameRun loop deferred (do
      let (header, parameters) ← Goose.Lower.newBlock types
      Goose.Lower.emitTerm (.br header arguments)
      Goose.Lower.setCur (some header)
      tail header parameters) := by
  intro before captured env current result after extension frames avoids terms run
  simp only [bind_eq] at run
  obtain ⟨⟨header, parameters⟩, allocated, allocateRun, ignored, closed, closedRun,
    ignored', selected, selectRun, tailRun⟩ := run
  obtain ⟨allocatedTerms, allocatedExtension⟩ := (GeneratedIntervalFrameRun.newBlock loop deferred types)
    before captured env current _ allocated extension frames avoids terms allocateRun
  have headerFresh : current.blocks.size ≤ header := newBlock_fresh (.refl current) allocateRun
  have headerOutside : captured.blocks.size ≤ header := Nat.le_trans extension.1 headerFresh
  have closedTerms := allocatedTerms.emitTermAt closedRun (by
    intro target successor
    have same : target = header := by simpa [Term.successors] using successor
    subst target
    exact Or.inr headerOutside)
  have closedExtension := (advB_emitTerm (.br header arguments) env allocated _ closed closedRun).ext
  have currentClosed := allocatedExtension.trans closedExtension
  obtain ⟨selectedTerms, selectedExtension⟩ := (GeneratedIntervalFrameRun.setCur loop deferred (some header))
    before captured env closed _ selected (extension.trans currentClosed) (frames.mono currentClosed) avoids closedTerms selectRun
  have currentSelected := currentClosed.trans selectedExtension
  have scopedAvoids : IntervalTargetsAvoid before captured ((header :: deferred) ++ LoopBuilderFrameTargets loop) :=
    avoids.cons (Or.inr headerOutside)
  obtain ⟨afterTerms, tailExtension⟩ := tailFrames header parameters before captured env selected result after
    (extension.trans currentSelected) (frames.mono currentSelected) scopedAvoids selectedTerms tailRun
  exact ⟨afterTerms, currentSelected.trans tailExtension⟩

end Goose.Lower
