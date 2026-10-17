import Goose.Lower.GeneratedIntervalFramesControl
import Goose.Lower.Validation.CfgBuilderFunctions

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Lower.Validation

private theorem interval_finishFunction_frames (loop : Option LoopCtx) (impl : Core.Impl) (value : ValueId) :
    GeneratedTargetFrameRun loop (finishFunction impl value) := by
  unfold finishFunction
  refine (generatedTargetFrame_read loop).bind fun env => (generatedTargetFrame_isLive loop).bind fun live => ?_
  cases live
  · exact generatedTargetFrame_pure loop ()
  · simp only [ite_true]
    split
    · apply generatedTargetFrame_header0 loop (tail := fun header => emitTerm (.br header []))
      intro header base env current after result extension frames terms fresh headerAt run
      refine ⟨terms.emitTermAt run ?_, (advB_emitTerm (.br header []) env current result after run).ext⟩
      intro target successor bounded
      have same : target = header := by simpa [Term.successors] using successor
      subst target
      exact False.elim (Nat.not_lt_of_ge fresh bounded)
    · exact generatedTargetFrame_emitNoSuccessors loop _ rfl

theorem generatedIntervalFrame_finishFunction (loop : Option LoopCtx) (deferred : List BlockId)
    (impl : Core.Impl) (value : ValueId) :
    GeneratedIntervalFrameRun loop deferred (finishFunction impl value) :=
  .of_frames (interval_finishFunction_frames loop impl value) deferred

theorem generatedIntervalFrame_implAction (deferred : List BlockId) (impl : Core.Impl) :
    GeneratedIntervalFrameRun none deferred (cfg_implAction impl) := by
  unfold cfg_implAction
  exact (GeneratedIntervalFrameRun.newBlock none deferred _).bind fun entry =>
    (GeneratedIntervalFrameRun.setCur none deferred _).bind fun _ =>
      (generatedIntervalFrame_lowerBlock none deferred _ false impl.body).bind fun value =>
        generatedIntervalFrame_finishFunction none deferred impl value

theorem generatedIntervalFrame_globalAction (deferred : List BlockId) (global : Core.Global) :
    GeneratedIntervalFrameRun none deferred (cfg_globalAction global) := by
  unfold cfg_globalAction
  exact (GeneratedIntervalFrameRun.newBlock none deferred []).bind fun entry =>
    (GeneratedIntervalFrameRun.setCur none deferred _).bind fun _ =>
      (generatedIntervalFrame_lowerExpr none deferred global.init).bind fun value =>
        GeneratedIntervalFrameRun.emitTerm (.ret [value] (some global.org)) (by simp [Term.successors])

end Goose.Lower
