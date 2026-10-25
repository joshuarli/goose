import Goose.Lower.GeneratedTargetFrames
import Goose.Lower.LoopFlow

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem LoopBuilderFrames.of_functionTargets {loop : LoopCtx} {state : LS} {fn : Func}
    (targets : LoopTargets fn loop) (bounds : LoopBuilderTargets (some loop) state)
    (extension : ExtT state fn.blocks) : LoopBuilderFrames (some loop) state := by
  have row (target : BlockId) (params : List (ValueId × VTy))
      (bounded : target < state.blocks.size)
      (expected : ∃ block, fn.blocks[target]? = some block ∧ block.params = params) :
      ∃ block, state.blocks[target]? = some block ∧ block.params = params := by
    let block := state.blocks[target]
    have blockAt : state.blocks[target]? = some block := by simp [block, bounded]
    obtain ⟨final, finalAt, finalParams⟩ := extension.params blockAt
    obtain ⟨expectedBlock, expectedAt, expectedParams⟩ := expected
    have equal : final = expectedBlock := Option.some.inj (finalAt.symm.trans expectedAt)
    exact ⟨block, blockAt, finalParams.symm.trans (equal ▸ expectedParams)⟩
  refine ⟨row loop.breakTo [] bounds.1 targets.breakBlock, ?_⟩
  cases kind : loop.cont with
  | jump header =>
    exact row header [] (by simpa [LoopBuilderTargets, kind] using bounds.2)
      (by simpa [kind] using targets.continueBlock)
  | next header ty counter =>
    exact row header [(counter, .data (.int ty))]
      (by simpa [LoopBuilderTargets, kind] using bounds.2)
      (by simpa [kind] using targets.continueBlock)

end Goose.Lower
