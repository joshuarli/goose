import Goose.Lower.Finish
import Goose.Lower.Leaf

namespace Goose.Proofs.Lower

open Goose.Core Goose.GIR Goose.Lower

theorem extT_finish (ls : LS) : ExtT ls (finishBlocks ls.blocks) := by
  refine ⟨by simp [finishBlocks], fun i blk hi => ?_⟩
  refine ⟨⟨blk.params, blk.insts.toList⟩, ?_, rfl, [], by simp⟩
  simp [finishBlocks, Array.getElem?_map, hi]

def bodyTail (impl : Impl) (le : LEnv) (v : ValueId) (ls1 : LS) : LS :=
  (finishFunction impl v le ls1).2

theorem bodyTail_cases (impl : Impl) (le : LEnv) (v : ValueId) (ls1 : LS)
    (hd : impl.body.diverges le.mod.noReturn = false) :
    (ls1.cur = none ∧ bodyTail impl le v ls1 = ls1) ∨
    (∃ b, ls1.cur = some b ∧
      emitTerm (.ret (if impl.body.value.isSome then [v] else []) none) le ls1 =
        ((), bodyTail impl le v ls1)) := by
  cases hc : ls1.cur with
  | none =>
    left
    refine ⟨rfl, ?_⟩
    unfold bodyTail
    rw [finishFunction_nondivergent impl le ls1 v hd]
    simp [bind_run, isLive_none hc, pure_run]
  | some b =>
    right
    refine ⟨b, rfl, ?_⟩
    unfold bodyTail
    rw [finishFunction_nondivergent impl le ls1 v hd]
    simp [bind_run, isLive_run hc]


end Goose.Proofs.Lower
