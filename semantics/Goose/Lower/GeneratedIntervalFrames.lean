import Goose.Lower.GeneratedTargetFrames

namespace Goose.Lower

open Goose.Core Goose.GIR

def IntervalEdgesFramed (before captured after : LS) : Prop :=
  ∀ (source : BlockId) (body : BlockB) (term : Term) (target : BlockId),
    after.blocks[source]? = some body →
    Inst.term term ∈ body.insts.toList → target ∈ term.successors →
    before.blocks.size ≤ target → target < captured.blocks.size →
    ∃ old, captured.blocks[source]? = some old ∧ Inst.term term ∈ old.insts.toList

theorem IntervalEdgesFramed.refl (before captured : LS) :
    IntervalEdgesFramed before captured captured := by
  intro source body term target row member successor lower upper
  exact ⟨body, row, member⟩

theorem IntervalEdgesFramed.of_frames {loop : Option LoopCtx} {before captured after : LS}
    (frames : LoopBuilderFrames loop before) (framed : TermEdgesFramed loop captured after) :
    IntervalEdgesFramed before captured after := by
  intro source body term target row member successor lower upper
  rcases framed source body term target row member successor upper with old | loopTarget
  · exact old
  · exact False.elim (Nat.not_lt_of_ge lower (frames.targetBound loopTarget))

end Goose.Lower
