import Goose.Lower.GeneratedIntervalFrames
import Goose.Lower.GeneratedTargetFramesSource

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Lower.Validation

def LoopBuilderFrameTargets (loop : Option LoopCtx) : List BlockId :=
  match loop with
  | none => []
  | some context => context.breakTo :: [match context.cont with
      | .jump header | .next header _ _ => header]

theorem loopBuilderFrameTargets_mem {loop : Option LoopCtx} {target : BlockId} :
    target ∈ LoopBuilderFrameTargets loop ↔ LoopBuilderFrameTarget loop target := by
  cases loop with
  | none => simp [LoopBuilderFrameTargets, LoopBuilderFrameTarget]
  | some context => cases kind : context.cont <;> simp [LoopBuilderFrameTargets, LoopBuilderFrameTarget, kind]

def IntervalTargetsAvoid (before captured : LS) (targets : List BlockId) : Prop :=
  ∀ target ∈ targets, target < before.blocks.size ∨ captured.blocks.size ≤ target

theorem IntervalTargetsAvoid.nil (before captured : LS) : IntervalTargetsAvoid before captured [] := by
  intro target member
  cases member

theorem IntervalTargetsAvoid.mono {before captured : LS} {first second : List BlockId}
    (avoids : IntervalTargetsAvoid before captured first)
    (included : ∀ target ∈ second, target ∈ first) : IntervalTargetsAvoid before captured second := by
  intro target member
  exact avoids target (included target member)

theorem IntervalTargetsAvoid.cons {before captured : LS} {targets : List BlockId}
    (avoids : IntervalTargetsAvoid before captured targets) {target : BlockId}
    (outside : target < before.blocks.size ∨ captured.blocks.size ≤ target) :
    IntervalTargetsAvoid before captured (target :: targets) := by
  intro next member
  rcases List.mem_cons.mp member with rfl | member
  · exact outside
  · exact avoids next member

theorem IntervalTargetsAvoid.append {before captured : LS} {first second : List BlockId}
    (one : IntervalTargetsAvoid before captured first) (two : IntervalTargetsAvoid before captured second) :
    IntervalTargetsAvoid before captured (first ++ second) := by
  intro target member
  rcases List.mem_append.mp member with member | member
  · exact one target member
  · exact two target member

theorem IntervalEdgesFramed.of_blocks {before captured current after : LS}
    (framed : IntervalEdgesFramed before captured current) (same : after.blocks = current.blocks) :
    IntervalEdgesFramed before captured after := by
  intro source body term target row member successor lower upper
  rw [same] at row
  exact framed source body term target row member successor lower upper

theorem IntervalEdgesFramed.extend {before captured current after : LS}
    (framed : IntervalEdgesFramed before captured current)
    (terms : ∀ (source : BlockId) (body : BlockB) (term : Term) (target : BlockId),
      after.blocks[source]? = some body → Inst.term term ∈ body.insts.toList → target ∈ term.successors →
      before.blocks.size ≤ target → target < captured.blocks.size →
      ∃ old, current.blocks[source]? = some old ∧ Inst.term term ∈ old.insts.toList) :
    IntervalEdgesFramed before captured after := by
  intro source body term target row member successor lower upper
  obtain ⟨old, oldRow, oldMember⟩ := terms source body term target row member successor lower upper
  exact framed source old term target oldRow oldMember successor lower upper

theorem IntervalEdgesFramed.after_frames {loop : Option LoopCtx} {before captured current after : LS}
    (framed : IntervalEdgesFramed before captured current) (extension : captured.Ext current)
    (next : TermEdgesFramed loop current after)
    (avoids : IntervalTargetsAvoid before captured (LoopBuilderFrameTargets loop)) :
    IntervalEdgesFramed before captured after := by
  apply framed.extend
  intro source body term target row member successor lower upper
  rcases next source body term target row member successor (Nat.lt_of_lt_of_le upper extension.1) with old | loopTarget
  · exact old
  · rcases avoids target (loopBuilderFrameTargets_mem.mpr loopTarget) with earlier | later
    · exact False.elim (Nat.not_lt_of_ge lower earlier)
    · exact False.elim (Nat.not_lt_of_ge later upper)

def GeneratedIntervalFrameRun (loop : Option LoopCtx) (deferred : List BlockId) (action : B α) : Prop :=
  ∀ before captured env current result after, captured.Ext current → LoopBuilderFrames loop current →
    IntervalTargetsAvoid before captured (deferred ++ LoopBuilderFrameTargets loop) →
    IntervalEdgesFramed before captured current → action env current = (result, after) →
    IntervalEdgesFramed before captured after ∧ current.Ext after

theorem GeneratedIntervalFrameRun.of_frames {loop : Option LoopCtx} {action : B α}
    (framed : GeneratedTargetFrameRun loop action) (deferred : List BlockId) :
    GeneratedIntervalFrameRun loop deferred action := by
  intro before captured env current result after extension loopFrames avoids oldFrames run
  obtain ⟨newFrames, advancing⟩ := framed current env current result after (.refl _) loopFrames
    (TermEdgesFramed.refl loop current) run
  exact ⟨oldFrames.after_frames extension newFrames
    (avoids.mono (fun target member => List.mem_append_right _ member)), advancing⟩

theorem GeneratedIntervalFrameRun.bind {loop : Option LoopCtx} {deferred : List BlockId}
    {first : B α} {next : α → B β} (one : GeneratedIntervalFrameRun loop deferred first)
    (two : ∀ value, GeneratedIntervalFrameRun loop deferred (next value)) :
    GeneratedIntervalFrameRun loop deferred (first >>= next) := by
  intro before captured env current result after extension frames avoids terms run
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  obtain ⟨middleTerms, firstExtension⟩ := one before captured env current value middle extension frames avoids terms firstRun
  obtain ⟨afterTerms, nextExtension⟩ := two value before captured env middle result after
    (extension.trans firstExtension) (frames.mono firstExtension) avoids middleTerms nextRun
  exact ⟨afterTerms, firstExtension.trans nextExtension⟩

theorem GeneratedIntervalFrameRun.weaken {loop : Option LoopCtx} {first second : List BlockId} {action : B α}
    (checked : GeneratedIntervalFrameRun loop first action)
    (included : ∀ target ∈ first, target ∈ second) : GeneratedIntervalFrameRun loop second action := by
  intro before captured env current result after extension frames avoids terms run
  apply checked before captured env current result after extension frames _ terms run
  apply avoids.mono
  intro target member
  rcases List.mem_append.mp member with member | member
  · exact List.mem_append_left _ (included target member)
  · exact List.mem_append_right _ member

end Goose.Lower
