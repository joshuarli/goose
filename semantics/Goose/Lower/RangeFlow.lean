import Goose.Lower.RangeIteration
import Goose.Lower.RangeBack
import Goose.Lower.EachFlow

namespace Goose.Lower

open Goose.Core Goose.GIR

def RangeFlowPost (cfg : Cfg) (env : Env) (cx : FnCtx) (output : LS)
    (counter : ValueId) (base : Frame) (flow : Flow) (point : Pt) (frame : Frame) : Prop :=
  (flow = .normal .unit ∧ output.pp = some point ∧ Same counter base frame ∧
    Rel cfg env cx frame output) ∨ ReturnedAt cx flow point frame

theorem rangeLoopFlow_to_step (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv)
    (header input output back finalBuilder : LS) (base before after : Frame)
    (counter bound hb exit depth result : Nat) (hint ty : IntTy) (current upper : Int)
    (block : Core.Block) (flow : Flow) (point : Pt)
    (invariant : RangeInv cfg env cx input counter bound ty upper base current before)
    (body : LoopFlowPost cfg env cx input before output
      ⟨depth, exit, .next hb hint counter⟩ block result flow point after)
    (counterInput : counter < input.vals.size) (boundCounter : bound < counter)
    (stackHeader : header.stack = input.stack) (stackFinal : finalBuilder.stack = input.stack)
    (exitPoint : finalBuilder.pp = some (exit, 0))
    (backEdge : rangeBack hint counter hb le output = ((), back))
    (extension : ExtT back cx.fn.blocks)
    (headerBlock : ∃ target, cx.fn.blocks[hb]? = some target ∧
      target.params = [(counter, .data (.int hint))]) :
    RangeStepPost cx (hb, 0) (RangeInv cfg env cx header counter bound ty upper base)
      (RangeFlowPost cfg env cx finalBuilder counter base) current flow point after := by
  obtain ⟨same, counterValue, boundValue, related⟩ := invariant
  rcases body with ⟨normal, rfl, P⟩ | returned | ⟨rfl, exited⟩ | ⟨rfl, continued⟩
  · have counterBody : after.vals[counter]? = some (.val (.int ty current)) := by
      rw [P.same counter counterInput]
      exact counterValue
    have boundBody : after.vals[bound]? = some (.val (.int ty upper)) := by
      rw [P.same bound (Nat.lt_trans boundCounter counterInput)]
      exact boundValue
    obtain ⟨next, goes, sameNext, nextValue, activation, scopes, depth⟩ :=
      rangeBack_goes cx le output back point after counter hb hint ty current backEdge P.pp extension
        (Nat.lt_of_lt_of_le counterInput P.mono) counterBody headerBlock
    have boundNext : next.vals[bound]? = some (.val (.int ty upper)) := by
      rw [sameNext bound boundCounter]
      exact boundBody
    have nextRelated : Rel cfg env cx next header :=
      ⟨related.prof, related.slots, activation.trans P.rel.act, scopes.trans P.rel.scopes,
        depth.trans P.rel.depth, stackHeader.trans related.stack⟩
    exact ⟨next, ⟨same.trans (P.same.mono (Nat.le_of_lt counterInput)) (Nat.le_refl _) |>.trans
      sameNext (Nat.le_refl _), nextValue, boundNext, nextRelated⟩, goes⟩
  · obtain ⟨value, origin, flowEq, site⟩ := returned
    subst flow
    exact Or.inr ⟨value, origin, rfl, site⟩
  · obtain ⟨pointEq, frame⟩ := exited
    have sameFinal := same.trans (frame.values.mono (Nat.le_of_lt counterInput)) (Nat.le_refl _)
    have finalRelated : Rel cfg env cx after finalBuilder :=
      ⟨related.prof, related.slots, frame.activation.trans related.act, frame.scopesEqual,
        frame.depth.trans related.depth, stackFinal.trans related.stack⟩
    exact Or.inl ⟨rfl, pointEq.symm ▸ exitPoint, sameFinal, finalRelated⟩
  · obtain ⟨runtimeTy, old, beforeValue, next⟩ := continued
    have valueEq : RVal.val (.int runtimeTy old) = .val (.int ty current) :=
      Option.some.inj (beforeValue.symm.trans counterValue)
    obtain ⟨typeEq, currentEq⟩ := Val.int.inj (RVal.val.inj valueEq)
    subst runtimeTy
    subst old
    have nextRelated : Rel cfg env cx after header :=
      ⟨related.prof, related.slots, next.activation.trans related.act, next.scopesEqual,
        next.depth.trans related.depth, stackHeader.trans related.stack⟩
    have boundNext : after.vals[bound]? = some (.val (.int ty upper)) := by
      rw [next.values bound boundCounter]
      exact boundValue
    exact ⟨after, ⟨same.trans next.values (Nat.le_refl _), next.counterValue, boundNext, nextRelated⟩,
      next.point.symm ▸ Goes.refl cx (hb, 0) after⟩

end Goose.Lower
