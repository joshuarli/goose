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

def RangeBlockCallback (n : Nat) (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv)
    (header : LS) (counter bound hb : ValueId) (hint runtimeType : IntTy) (upper : Int)
    (base : Frame) (x : VarId) (block : Core.Block) (org : OriginId)
    (bodyAllowed : Int → St → Prop) : Prop :=
  ∀ fuel, fuel < n → ∀ depth exit input result output current frame state bodyPoint,
    lowerBlock (some ⟨depth, exit, .next hb hint counter⟩)
      [(x, counter, org)] false block le input = (result, output) →
    input.pp = some bodyPoint → ExtT output cx.fn.blocks →
    input.stack = header.stack → depth = input.stack.length →
    counter < input.vals.size →
    LoopTargets cx.fn ⟨depth, exit, .next hb hint counter⟩ →
    RangeInv cfg env cx input counter bound runtimeType upper base current frame →
    bodyAllowed current state →
    PreRel frame [(x, counter, org)] [(x, .int runtimeType current)] →
    SimEAt cx bodyPoint frame
      (execBlock fuel cfg env [(x, .int runtimeType current)] block >>= prepareReturn env)
      (LoopFlowPost cfg env cx input frame output
        ⟨depth, exit, .next hb hint counter⟩ block result) state

theorem lowerRange_flow_sim_at (n : Nat) (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv)
    (header output : LS) (counter bound hb : ValueId) (hint runtimeType : IntTy)
    (upper : Int) (base : Frame) (x : VarId) (org : OriginId) (block : Core.Block)
    (bodyAllowed : Int → St → Prop) (allowed : Int → St → Prop)
    (lowered : lowerRange hint counter bound hb
      (fun depth xb => lowerBlock (some ⟨depth, xb, .next hb hint counter⟩)
        [(x, counter, org)] false block) le header = ((), output))
    (atHeader : header.pp = some (hb, 0)) (extension : ExtT output cx.fn.blocks)
    (headerBlock : ∃ target, cx.fn.blocks[hb]? = some target ∧
      target.params = [(counter, .data (.int hint))])
    (boundBeforeCounter : bound < counter) (counterInHeader : counter < header.vals.size)
    (bodyCallback : RangeBlockCallback n cfg env cx le header counter bound hb hint runtimeType
      upper base x block org bodyAllowed)
    (enter : ∀ current state, allowed current state → bodyAllowed current state)
    (retained : ∀ fuel, fuel < n → ∀ current state flow after, allowed current state →
      (execBlock fuel cfg env [(x, .int runtimeType current)] block >>= prepareReturn env)
        state = .ok flow after →
      (match flow with | .normal _ | .cont => allowed (current + 1) after | _ => True)) :
    ∀ current frame state,
      RangeInv cfg env cx header counter bound runtimeType upper base current frame →
      allowed current state →
      SimEAt cx (hb, 0) frame
        (execRange n cfg env x runtimeType current upper block >>= prepareReturn env)
        (RangeFlowPost cfg env cx output counter base) state := by
  let bodyB := fun depth xb =>
    lowerBlock (some ⟨depth, xb, .next hb hint counter⟩)
      [(x, counter, org)] false block
  change lowerRange hint counter bound hb bodyB le header = ((), output) at lowered
  obtain ⟨condition, compared, bodyPoint, exit, forked, input, result, bodyOutput, back,
      hcompare, hfork, hinput, hlowerBody, hback, hexit⟩ := lowerRange_unfold lowered
  have backAdvances := advB_rangeBack hint counter hb le bodyOutput () back hback
  have extensionBack : ExtT back cx.fn.blocks := by
    simpa [hexit, ExtT] using extension
  have extensionBody := extensionBack.of_adv backAdvances
  have bodyAdvances' := advB_lowerBlock
    (some ⟨compared.stack.length, exit, .next hb hint counter⟩)
    [(x, counter, org)] false block le input result bodyOutput hlowerBody
  have extensionInput := extensionBody.of_adv bodyAdvances'
  have extensionFork : ExtT forked cx.fn.blocks := by
    simpa [hinput, ExtT] using extensionInput
  obtain ⟨entryBlock, entryLive, _, _⟩ := LS.pp_some atHeader
  have conditionLive : compared.cur = some hb := by
    have run := emitDef_run (.cmp .lt hint counter bound) le entryLive
    rw [run] at hcompare
    have stateEq := (Prod.mk.inj hcompare).2
    calc
      compared.cur = header.cur := by simpa using (congrArg LS.cur stateEq).symm
      _ = some hb := entryLive
  have extensionForked := extensionFork.of_adv (adv_fork conditionLive hfork)
  obtain ⟨conditionId, compareSize, compareStack, comparePoint, compareInstruction⟩ :=
    rangeCompare_facts hcompare atHeader extensionForked
  obtain ⟨_, _, _, forkValues, forkStack, _,
    forkTerm, bodyBlockLive, exitBlockLive⟩ := fork_facts hfork comparePoint extensionFork
  obtain ⟨bodyTarget, bodyTargetLive, bodyParams⟩ := extensionFork.params bodyBlockLive
  obtain ⟨exitTarget, exitTargetLive, exitParams⟩ := extensionFork.params exitBlockLive
  have compareAt : instAt cx.fn (hb, 0) = some (.def condition (.cmp .lt hint counter bound)) := by
    rw [instAt_eq]
    exact compareInstruction
  have branchAt : instAt cx.fn (hb, 1) = some (.term (.condbr condition bodyPoint [] exit [])) := by
    rw [instAt_eq]
    exact forkTerm
  have inputValueSize : input.vals.size = header.vals.size + 1 := by
    rw [hinput]
    change forked.vals.size = _
    rw [forkValues, compareSize]
  have inputStack : input.stack = header.stack := by
    rw [hinput]
    exact forkStack.trans compareStack
  have bodyPointInput : input.pp = some (bodyPoint, 0) := by
    rw [hinput]
    exact LS.pp_cur bodyBlockLive
  have bodyDepth : compared.stack.length = input.stack.length := by
    rw [inputStack]
    exact congrArg List.length compareStack
  have bodyCounterBound : counter < input.vals.size := by
    rw [inputValueSize]
    exact Nat.lt_trans counterInHeader (Nat.lt_succ_self _)
  have bodyTargets : ∀ depth,
      LoopTargets cx.fn ⟨depth, exit, .next hb hint counter⟩ := by
    intro depth
    exact ⟨⟨exitTarget, exitTargetLive, exitParams⟩, headerBlock⟩
  have outputExitBlock : back.blocks[exit]? = some ⟨[], #[]⟩ := by
    refine (bodyAdvances'.trans backAdvances).keep exit ⟨[], #[]⟩ ?_ ?_
    · rw [hinput]
      intro sameBlock
      have blockEq : bodyPoint = exit := Option.some.inj sameBlock
      have ids := fork_ids hfork
      obtain ⟨bodyId, exitId⟩ := Prod.mk.inj ids.1
      have bodyLess : bodyPoint < exit := by
        rw [bodyId, exitId]
        exact Nat.lt_succ_self _
      exact (Nat.ne_of_lt bodyLess) blockEq
    · rw [hinput]
      exact exitBlockLive
  have exitPoint : output.pp = some (exit, 0) := by
    rw [hexit]
    exact LS.pp_cur outputExitBlock
  have headerStackOutput : output.stack = header.stack := by
    rw [hexit]
    exact backAdvances.stack.trans
      (bodyAdvances'.stack.trans (by rw [hinput]; exact forkStack.trans compareStack))
  let headerInv := fun current frame =>
    RangeInv cfg env cx header counter bound runtimeType upper base current frame
  let bodyInv := fun current frame =>
    RangeInv cfg env cx input counter bound runtimeType upper base current frame
  let post : Flow → Pt → Frame → Prop := RangeFlowPost cfg env cx output counter base
  have branch : RangeBranch cx (hb, 0) (bodyPoint, 0) upper headerInv bodyInv post := by
    intro current frame invariant
    obtain ⟨same, counterValue, boundValue, related⟩ := invariant
    have comparePure : execPure cx frame (.cmp .lt hint counter bound) =
        pure (.val (.bool (current < upper))) := by
      have typedCompare := (execPure_cmp (cx := cx) (fr := frame) (op := .lt)
        counterValue boundValue).1 hint
      rw [typedCompare]
      simp [expectComparable, expectSameTy, evalCmp]
    have comparedGoes := Goes.def_pure compareAt (by simp) comparePure
    let comparedFrame := frame.set condition (.val (.bool (current < upper)))
    have conditionValue : comparedFrame.vals[condition]? =
        some (.val (.bool (current < upper))) := Frame.set_get _ _ _
    have counterCompared : comparedFrame.vals[counter]? = some (.val (.int runtimeType current)) := by
      have different : counter ≠ condition := by
        rw [conditionId]
        exact Nat.ne_of_lt counterInHeader
      simpa [comparedFrame, Frame.set, Std.HashMap.getElem?_insert, different.symm] using counterValue
    have boundCompared : comparedFrame.vals[bound]? = some (.val (.int runtimeType upper)) := by
      have different : bound ≠ condition := by
        rw [conditionId]
        exact Nat.ne_of_lt (Nat.lt_trans boundBeforeCounter counterInHeader)
      simpa [comparedFrame, Frame.set, Std.HashMap.getElem?_insert, different.symm] using boundValue
    have sameComparedLocal : Same counter frame comparedFrame := by
      have below : counter ≤ condition := by rw [conditionId]; exact Nat.le_of_lt counterInHeader
      change Same counter frame (frame.set condition (.val (.bool (current < upper))))
      exact Same.set frame below _
    have sameCompared : Same counter base comparedFrame :=
      same.trans sameComparedLocal (Nat.le_refl _)
    have relatedCompared : Rel cfg env cx comparedFrame header := by
      simpa [comparedFrame] using related.set condition (.val (.bool (current < upper)))
    by_cases below : current < upper
    · simp only [below, ↓reduceIte]
      have trueCondition : comparedFrame.vals[condition]? = some (.val (.bool true)) := by
        simpa [below] using conditionValue
      have enterGoes := goes_condbr_then0 branchAt trueCondition bodyTargetLive bodyParams rfl
      have relatedInput : Rel cfg env cx comparedFrame input :=
        relatedCompared.stack_eq inputStack
      refine ⟨comparedFrame, ?_, comparedGoes.trans enterGoes⟩
      exact ⟨sameCompared, counterCompared, boundCompared, relatedInput⟩
    · simp only [below, ↓reduceIte]
      have falseCondition : comparedFrame.vals[condition]? = some (.val (.bool false)) := by
        simpa [below] using conditionValue
      have exitGoes := goes_condbr_else0 branchAt falseCondition exitTargetLive exitParams rfl
      refine ⟨(exit, 0), comparedFrame, Or.inl ?_, comparedGoes.trans exitGoes⟩
      exact ⟨rfl, exitPoint, sameCompared, relatedCompared.stack_eq headerStackOutput⟩
  have bodySimulation : ∀ fuel, fuel < n → ∀ current frame state,
      bodyInv current frame → allowed current state →
      SimEAt cx (bodyPoint, 0) frame
        (execBlock fuel cfg env [(x, .int runtimeType current)] block >>= prepareReturn env)
        (RangeStepPost cx (hb, 0) headerInv post current) state := by
    intro fuel fuelBound current frame state invariant allowedState
    have callbackInput := bodyCallback fuel fuelBound compared.stack.length exit input result bodyOutput
      current frame state (bodyPoint, 0) hlowerBody bodyPointInput extensionBody inputStack
      bodyDepth bodyCounterBound (bodyTargets compared.stack.length) invariant
      (enter current state allowedState)
      (by
        obtain ⟨_, counterValue, _, _⟩ := invariant
        simp [PreRel, counterValue])
    exact callbackInput.mono fun flow _ point after _ bodyFlow =>
      rangeLoopFlow_to_step cfg env cx le header input bodyOutput back output
        base frame after counter bound hb exit compared.stack.length result hint runtimeType
        current upper block flow point invariant bodyFlow bodyCounterBound boundBeforeCounter
        inputStack.symm (headerStackOutput.trans inputStack.symm) exitPoint hback extensionBack headerBlock
  exact range_sim_at n cx cfg env x runtimeType upper block (hb, 0) (bodyPoint, 0)
    headerInv bodyInv allowed post branch bodySimulation retained

end Goose.Lower
