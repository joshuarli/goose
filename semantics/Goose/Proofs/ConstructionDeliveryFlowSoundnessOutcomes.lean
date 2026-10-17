import Goose.Proofs.ConstructionDeliveryFlowSoundnessStatic
import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFrames
import Goose.Construct.Eval

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

def jumpControlFlow (scope : BreakScope) : JumpKind → StaticFlow
  | .continueLoop => continueLoopFlow
  | .breakValue _ => match scope with | .block => valueBreakFlow | .loop => loopBreakFlow

theorem jumpControlFlow_ne_normal (scope : BreakScope) (kind : JumpKind) :
    jumpControlFlow scope kind ≠ normalFlow := by
  cases scope <;> cases kind <;>
    simp [jumpControlFlow, valueBreakFlow, loopBreakFlow, continueLoopFlow, normalFlow,
      statementFlows, blockFlows, statementFlow_transition, blockFlow_transition,
      expressionFlow_transition, continueFlow_transition]

def resultControlFlow : Flow → StaticFlow
  | .normal _ => normalFlow
  | .breaking _ => loopBreakFlow
  | .continuing => continueLoopFlow

def JumpScopeMatches (scope : BreakScope) : JumpKind → Prop
  | .breakValue _ => True
  | .continueLoop => scope = .loop

def ControlFlowOutcome (activation : Goose.Core.ActId) (before : ExecutionState) (allowed : List StaticFlow)
    (resultFlow : α → StaticFlow) : ExecutionStep α → Prop
  | .ok value _ => resultFlow value ∈ allowed
  | .stop _ _ | .escape _ _ _ => True
  | .jump id kind _ => ∃ target ∈ before.breaks,
      before.breaks.find? (fun entry => entry.act == activation && some target.scope == some entry.scope) = some target ∧
      JumpScopeMatches target.scope kind ∧ target.id = id ∧ jumpControlFlow target.scope kind ∈ allowed

structure ControlFlowAction (activation : Goose.Core.ActId) (allowed : List StaticFlow) (resultFlow : α → StaticFlow)
    (action : EvalM α) : Prop where
  frame : BreakFrameAction action
  outcome : ∀ before, BreakTargetsBelowCounter before → ControlFlowOutcome activation before allowed resultFlow (action before)

variable {activation : Goose.Core.ActId}

theorem controlFlow_pure (allowed : List StaticFlow) (resultFlow : α → StaticFlow)
    (value : α) (present : resultFlow value ∈ allowed) :
    ControlFlowAction activation allowed resultFlow (pure value) :=
  ⟨breakFrame_pure value, fun _ _ => present⟩

theorem controlFlow_stop (allowed : List StaticFlow) (resultFlow : α → StaticFlow)
    (reason : Goose.Core.Stop) : ControlFlowAction activation allowed resultFlow (EvalM.stop reason) :=
  ⟨breakFrame_stop reason, fun _ _ => True.intro⟩

theorem controlFlow_mono (first second : List StaticFlow) (resultFlow : α → StaticFlow)
    (action : EvalM α) (included : ∀ flow ∈ first, flow ∈ second)
    (checked : ControlFlowAction activation first resultFlow action) :
    ControlFlowAction activation second resultFlow action := by
  refine ⟨checked.frame, ?_⟩
  intro before bounded
  have reached := checked.outcome before bounded
  cases evaluated : action before with
  | ok value after => exact included _ (by simpa only [evaluated, ControlFlowOutcome] using reached)
  | stop reason after => trivial
  | escape address carriers after => trivial
  | jump id kind after =>
      simp only [evaluated, ControlFlowOutcome] at reached ⊢
      rcases reached with ⟨target, member, selected, compatible, equal, permitted⟩
      exact ⟨target, member, selected, compatible, equal, included _ permitted⟩

theorem controlFlow_bind (first second : List StaticFlow) (resultFlow : β → StaticFlow)
    (action : EvalM α) (next : α → EvalM β)
    (head : ControlFlowAction activation first (fun _ => normalFlow) action)
    (tail : ∀ value, ControlFlowAction activation second resultFlow (next value)) :
    ControlFlowAction activation (continueFlows first second) resultFlow (action >>= next) := by
  refine ⟨breakFrame_bind action next head.frame (fun value => (tail value).frame), ?_⟩
  intro before bounded
  have reached := head.outcome before bounded
  have framed := head.frame before bounded
  cases evaluated : action before with
  | ok value middle =>
      simp only [evaluated, ControlFlowOutcome] at reached
      simp only [evaluated] at framed
      change BreakStackFrame before middle at framed
      have continued := (tail value).outcome middle (framed.bounded bounded)
      cases finished : next value middle with
      | ok result after =>
          simp only [finished, ControlFlowOutcome] at continued
          simp only [bind, Bind.bind, evaluated, finished, ControlFlowOutcome]
          exact mem_continueFlows_second first second _ reached continued
      | stop reason after => simp only [bind, Bind.bind, evaluated, finished, ControlFlowOutcome]
      | escape address carriers after => simp only [bind, Bind.bind, evaluated, finished, ControlFlowOutcome]
      | jump id kind after =>
          simp only [finished, ControlFlowOutcome] at continued
          rcases continued with ⟨target, member, selected, compatible, equal, permitted⟩
          simp only [bind, Bind.bind, evaluated, finished, ControlFlowOutcome]
          exact ⟨target, by simpa only [framed.stack] using member, by simpa only [framed.stack] using selected, compatible, equal,
            mem_continueFlows_second first second _ reached permitted⟩
  | stop reason middle => simp only [bind, Bind.bind, evaluated, ControlFlowOutcome]
  | escape address carriers middle => simp only [bind, Bind.bind, evaluated, ControlFlowOutcome]
  | jump id kind middle =>
      simp only [evaluated, ControlFlowOutcome] at reached
      rcases reached with ⟨target, member, selected, compatible, equal, permitted⟩
      simp only [bind, Bind.bind, evaluated, ControlFlowOutcome]
      refine ⟨target, member, selected, compatible, equal, mem_continueFlows_first first second _ ?_ permitted⟩
      exact jumpControlFlow_ne_normal _ _

theorem controlFlow_normal (action : EvalM α) (frame : BreakFrameAction action)
    (noJump : ∀ before id kind after, action before ≠ .jump id kind after) :
    ControlFlowAction activation [normalFlow] (fun _ => normalFlow) action := by
  refine ⟨frame, ?_⟩
  intro before _
  cases evaluated : action before with
  | ok value after => exact List.mem_singleton_self _
  | stop reason after => trivial
  | escape address carriers after => trivial
  | jump id kind after => exact False.elim (noJump before id kind after evaluated)

theorem controlFlow_withScope (allowed : List StaticFlow) (resultFlow : α → StaticFlow)
    (environment : RuntimeActivation) (scope scopeInst : Nat) (action : EvalM α)
    (body : ControlFlowAction activation allowed resultFlow action) :
    ControlFlowAction activation allowed resultFlow (withScope environment scope scopeInst action) := by
  refine ⟨breakFrame_withScope environment scope scopeInst action body.frame, ?_⟩
  intro before bounded
  have reached := body.outcome before bounded
  cases evaluated : action before <;>
    simpa only [withScope, evaluated, releaseScope, bind, Bind.bind, EvalM.get, EvalM.set, ControlFlowOutcome] using reached

theorem controlFlow_jump {resultFlow : α → StaticFlow} (scope : BreakScope) (kind : JumpKind) (compatible : JumpScopeMatches scope kind) :
    ControlFlowAction activation [jumpControlFlow scope kind] resultFlow
      (do let target ← currentBreak activation (some scope); jump target.id kind) := by
  refine ⟨breakFrame_bind _ _ (breakFrame_currentBreak _ _) (fun target => breakFrame_jump _ _), ?_⟩
  intro before bounded
  cases selected : before.breaks.find? (fun target => target.act == activation && some scope == some target.scope) with
  | none =>
      simp only [bind, Bind.bind, currentBreak, EvalM.get, selected, Option.isNone_some, Bool.false_or, ControlFlowOutcome]
      trivial
  | some target =>
      have selectedScope := List.find?_some selected
      have scopeEqual : target.scope = scope := by
        simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at selectedScope
        exact selectedScope.2.symm
      simp only [bind, Bind.bind, currentBreak, EvalM.get, Option.isNone_some, Bool.false_or, selected, jump, ControlFlowOutcome]
      exact ⟨target, List.mem_of_find?_eq_some selected, by simpa only [scopeEqual] using selected,
        by simpa only [scopeEqual] using compatible, rfl, by simp only [scopeEqual, List.mem_singleton]⟩

#print axioms controlFlow_pure
#print axioms controlFlow_stop
#print axioms controlFlow_mono
#print axioms controlFlow_bind
#print axioms controlFlow_normal
#print axioms controlFlow_withScope
#print axioms controlFlow_jump

end Goose.Proofs.ConstructionDelivery
