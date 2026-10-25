import Goose.Construct.Runtime

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

def BreakTargetsBelowCounter (state : ExecutionState) : Prop :=
  ∀ target ∈ state.breaks, target.id < state.nextScope

structure BreakStackFrame (before after : ExecutionState) : Prop where
  counter : before.nextScope ≤ after.nextScope
  stack : after.breaks = before.breaks

theorem BreakStackFrame.refl (state : ExecutionState) : BreakStackFrame state state :=
  ⟨Nat.le_refl _, rfl⟩

theorem BreakStackFrame.trans {before middle after : ExecutionState}
    (head : BreakStackFrame before middle) (tail : BreakStackFrame middle after) :
    BreakStackFrame before after :=
  ⟨Nat.le_trans head.counter tail.counter, tail.stack.trans head.stack⟩

theorem BreakStackFrame.bounded {before after : ExecutionState}
    (frame : BreakStackFrame before after) (bounded : BreakTargetsBelowCounter before) :
    BreakTargetsBelowCounter after := by
  intro target present
  rw [frame.stack] at present
  exact Nat.lt_of_lt_of_le (bounded target present) frame.counter

private def BreakStepFrame (before : ExecutionState) : ExecutionStep α → Prop
  | .ok _ after | .stop _ after | .escape _ _ after | .jump _ _ after => BreakStackFrame before after

def BreakFrameAction (action : EvalM α) : Prop :=
  ∀ state, BreakTargetsBelowCounter state → BreakStepFrame state (action state)

theorem breakFrame_pure (value : α) : BreakFrameAction (pure value) := by
  intro state _
  exact BreakStackFrame.refl state

theorem breakFrame_stop (reason : Goose.Core.Stop) : BreakFrameAction (EvalM.stop (α := α) reason) := by
  intro state _
  exact BreakStackFrame.refl state

theorem breakFrame_get : BreakFrameAction EvalM.get := by
  intro state _
  exact BreakStackFrame.refl state

theorem breakFrame_jump (target : Nat) (kind : JumpKind) : BreakFrameAction (jump (α := α) target kind) := by
  intro state _
  exact BreakStackFrame.refl state

theorem breakFrame_bind (action : EvalM α) (next : α → EvalM β)
    (head : BreakFrameAction action) (tail : ∀ value, BreakFrameAction (next value)) :
    BreakFrameAction (action >>= next) := by
  intro state bounded
  have first := head state bounded
  cases evaluated : action state with
  | ok value middle =>
      simp only [evaluated, BreakStepFrame] at first
      have second := tail value middle (first.bounded bounded)
      simp only [bind, Bind.bind, evaluated]
      cases result : next value middle <;>
        simp only [result, BreakStepFrame] at second ⊢ <;> exact first.trans second
  | stop reason middle => simpa only [bind, Bind.bind, evaluated, BreakStepFrame] using first
  | escape address carriers middle => simpa only [bind, Bind.bind, evaluated, BreakStepFrame] using first
  | jump target kind middle => simpa only [bind, Bind.bind, evaluated, BreakStepFrame] using first

theorem breakFrame_liftConstruction (origin : Goose.Core.OriginId) (action : ConstructionM α) :
    BreakFrameAction (liftConstruction origin action) := by
  intro state _
  cases result : action state.construction <;>
    simp only [liftConstruction, result, BreakStepFrame] <;> exact ⟨Nat.le_refl _, rfl⟩

theorem breakFrame_freshScope : BreakFrameAction freshScope := by
  intro state _
  change BreakStackFrame state { state with nextScope := state.nextScope + 1 }
  exact ⟨Nat.le_succ _, rfl⟩

theorem breakFrame_freshAct : BreakFrameAction freshAct := by
  intro state _
  change BreakStackFrame state { state with nextAct := state.nextAct + 1 }
  exact ⟨Nat.le_refl _, rfl⟩

theorem breakFrame_get_bind (action : ExecutionState → EvalM α)
    (preserved : ∀ state, BreakTargetsBelowCounter state → BreakStepFrame state (action state state)) :
    BreakFrameAction (EvalM.get >>= action) := by
  intro state bounded
  exact preserved state bounded

theorem breakStackFrame_removeFreshTarget (before after : ExecutionState)
    (act : Goose.Core.ActId) (scope : BreakScope) (channels : List Channel)
    (bounded : BreakTargetsBelowCounter before)
    (frame : BreakStackFrame
      { before with nextScope := before.nextScope + 1, breaks := ⟨before.nextScope, act, scope, channels⟩ :: before.breaks } after) :
    BreakStackFrame before
      { after with breaks := after.breaks.filter (fun entry => entry.id != before.nextScope) } := by
  constructor
  · exact Nat.le_trans (Nat.le_succ _) frame.counter
  · change after.breaks.filter (fun entry => entry.id != before.nextScope) = before.breaks
    rw [frame.stack]
    have original : before.breaks.filter (fun entry => entry.id != before.nextScope) = before.breaks := by
      apply List.filter_eq_self.mpr
      intro target present
      simpa only [bne_iff_ne] using Nat.ne_of_lt (bounded target present)
    simpa using original

theorem breakFrame_withBreakTarget (act : Goose.Core.ActId) (scope : BreakScope)
    (channels : List Channel) (action : EvalM α) (receive : JumpKind → EvalM α)
    (body : BreakFrameAction action) (handler : ∀ kind, BreakFrameAction (receive kind)) :
    BreakFrameAction (withBreakTarget act scope channels action receive) := by
  intro state bounded
  let prepared : ExecutionState :=
    { state with nextScope := state.nextScope + 1, breaks := ⟨state.nextScope, act, scope, channels⟩ :: state.breaks }
  have preparedBound : BreakTargetsBelowCounter prepared := by
    intro target present
    change target ∈ ⟨state.nextScope, act, scope, channels⟩ :: state.breaks at present
    cases present with
    | head => exact Nat.lt_succ_self _
    | tail _ present => exact Nat.lt_trans (bounded target present) (Nat.lt_succ_self _)
  have checked := body prepared preparedBound
  change BreakStepFrame state
    (match mapStepState
      (fun current => { current with breaks := current.breaks.filter (fun entry => entry.id != state.nextScope) })
      (action prepared) with
    | .jump actual kind after =>
        if actual == state.nextScope then receive kind after else .jump actual kind after
    | result => result)
  cases result : action prepared with
  | ok value after =>
      simp only [result, BreakStepFrame] at checked
      exact breakStackFrame_removeFreshTarget state after act scope channels bounded checked
  | stop reason after =>
      simp only [result, BreakStepFrame] at checked
      exact breakStackFrame_removeFreshTarget state after act scope channels bounded checked
  | escape address carriers after =>
      simp only [result, BreakStepFrame] at checked
      exact breakStackFrame_removeFreshTarget state after act scope channels bounded checked
  | jump target kind after =>
      simp only [result, BreakStepFrame] at checked
      have restored := breakStackFrame_removeFreshTarget state after act scope channels bounded checked
      dsimp only [mapStepState]
      split
      · have finished := handler kind _ (restored.bounded bounded)
        cases received : receive kind
            { after with breaks := after.breaks.filter (fun entry => entry.id != state.nextScope) } <;>
          simp only [received, BreakStepFrame] at finished ⊢ <;> exact restored.trans finished
      · exact restored

theorem breakFrame_releaseScope (environment : RuntimeActivation) (scope scopeInst : Nat) :
    BreakFrameAction (releaseScope environment scope scopeInst) := by
  intro state _
  change BreakStackFrame state (releaseScopeState environment scope scopeInst state)
  exact ⟨Nat.le_refl _, rfl⟩

theorem breakFrame_withScope (environment : RuntimeActivation) (scope scopeInst : Nat)
    (action : EvalM α) (body : BreakFrameAction action) :
    BreakFrameAction (withScope environment scope scopeInst action) := by
  intro state bounded
  have checked := body state bounded
  cases result : action state with
  | ok value after =>
      simp only [result, BreakStepFrame] at checked
      simp only [withScope, result]
      change BreakStackFrame state (releaseScopeState environment scope scopeInst after)
      exact ⟨checked.counter, checked.stack⟩
  | stop reason after =>
      simpa only [withScope, result, BreakStepFrame] using checked
  | escape address carriers after =>
      simp only [result, BreakStepFrame] at checked
      simp only [withScope, result]
      change BreakStackFrame state (releaseScopeState environment scope scopeInst after)
      exact ⟨checked.counter, checked.stack⟩
  | jump target kind after =>
      simp only [result, BreakStepFrame] at checked
      simp only [withScope, result]
      change BreakStackFrame state (releaseScopeState environment scope scopeInst after)
      exact ⟨checked.counter, checked.stack⟩

theorem BreakTargetsBelowCounter.initial : BreakTargetsBelowCounter .initial := by
  intro target present
  cases present

#print axioms BreakTargetsBelowCounter.initial
#print axioms BreakStackFrame.refl
#print axioms BreakStackFrame.trans
#print axioms BreakStackFrame.bounded
#print axioms breakFrame_pure
#print axioms breakFrame_stop
#print axioms breakFrame_get
#print axioms breakFrame_jump
#print axioms breakFrame_bind
#print axioms breakFrame_liftConstruction
#print axioms breakFrame_freshScope
#print axioms breakFrame_freshAct
#print axioms breakFrame_get_bind
#print axioms breakFrame_withBreakTarget
#print axioms breakFrame_releaseScope
#print axioms breakFrame_withScope

end Goose.Proofs.ConstructionDelivery
