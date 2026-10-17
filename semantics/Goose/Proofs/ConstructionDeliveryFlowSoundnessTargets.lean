import Goose.Proofs.ConstructionDeliveryFlowSoundnessOutcomes

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem preparedTargetsBounded (before : ExecutionState) (activation : Goose.Core.ActId)
    (scope : BreakScope) (channels : List Channel) (bounded : BreakTargetsBelowCounter before) :
    BreakTargetsBelowCounter { before with nextScope := before.nextScope + 1, breaks := ⟨before.nextScope, activation, scope, channels⟩ :: before.breaks } := by
  intro target present
  cases present with
  | head => exact Nat.lt_succ_self _
  | tail _ present => exact Nat.lt_trans (bounded target present) (Nat.lt_succ_self _)

theorem controlFlow_withBreakTarget (activation : Goose.Core.ActId) (scope : BreakScope)
    (channels : List Channel) (first second : List StaticFlow) (resultFlow : α → StaticFlow)
    (action : EvalM α) (receive : JumpKind → EvalM α)
    (body : ControlFlowAction activation first resultFlow action)
    (normalIncluded : ∀ value, resultFlow value ∈ first → resultFlow value ∈ second)
    (outerIncluded : ∀ outer kind, outer ≠ scope →
      jumpControlFlow outer kind ∈ first → jumpControlFlow outer kind ∈ second)
    (handlerFrame : ∀ kind, BreakFrameAction (receive kind))
    (handler : ∀ kind, jumpControlFlow scope kind ∈ first →
      ControlFlowAction activation second resultFlow (receive kind)) :
    ControlFlowAction activation second resultFlow (withBreakTarget activation scope channels action receive) := by
  refine ⟨breakFrame_withBreakTarget activation scope channels action receive body.frame handlerFrame, ?_⟩
  intro before bounded
  let prepared : ExecutionState := { before with nextScope := before.nextScope + 1, breaks := ⟨before.nextScope, activation, scope, channels⟩ :: before.breaks }
  have preparedBound : BreakTargetsBelowCounter prepared := preparedTargetsBounded before activation scope channels bounded
  have reached := body.outcome prepared preparedBound
  have framed := body.frame prepared preparedBound
  change ControlFlowOutcome activation before second resultFlow
    (match mapStepState
      (fun current => { current with breaks := current.breaks.filter (fun entry => entry.id != before.nextScope) })
      (action prepared) with
    | .jump actual kind after => if actual == before.nextScope then receive kind after else .jump actual kind after
    | result => result)
  cases evaluated : action prepared with
  | ok value after =>
      simp only [evaluated, ControlFlowOutcome] at reached
      exact normalIncluded value reached
  | stop reason after => trivial
  | escape address carriers after => trivial
  | jump id kind after =>
      simp only [evaluated, ControlFlowOutcome] at reached
      rcases reached with ⟨target, member, selected, compatible, equal, permitted⟩
      simp only [evaluated] at framed
      change BreakStackFrame prepared after at framed
      have restored := breakStackFrame_removeFreshTarget before after activation scope channels bounded framed
      have restoredStack : after.breaks.filter (fun entry => entry.id != before.nextScope) = before.breaks := restored.stack
      simp only [mapStepState]
      split
      · rename_i caught
        have identity : target.id = before.nextScope := equal.trans (beq_iff_eq.mp caught)
        have targetScope : target.scope = scope := by
          change target ∈ ⟨before.nextScope, activation, scope, channels⟩ :: before.breaks at member
          cases member with
          | head => rfl
          | tail _ prior => exact False.elim ((Nat.ne_of_lt (bounded target prior)) identity)
        have finished := (handler kind (by simpa only [targetScope] using permitted)).outcome _ (restored.bounded bounded)
        cases handled : receive kind { after with breaks := after.breaks.filter (fun entry => entry.id != before.nextScope) } with
        | ok value final => simpa only [handled, ControlFlowOutcome] using finished
        | stop reason final => trivial
        | escape address carriers final => trivial
        | jump actual nextKind final =>
            simp only [handled, ControlFlowOutcome] at finished ⊢
            rcases finished with ⟨outer, present, selection, scopeMatches, actualEqual, admitted⟩
            exact ⟨outer, by simpa only [restoredStack] using present,
              by simpa only [restoredStack] using selection, scopeMatches, actualEqual, admitted⟩
      · rename_i uncaught
        have targetDifferent : target.id ≠ before.nextScope := by
          intro same
          have : id = before.nextScope := equal.symm.trans same
          exact uncaught (beq_iff_eq.mpr this)
        have prior : target ∈ before.breaks := by
          change target ∈ ⟨before.nextScope, activation, scope, channels⟩ :: before.breaks at member
          cases member with
          | head => exact False.elim (targetDifferent rfl)
          | tail _ present => exact present
        have outerScope : target.scope ≠ scope := by
          intro same
          have chosen := selected
          change (⟨before.nextScope, activation, scope, channels⟩ :: before.breaks).find?
            (fun entry => entry.act == activation && some target.scope == some entry.scope) = some target at chosen
          simp only [same, List.find?_cons, beq_self_eq_true, Bool.true_and, Option.some.injEq] at chosen
          exact targetDifferent (congrArg BreakTarget.id chosen.symm)
        have scopeFalse : (some target.scope == (some scope : Option BreakScope)) = false := by
          apply beq_eq_false_iff_ne.mpr
          exact fun equal => outerScope (Option.some.inj equal)
        have priorSelected : before.breaks.find?
            (fun entry => entry.act == activation && some target.scope == some entry.scope) = some target := by
          change (⟨before.nextScope, activation, scope, channels⟩ :: before.breaks).find?
            (fun entry => entry.act == activation && some target.scope == some entry.scope) = some target at selected
          simpa only [List.find?_cons, beq_self_eq_true, Bool.true_and, scopeFalse] using selected
        exact ⟨target, prior, priorSelected, compatible, equal, outerIncluded _ _ outerScope permitted⟩

theorem controlFlow_withBreakTarget_jump_outer (activation : Goose.Core.ActId) (scope : BreakScope)
    (channels : List Channel) (allowed : List StaticFlow) (resultFlow : α → StaticFlow)
    (action : EvalM α) (receive : JumpKind → EvalM α)
    (body : ControlFlowAction activation allowed resultFlow action)
    (handler : ∀ kind before id nextKind after, receive kind before ≠ .jump id nextKind after)
    (before : ExecutionState) (bounded : BreakTargetsBelowCounter before)
    (id : Nat) (kind : JumpKind) (after : ExecutionState)
    (run : withBreakTarget activation scope channels action receive before = .jump id kind after) :
    ∃ target ∈ before.breaks,
      before.breaks.find? (fun entry => entry.act == activation && some target.scope == some entry.scope) = some target ∧
      target.id = id ∧ target.scope ≠ scope ∧
      JumpScopeMatches target.scope kind ∧ jumpControlFlow target.scope kind ∈ allowed := by
  let prepared : ExecutionState := { before with nextScope := before.nextScope + 1, breaks := ⟨before.nextScope, activation, scope, channels⟩ :: before.breaks }
  have reached := body.outcome prepared (preparedTargetsBounded before activation scope channels bounded)
  change (match mapStepState
    (fun current => { current with breaks := current.breaks.filter (fun entry => entry.id != before.nextScope) })
    (action prepared) with
    | .jump actual nextKind final => if actual == before.nextScope then receive nextKind final else .jump actual nextKind final
    | result => result) = .jump id kind after at run
  cases evaluated : action prepared with
  | ok value middle => simp only [evaluated, mapStepState] at run; cases run
  | stop reason middle => simp only [evaluated, mapStepState] at run; cases run
  | escape address carriers middle => simp only [evaluated, mapStepState] at run; cases run
  | jump actual nextKind middle =>
    simp only [evaluated, ControlFlowOutcome] at reached
    rcases reached with ⟨target, member, selected, compatible, equal, admitted⟩
    simp only [evaluated, mapStepState] at run
    split at run
    · exact False.elim (handler _ _ _ _ _ run)
    · rename_i uncaught
      cases run
      have different : target.id ≠ before.nextScope := by
        intro same
        exact uncaught (beq_iff_eq.mpr (equal.symm.trans same))
      have prior : target ∈ before.breaks := by
        change target ∈ ⟨before.nextScope, activation, scope, channels⟩ :: before.breaks at member
        cases member with
        | head => exact False.elim (different rfl)
        | tail _ present => exact present
      have outerScope : target.scope ≠ scope := by
        intro same
        change (⟨before.nextScope, activation, scope, channels⟩ :: before.breaks).find?
          (fun entry => entry.act == activation && some target.scope == some entry.scope) = some target at selected
        simp only [same, List.find?_cons, beq_self_eq_true, Bool.true_and, Option.some.injEq] at selected
        exact different (congrArg BreakTarget.id selected.symm)
      have scopeFalse : (some target.scope == (some scope : Option BreakScope)) = false := by
        apply beq_eq_false_iff_ne.mpr
        exact fun equal => outerScope (Option.some.inj equal)
      have priorSelected : before.breaks.find?
          (fun entry => entry.act == activation && some target.scope == some entry.scope) = some target := by
        change (⟨before.nextScope, activation, scope, channels⟩ :: before.breaks).find?
          (fun entry => entry.act == activation && some target.scope == some entry.scope) = some target at selected
        simpa only [List.find?_cons, beq_self_eq_true, Bool.true_and, scopeFalse] using selected
      exact ⟨target, prior, priorSelected, equal, outerScope, compatible, admitted⟩

#print axioms controlFlow_withBreakTarget
#print axioms controlFlow_withBreakTarget_jump_outer

end Goose.Proofs.ConstructionDelivery
