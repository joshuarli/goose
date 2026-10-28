import Goose.Construct.Destination
import Goose.Proofs.ConstructionExecutionProtocolReservationFrontier

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

theorem constructionM_pure_bind (value : α) (next : α → ConstructionM β) :
    pure value >>= next = next value := rfl

theorem constructionM_bind_assoc (action : ConstructionM α) (first : α → ConstructionM β)
    (next : β → ConstructionM γ) :
    (action >>= first) >>= next = action >>= fun value => first value >>= next := by
  funext state
  simp only [bind]
  cases action state <;> rfl

theorem constructionM_if_bind (condition : Prop) [Decidable condition]
    (yes no : ConstructionM α) (next : α → ConstructionM β) :
    (if condition then yes else no) >>= next =
      if condition then yes >>= next else no >>= next := by
  by_cases selected : condition <;> simp only [selected, ↓reduceIte]

open Lean Elab Term Meta in
elab "prepare_exit_head" : term => do
  let declaration ← getConstInfo ``Goose.Construct.prepareExitDestination_equation
  forallTelescope declaration.type fun _ body => do
    return body.getAppArgs[1]!.getAppFn

abbrev prepareExitDestinationAction : DestinationId → ExitSource → ConstructionM (DestinationId × PendingDestination) :=
  prepare_exit_head

abbrev reserveLookupStep (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (lookupDestination_result id state)

theorem reserveExitDestination_equation (incoming : DestinationId) (source : ExitSource) :
    reserveExitDestination incoming source = (do
      let named := source == ExitSource.namedResult
      let current ← renewReceivingDestination incoming
      let state ← ConstructionM.get
      let current ← if named then pure current else exitFrontierAction (state.destinations.size + 1) current
      let snapshot ← reserveLookupStep current
      let direct := match snapshot.progress with | .open 0 => true | _ => false
      let selected ← if direct || named then pure current else openExitReplacement current
      let state ← ConstructionM.get
      let token := state.exitReservations.size
      ConstructionM.set {state with exitReservations := state.exitReservations.push (.active (if named then .named .awaitingSource else .fresh) incoming selected snapshot)}
      pure (token, selected)) := by
  unfold reserveExitDestination
  rw [prepareExitDestination_equation]
  simp only [constructionM_bind_assoc, constructionM_pure_bind, constructionM_if_bind]
  rfl

theorem constructionInvariant_bind (predicate : ConstructionState → Prop)
    (action : ConstructionM α) (next : α → ConstructionM β)
    (first : ∀ state, predicate state → predicate (action state).finalState)
    (remaining : ∀ value state, predicate state → predicate (next value state).finalState)
    (state : ConstructionState) (valid : predicate state) :
    predicate ((action >>= next) state).finalState := by
  have middle := first state valid
  cases evaluated : action state with
  | fault reason final => simpa only [evaluated, bind, ConstructionResult.finalState] using middle
  | ok value after =>
      simp only [evaluated, ConstructionResult.finalState] at middle
      simpa only [evaluated, bind] using remaining value after middle

theorem constructionInvariant_forIn (predicate : ConstructionState → Prop) (items : List α)
    (action : α → β → ConstructionM (ForInStep β)) (initial : β)
    (preserved : ∀ item value state, predicate state → predicate (action item value state).finalState)
    (state : ConstructionState) (valid : predicate state) :
    predicate (forIn items initial action state).finalState := by
  induction items generalizing initial state with
  | nil => exact valid
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply constructionInvariant_bind predicate _ _ (preserved item initial)
      intro step after afterValid
      cases step with
      | done value => exact afterValid
      | yield value => exact ih value after afterValid
      exact valid

theorem constructionInvariant_forEach (predicate : ConstructionState → Prop) (items : List α)
    (action : α → ConstructionM Unit)
    (preserved : ∀ item state, predicate state → predicate (action item state).finalState)
    (state : ConstructionState) (valid : predicate state) :
    predicate (((do for item in items do action item) : ConstructionM Unit) state).finalState := by
  apply constructionInvariant_bind predicate
  · intro current currentValid
    apply constructionInvariant_forIn predicate
    · intro item value after afterValid
      apply constructionInvariant_bind predicate (action item)
      · exact preserved item
      · intro _ final finalValid
        exact finalValid
      · exact afterValid
    · exact currentValid
  · intro _ after afterValid
    exact afterValid
  · exact valid

end Goose.Proofs.ConstructionExecutionProtocol
