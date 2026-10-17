import Goose.Proofs.ConstructionExecutionProtocolOwnersAncestry
import Goose.Proofs.ConstructionExecutionProtocolReservationCombinators
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct Goose.Core

private abbrev namedWritable (id : DestinationId) : ConstructionM PendingDestination := fun state =>
  (fun {left right : ConstructionResult PendingDestination} (_ : left = right) => left)
    (writableDestination_result id state)

private abbrev namedReplace (id : DestinationId) (destination : PendingDestination) : ConstructionM Unit := fun state =>
  (fun {left right : ConstructionResult Unit} (_ : left = right) => left)
    (replaceDestination_result id destination state)

private def namedActive (destination : PendingDestination) : Bool :=
  match destination.progress with
  | .open _ | .suspended _ _ | .built _ | .exiting _ _ => true
  | .published _ | .attached _ | .abandoned | .cancelled | .retired => false

local syntax "named_tree_split_if" : tactic
elab_rules : tactic
  | `(tactic| named_tree_split_if) => Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let some (yes, no) ← Lean.Meta.splitIfTarget? goal
        | Lean.throwError "no named tree condition to split"
      return [yes.mvarId, no.mvarId]

private theorem abandonDestination_other_row (id index : DestinationId) (state : ConstructionState)
    (different : id ≠ index) :
    (abandonDestination id state).finalState.destinations[index]? = state.destinations[index]? := by
  simp only [abandonDestination, writableDestination_result, bind]
  cases found : state.destinations[id]? with
  | none => rfl
  | some destination =>
    simp only [found]
    cases allowed : destinationCanWrite state id with
    | false => rfl
    | true =>
      simp only [allowed]
      cases progress : destination.progress <;> simp only [progress] <;> try rfl
      all_goals
        simp only [lookupStorage_result, bind]
        cases stored : state.storage[destination.storage]? with
        | none => rfl
        | some storage =>
          simp only [stored, replaceStorage_result, bind]
          named_tree_split_if
          · simp only [replaceDestination_result, bind]
            named_tree_split_if
            · simp [emit_result, bind, ConstructionResult.finalState,
                Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different]
            · rfl
          · rfl

private def namedTreeStep (destination : PendingDestination) : ConstructionM Unit := do
  let current ← namedWritable destination.capability.id
  match current.progress with
  | .suspended count _ => namedReplace current.capability.id {current with progress := .open count}
  | _ => pure ()
  abandonDestination destination.capability.id

private theorem namedTreeStep_other_row (destination : PendingDestination) (index : DestinationId)
    (different : destination.capability.id ≠ index) (initial : Option PendingDestination)
    (state : ConstructionState)
    (valid : DestinationCapabilitiesIndexed state ∧ state.destinations[index]? = initial) :
    DestinationCapabilitiesIndexed (namedTreeStep destination state).finalState ∧
      (namedTreeStep destination state).finalState.destinations[index]? = initial := by
  have abandon (before : ConstructionState)
      (beforeValid : DestinationCapabilitiesIndexed before ∧ before.destinations[index]? = initial) :
      DestinationCapabilitiesIndexed (abandonDestination destination.capability.id before).finalState ∧
        (abandonDestination destination.capability.id before).finalState.destinations[index]? = initial :=
    ⟨abandonDestination_destination_capabilities _ before beforeValid.1,
      (abandonDestination_other_row _ _ before different).trans beforeValid.2⟩
  simp only [namedTreeStep, namedWritable, writableDestination_result, bind]
  cases found : state.destinations[destination.capability.id]? with
  | none => exact valid
  | some current =>
    simp only [found]
    cases allowed : destinationCanWrite state destination.capability.id with
    | false => exact valid
    | true =>
      simp only [allowed]
      have correct := valid.1 destination.capability.id current found
      cases progress : current.progress <;> simp only [progress] <;> try exact abandon state valid
      case suspended count child =>
        have inside := (Array.getElem?_eq_some_iff.mp found).choose
        simp only [namedReplace, replaceDestination_result, correct, inside, ↓reduceIte, bind]
        apply abandon
        constructor
        · intro queried row present
          simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at present
          by_cases same : destination.capability.id = queried
          · subst queried
            simp only [inside, ↓reduceIte, Option.some.injEq] at present
            subst row
            exact correct
          · exact valid.1 queried row (by simpa only [same, ↓reduceIte] using present)
        · simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne different] using valid.2

private abbrev namedTreeForInStep (destination : PendingDestination) (_ : PUnit) :
    ConstructionM (ForInStep PUnit) := do
  let current ← namedWritable destination.capability.id
  match current.progress with
  | .suspended count _ =>
    namedReplace current.capability.id {current with progress := .open count}
    abandonDestination destination.capability.id
    pure (.yield ⟨⟩)
  | _ =>
    abandonDestination destination.capability.id
    pure (.yield ⟨⟩)

private theorem namedTreeForInStep_other_row (destination : PendingDestination) (token : PUnit)
    (index : DestinationId) (different : destination.capability.id ≠ index)
    (initial : Option PendingDestination) (state : ConstructionState)
    (valid : DestinationCapabilitiesIndexed state ∧ state.destinations[index]? = initial) :
    DestinationCapabilitiesIndexed (namedTreeForInStep destination token state).finalState ∧
      (namedTreeForInStep destination token state).finalState.destinations[index]? = initial := by
  have equivalent : namedTreeForInStep destination token =
      namedTreeStep destination >>= fun _ => pure (.yield PUnit.unit) := by
    funext current
    simp only [namedTreeForInStep, namedTreeStep, bind]
    cases found : namedWritable destination.capability.id current with
    | fault kind after => rfl
    | ok row after =>
      cases progress : row.progress <;> simp only [progress] <;> try rfl
      case suspended count child =>
        cases namedReplace row.capability.id {row with progress := .open count} after <;> rfl
  rw [equivalent]
  have preserved := namedTreeStep_other_row destination index different initial state valid
  cases result : namedTreeStep destination state <;>
    simpa only [result, bind, pure, ConstructionResult.finalState] using preserved

private theorem namedTreeForInInvariant (predicate : ConstructionState → Prop) (items : List α)
    (action : α → β → ConstructionM (ForInStep β)) (initial : β)
    (preserved : ∀ item ∈ items, ∀ value state, predicate state → predicate (action item value state).finalState)
    (state : ConstructionState) (valid : predicate state) :
    predicate (forIn items initial action state).finalState := by
  induction items generalizing initial state with
  | nil => exact valid
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply constructionInvariant_bind predicate _ _ (preserved item (by simp) initial)
    · intro step after afterValid
      cases step with
      | done value => exact afterValid
      | yield value => exact ih value (fun next member => preserved next (by simp [member])) after afterValid
    · exact valid

set_option maxHeartbeats 1000000 in
theorem abandonTree_earlier_destination (id index : DestinationId) (state : ConstructionState)
    (earlier : index < id) (valid : DestinationLifecycleInvariant state) :
    (abandonTree id state).finalState.destinations[index]? = state.destinations[index]? := by
  have outside : ∀ destination ∈ state.destinations.toList.reverse.filter
      (fun destination => destinationDescendant state.destinations id destination.capability.id && namedActive destination),
      destination.capability.id ≠ index := by
    intro destination member same
    have descendant := (Bool.and_eq_true_iff.mp (List.mem_filter.mp member).2).1
    rw [same] at descendant
    have impossible := destinationDescendant_false_of_lt state valid.2.2.2 id index earlier
    simp [impossible] at descendant
  have preserved : DestinationCapabilitiesIndexed (abandonTree id state).finalState ∧
      (abandonTree id state).finalState.destinations[index]? = state.destinations[index]? := by
    simp only [abandonTree, writableDestination_result, bind]
    cases found : state.destinations[id]? with
    | none => exact ⟨valid.2.1, rfl⟩
    | some parent =>
      simp only [found]
      cases allowed : destinationCanWrite state id with
      | false => exact ⟨valid.2.1, rfl⟩
      | true =>
        simp only [allowed]
        cases progress : parent.progress <;> simp only [progress] <;> try exact ⟨valid.2.1, rfl⟩
        all_goals
          simp only [pure, bind, ConstructionM.get]
          apply constructionInvariant_bind (fun current => DestinationCapabilitiesIndexed current ∧ current.destinations[index]? = state.destinations[index]?)
          · intro before beforeValid
            apply constructionInvariant_forIn (fun current => DestinationCapabilitiesIndexed current ∧ current.destinations[index]? = state.destinations[index]?)
            · intro destination token current currentValid
              cases destination with
              | mk capability backing layout use progress writeEnd rollbackEnd known adaptation =>
                cases progress <;> exact currentValid
            · exact beforeValid
          · intro token after afterValid
            apply constructionInvariant_bind (fun current => DestinationCapabilitiesIndexed current ∧ current.destinations[index]? = state.destinations[index]?)
            · intro before beforeValid
              apply namedTreeForInInvariant (fun current => DestinationCapabilitiesIndexed current ∧ current.destinations[index]? = state.destinations[index]?)
              · intro destination member token current currentValid
                have expected := namedTreeForInStep_other_row destination token index
                  (outside destination member) _ current currentValid
                simp only [namedTreeForInStep, namedWritable, writableDestination_result, namedReplace, replaceDestination_result, bind] at expected ⊢
                exact expected
              · exact beforeValid
            · intro result final finalValid
              exact finalValid
            · exact afterValid
          · exact ⟨valid.2.1, rfl⟩
  exact preserved.2

end Goose.Proofs.ConstructionExecutionProtocol
