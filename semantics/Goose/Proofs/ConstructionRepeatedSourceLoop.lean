import Goose.Proofs.ConstructionRepeatedSourceSnapshot

set_option Elab.async false

namespace Goose.Proofs.ConstructionRepeatedSourceSnapshot
open Goose.Construct Goose.Core

private theorem destinationCurrent_indexing (before after : ConstructionState)
    (size : after.destinations.size = before.destinations.size)
    (successors : after.destinationSuccessors = before.destinationSuccessors) (incoming : DestinationId) :
    destinationCurrent after incoming = destinationCurrent before incoming := by
  have steps : ∀ fuel id, destinationCurrentSteps fuel after id = destinationCurrentSteps fuel before id := by
    intro fuel
    induction fuel with
    | zero => intro id; rfl
    | succ fuel ih =>
        intro id
        simp only [destinationCurrentSteps_succ, size, successors]
        split
        · cases found : before.destinationSuccessors.lookup id with
          | none => rfl
          | some next =>
              simp only [found]
              split
              · exact ih next
              · rfl
        · rfl
  simp only [destinationCurrent_result, size, steps]

private theorem recordCopy_repeat_success (state after : ConstructionState)
    (parentId sourceId : DestinationId) (parent source : PendingDestination) (parentCount sourceCount : Nat)
    (parentFound : state.destinations[parentId]? = some parent)
    (parentOpen : parent.progress = .open parentCount)
    (sourceFound : state.destinations[sourceId]? = some source)
    (sourceBuilt : source.progress = .built sourceCount)
    (executed : recordCopy (.repeat sourceId) parentId state = .ok () after) :
    after = { state with events := state.events ++ [.copy (.repeat sourceId) parentId] } := by
  simp only [recordCopy, writableDestination_result, parentFound, bind] at executed
  cases allowed : destinationCanWrite state parentId with
  | false => simp only [allowed] at executed; cases executed
  | true =>
      simp only [allowed, parentOpen, lookupDestination_result, sourceFound, sourceBuilt,
        emit_result, pure] at executed
      cases executed
      rfl

theorem repeatElement_success_parent (fuel : Nat) (layout : LayoutEnv)
    (incoming parentId sourceId : DestinationId) (element : Construct.Ty) (origin : OriginId)
    (state after : ExecutionState) (parent source : PendingDestination) (storage : ReceivingStorage)
    (parentCount sourceCount : Nat)
    (resolved : destinationCurrent state.construction incoming = .ok parentId)
    (parentFound : state.construction.destinations[parentId]? = some parent)
    (parentOpen : parent.progress = .open parentCount)
    (sourceFound : state.construction.destinations[sourceId]? = some source)
    (sourceBuilt : source.progress = .built sourceCount)
    (sourceStorage : state.construction.storage[source.storage]? = some storage)
    (executed : repeatElement fuel layout incoming element sourceId origin state = .ok () after) :
    ∃ current, after.construction.destinations[parentId]? = some current ∧
      current.backing = parent.backing ∧ current.progress = .open (parentCount + 1) ∧
      destinationCurrent after.construction incoming = .ok parentId := by
  cases fuel with
  | zero => simp only [repeatElement, Construct.timeout, EvalM.stop] at executed; cases executed
  | succ fuel =>
      rw [repeatElement_readsSnapshot fuel layout incoming parentId sourceId element origin state parent source storage
        parentCount sourceCount resolved parentFound parentOpen sourceFound sourceBuilt sourceStorage] at executed
      cases measured : packedEnd fuel layout element storage.bytes source.capability.start with
      | error reason =>
          cases reason <;> simp only [liftLayout, measured, Construct.fault, Construct.timeout, EvalM.stop, bind] at executed <;> cases executed
      | ok finish =>
          simp only [liftLayout, measured, pure, bind, liftConstruction] at executed
          cases copied : recordCopy (.repeat sourceId) parentId state.construction with
          | fault reason middle => simp only [copied] at executed; cases executed
          | ok token middle =>
              cases token
              have same := recordCopy_repeat_success state.construction middle parentId sourceId parent source
                parentCount sourceCount parentFound parentOpen sourceFound sourceBuilt copied
              subst middle
              simp only [copied, bind] at executed
              cases written : writeElement parentId (storage.bytes.extract source.capability.start finish)
                  { state.construction with events := state.construction.events ++ [.copy (.repeat sourceId) parentId] } with
              | fault reason final => simp only [written] at executed; cases executed
              | ok token final =>
                  cases token
                  simp only [written] at executed
                  cases executed
                  have found := Goose.Proofs.ConstructionStorage.writeElement_success_destination parentId
                    (storage.bytes.extract source.capability.start finish)
                    { state.construction with events := state.construction.events ++ [.copy (.repeat sourceId) parentId] }
                    final parent parentCount parentFound parentOpen written
                  have indexed := Goose.Proofs.ConstructionStorage.writeElement_preserves_indexing parentId
                    (storage.bytes.extract source.capability.start finish)
                    { state.construction with events := state.construction.events ++ [.copy (.repeat sourceId) parentId] }
                  simp only [written, ConstructionResult.finalState] at indexed
                  refine ⟨_, found.1, rfl, rfl, ?_⟩
                  exact (destinationCurrent_indexing state.construction final indexed.1 indexed.2 incoming).trans resolved

def RepeatedSourceLoopOutcome (incoming parentId sourceId : DestinationId)
    (source : PendingDestination) (storage : ReceivingStorage) (parentBacking : DestinationBacking)
    (parentCount repetitions : Nat) (result : ExecutionStep PUnit) : Prop :=
  (((stepState result).construction.destinations[sourceId]?,
    (stepState result).construction.storage[source.storage]?) = (some source, some storage)) ∧
    match result with
    | .ok _ after => ∃ current, after.construction.destinations[parentId]? = some current ∧
        current.backing = parentBacking ∧ current.progress = .open (parentCount + repetitions) ∧
        destinationCurrent after.construction incoming = .ok parentId
    | .stop _ _ | .escape _ _ _ | .jump _ _ _ => True

theorem repeatElement_fillLoop (fuel : Nat) (layout : LayoutEnv)
    (incoming parentId sourceId : DestinationId) (element : Construct.Ty) (origin : OriginId)
    (state : ExecutionState) (parent source : PendingDestination) (storage : ReceivingStorage)
    (parentCount sourceCount repetitions : Nat)
    (resolved : destinationCurrent state.construction incoming = .ok parentId)
    (parentFound : state.construction.destinations[parentId]? = some parent)
    (parentOpen : parent.progress = .open parentCount)
    (sourceFound : state.construction.destinations[sourceId]? = some source)
    (sourceBuilt : source.progress = .built sourceCount)
    (sourceStorage : state.construction.storage[source.storage]? = some storage)
    (separate : source.storage ≠ parent.storage) :
    RepeatedSourceLoopOutcome incoming parentId sourceId source storage parent.backing parentCount repetitions
      ((forIn [0:repetitions] PUnit.unit fun _ _ => do
          repeatElement fuel layout incoming element sourceId origin
          pure (.yield PUnit.unit)) state) := by
  have all : ∀ (steps : List Nat) (state : ExecutionState) (parent : PendingDestination) (parentCount : Nat),
      (destinationCurrent state.construction incoming = .ok parentId ∧
        state.construction.destinations[parentId]? = some parent ∧ parent.progress = .open parentCount ∧
        state.construction.destinations[sourceId]? = some source ∧
        state.construction.storage[source.storage]? = some storage ∧ source.storage ≠ parent.storage) →
      RepeatedSourceLoopOutcome incoming parentId sourceId source storage parent.backing parentCount steps.length
        ((forIn steps PUnit.unit fun _ _ => do
            repeatElement fuel layout incoming element sourceId origin
            pure (.yield PUnit.unit)) state) := by
    intro steps
    induction steps with
    | nil =>
        intro before owner count valid
        rcases valid with ⟨resolved, found, opened, sourceFound, sourceStorage, separate⟩
        exact ⟨by simp only [List.forIn_nil, pure, stepState, sourceFound, sourceStorage],
          owner, found, rfl, opened, resolved⟩
    | cons index rest ih =>
        intro before owner count valid
        rcases valid with ⟨resolved, found, opened, sourceFound, sourceStorage, separate⟩
        have snapshot := repeatElement_sourceFrame fuel layout incoming parentId sourceId element origin
          before owner source storage count sourceCount resolved found opened sourceFound sourceBuilt sourceStorage separate
        cases evaluated : repeatElement fuel layout incoming element sourceId origin before with
        | ok token middle =>
            cases token
            obtain ⟨current, currentFound, sameBacking, currentOpen, currentResolved⟩ :=
              repeatElement_success_parent fuel layout incoming parentId sourceId element origin before middle
                owner source storage count sourceCount resolved found opened sourceFound sourceBuilt sourceStorage evaluated
            simp only [evaluated, stepState] at snapshot
            have sameStorage : current.storage = owner.storage :=
              congrArg DestinationBacking.writeStorage sameBacking
            have next := ih middle current (count + 1)
              ⟨currentResolved, currentFound, currentOpen, congrArg Prod.fst snapshot, congrArg Prod.snd snapshot,
                by rw [sameStorage]; exact separate⟩
            simp only [List.forIn_cons, bind, evaluated, pure]
            simpa only [RepeatedSourceLoopOutcome, bind, pure, sameBacking, List.length_cons,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next
        | stop reason middle | escape target carriers middle | jump target kind middle =>
            simp only [RepeatedSourceLoopOutcome, List.forIn_cons, bind, evaluated, pure]
            exact ⟨by simpa only [evaluated] using snapshot, True.intro⟩
  simpa [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size] using
    all (List.range' 0 repetitions 1) state parent parentCount
      ⟨resolved, parentFound, parentOpen, sourceFound, sourceStorage, separate⟩

#print axioms repeatElement_success_parent
#print axioms repeatElement_fillLoop

end Goose.Proofs.ConstructionRepeatedSourceSnapshot
