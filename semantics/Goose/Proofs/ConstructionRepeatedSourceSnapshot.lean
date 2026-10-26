import Goose.Construct.Eval
import Goose.Proofs.ConstructionElementWriteTransition
import Lean.Elab.Tactic.Split

set_option Elab.async false

namespace Goose.Proofs.ConstructionRepeatedSourceSnapshot
open Goose.Construct Goose.Core

theorem writeElement_sourceFrame (id : DestinationId) (bytes : ByteArray)
    (state : ConstructionState) (source : StorageId) (sourceId : DestinationId) (destination : PendingDestination)
    (found : state.destinations[id]? = some destination)
    (separate : source ≠ destination.storage) (distinct : sourceId ≠ id) :
    ((writeElement id bytes state).finalState.destinations[sourceId]?,
      (writeElement id bytes state).finalState.storage[source]?) =
        (state.destinations[sourceId]?, state.storage[source]?) := by
  have transition := Goose.Proofs.ConstructionStorage.writeElement_transition id bytes state
  generalize evaluated : writeElement id bytes state = result at transition ⊢
  cases transition with
  | rejected reason => rfl
  | written actual storage count present stored opened =>
      have same := Option.some.inj (present.symm.trans found)
      subst actual
      simp [ConstructionResult.finalState, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds, Ne.symm separate, Ne.symm distinct]

theorem recordCopy_sourceFrame (source : CopySource) (id : DestinationId)
    (state : ConstructionState) :
    ((recordCopy source id state).finalState.destinations,
      (recordCopy source id state).finalState.storage) = (state.destinations, state.storage) := by
  simp only [recordCopy, writableDestination_result, bind]
  cases found : state.destinations[id]? with
  | none => rfl
  | some destination =>
      cases allowed : destinationCanWrite state id with
      | false => rfl
      | true =>
          simp only [allowed, bind]
          cases progress : destination.progress <;> simp only [progress, bind]
          all_goals try rfl
          case «open» count =>
            cases source with
            | storage storageId path =>
                simp only [lookupStorage_result, bind]
                cases state.storage[storageId]? <;> rfl
            | «repeat» sourceId =>
                simp only [lookupDestination_result, bind]
                cases foundSource : state.destinations[sourceId]? with
                | none => rfl
                | some original =>
                    simp only [foundSource, bind]
                    cases original.progress <;> rfl

theorem renewReceivingDestination_open (state : ConstructionState) (incoming current : DestinationId)
    (destination : PendingDestination) (count : Nat)
    (resolved : destinationCurrent state incoming = .ok current)
    (present : state.destinations[current]? = some destination)
    (opened : destination.progress = .open count) :
    renewReceivingDestination incoming state = .ok current state := by
  simp only [renewReceivingDestination, ConstructionM.get, bind, resolved, pure,
    lookupDestination_result, present, opened]

def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem repeatElement_sourceFrame (fuel : Nat) (layout : LayoutEnv) (incoming parentId sourceId : DestinationId)
    (element : Construct.Ty) (origin : OriginId) (state : ExecutionState)
    (parent source : PendingDestination) (storage : ReceivingStorage) (parentCount sourceCount : Nat)
    (resolved : destinationCurrent state.construction incoming = .ok parentId)
    (parentFound : state.construction.destinations[parentId]? = some parent)
    (parentOpen : parent.progress = .open parentCount)
    (sourceFound : state.construction.destinations[sourceId]? = some source)
    (sourceBuilt : source.progress = .built sourceCount)
    (sourceStorage : state.construction.storage[source.storage]? = some storage)
    (separate : source.storage ≠ parent.storage) :
    ((stepState (repeatElement fuel layout incoming element sourceId origin state)).construction.destinations[sourceId]?,
      (stepState (repeatElement fuel layout incoming element sourceId origin state)).construction.storage[source.storage]?) =
        (some source, some storage) := by
  have distinct : sourceId ≠ parentId := by
    intro same
    have row : source = parent := Option.some.inj ((same ▸ sourceFound).symm.trans parentFound)
    exact separate (congrArg PendingDestination.storage row)
  cases fuel with
  | zero => simp only [repeatElement, Construct.timeout, EvalM.stop, stepState, sourceFound, sourceStorage]
  | succ fuel =>
      have renewed := renewReceivingDestination_open state.construction incoming parentId parent parentCount
        resolved parentFound parentOpen
      simp only [repeatElement, liftConstruction, renewed, bind, storedDestination,
        getDestination, EvalM.get, sourceFound, pure, sourceBuilt, progressCount, getStorage, sourceStorage]
      cases measured : packedEnd fuel layout element storage.bytes source.capability.start with
      | error reason =>
          cases reason <;> simp only [liftLayout, measured, Construct.fault, Construct.timeout, EvalM.stop, bind, stepState]
          all_goals simp only [sourceFound, sourceStorage]
      | ok finish =>
          simp only [liftLayout, measured, pure, bind]
          have copiedFrame := recordCopy_sourceFrame (.repeat sourceId) parentId state.construction
          cases copied : recordCopy (.repeat sourceId) parentId state.construction with
          | fault reason after =>
              simp only [copied, ConstructionResult.finalState] at copiedFrame
              simp only [copied, bind, stepState]
              exact (congrArg (fun pair => (pair.1[sourceId]?, pair.2[source.storage]?)) copiedFrame).trans
                (by rw [sourceFound, sourceStorage])
          | ok value after =>
              simp only [copied, ConstructionResult.finalState] at copiedFrame
              have rows : after.destinations = state.construction.destinations := congrArg Prod.fst copiedFrame
              have storages : after.storage = state.construction.storage := congrArg Prod.snd copiedFrame
              have parentAfter : after.destinations[parentId]? = some parent := rows ▸ parentFound
              have writeFrame := writeElement_sourceFrame parentId
                (storage.bytes.extract source.capability.start finish) after source.storage sourceId parent
                parentAfter separate distinct
              rw [rows, storages, sourceFound, sourceStorage] at writeFrame
              simp only [copied, bind]
              cases written : writeElement parentId (storage.bytes.extract source.capability.start finish) after <;>
                simpa only [written, ConstructionResult.finalState, stepState] using writeFrame

theorem repeatElement_readsSnapshot (fuel : Nat) (layout : LayoutEnv) (incoming parentId sourceId : DestinationId)
    (element : Construct.Ty) (origin : OriginId) (state : ExecutionState)
    (parent source : PendingDestination) (storage : ReceivingStorage) (parentCount sourceCount : Nat)
    (resolved : destinationCurrent state.construction incoming = .ok parentId)
    (parentFound : state.construction.destinations[parentId]? = some parent)
    (parentOpen : parent.progress = .open parentCount)
    (sourceFound : state.construction.destinations[sourceId]? = some source)
    (sourceBuilt : source.progress = .built sourceCount)
    (sourceStorage : state.construction.storage[source.storage]? = some storage) :
    repeatElement (fuel + 1) layout incoming element sourceId origin state = (do
      let finish ← liftLayout (packedEnd fuel layout element storage.bytes source.capability.start)
      liftConstruction origin (recordCopy (.repeat sourceId) parentId)
      liftConstruction origin (writeElement parentId (storage.bytes.extract source.capability.start finish))) state := by
  have renewed := renewReceivingDestination_open state.construction incoming parentId parent parentCount
    resolved parentFound parentOpen
  simp only [repeatElement, liftConstruction, renewed, bind, storedDestination,
    getDestination, EvalM.get, sourceFound, pure, sourceBuilt, progressCount, getStorage, sourceStorage]

set_option maxHeartbeats 800000 in
theorem retireRepeatedSource_consumes (state after : ConstructionState) (parentId sourceId : DestinationId)
    (parent source : PendingDestination) (storageId : StorageId) (parentCount sourceCount : Nat)
    (parentFound : state.destinations[parentId]? = some parent)
    (sourceFound : state.destinations[sourceId]? = some source)
    (parentOpen : parent.progress = .open parentCount)
    (sourceBuilt : source.progress = .built sourceCount)
    (sourceUse : source.use = .receiver) (sourceBacking : source.backing = .direct storageId)
    (executed : retireRepeatedSource parentId sourceId state = .ok () after) :
    parentId ≠ sourceId ∧ parent.storage ≠ storageId ∧
      after = { state with
        storage := state.storage.set! storageId ⟨ByteArray.empty, 0⟩
        destinations := state.destinations.set! sourceId { source with progress := .retired } } := by
  have sourceInside := (Array.getElem?_eq_some_iff.mp sourceFound).choose
  simp only [retireRepeatedSource, writableDestination_result, parentFound, bind] at executed
  cases parentAllowed : destinationCanWrite state parentId <;> simp only [parentAllowed, bind] at executed
  · contradiction
  · simp only [writableDestination_result, sourceFound, bind] at executed
    cases sourceAllowed : destinationCanWrite state sourceId <;> simp only [sourceAllowed, bind] at executed
    · contradiction
    · simp only [parentOpen, sourceBuilt, sourceUse, sourceBacking, bind] at executed
      split at executed
      · contradiction
      · rename_i separate
        have distinct : parentId ≠ sourceId := by
          intro same
          simp [same] at separate
        have different : parent.storage ≠ storageId := by
          intro same
          simp [same] at separate
        refine ⟨distinct, different, ?_⟩
        cases stored : state.storage[storageId]? with
        | none => simp only [lookupStorage_result, stored, bind] at executed; contradiction
        | some storage =>
            have inside := (Array.getElem?_eq_some_iff.mp stored).choose
            simp only [lookupStorage_result, stored, bind] at executed
            repeat' first
              | split at executed
              | contradiction
              | simp_all only [ConstructionM.get, ConstructionM.set, bind, pure, ConstructionM.fail,
                  replaceStorage_result, replaceDestination_result, sourceInside, inside,
                  ↓reduceIte, ConstructionResult.ok.injEq, true_and]

private def fixtureModule : Construct.Module := ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩
private def fixtureConfig : EvalConfig := ⟨.release, fixtureModule⟩
private def fixtureEnvironment : RuntimeActivation := ⟨0, 0, #[], [], []⟩

private def repetitionFixture (aliasStorage retire : Bool) : EvalM (DestinationId × DestinationId) := do
  let parent ← newDestination fixtureConfig.layout 0 (.arr (.varr (.int .u8)) 2) .value 0
  let source ← newDestination fixtureConfig.layout 0 (.varr (.int .u8)) .value 0
  buildExpr 10 fixtureConfig fixtureEnvironment source (.bytes (.varr (.int .u8)) [65] 0)
  if aliasStorage then
    let state ← EvalM.get
    let parentRow ← getDestination parent
    let sourceRow ← getDestination source
    EvalM.set { state with construction := { state.construction with
      destinations := state.construction.destinations.set! parent
        { parentRow with backing := .direct sourceRow.storage, writeEnd := 1 } } }
  repeatElement 10 fixtureConfig.layout parent (.varr (.int .u8)) source 0
  if retire then receivingAction 0 parent (fun parent => retireRepeatedSource parent source)
  pure (parent, source)

private def fixtureBytes (aliasStorage retire : Bool) : Option (List UInt8 × List UInt8) := do
  let .ok (parent, source) after := repetitionFixture aliasStorage retire .initial | none
  let parent ← after.construction.destinations[parent]?
  let source ← after.construction.destinations[source]?
  let receiver ← after.construction.storage[parent.storage]?
  let copied ← after.construction.storage[source.storage]?
  pure (receiver.bytes.data.toList, copied.bytes.data.toList)

#guard fixtureBytes false false == some ([1, 0, 0, 0, 65], [1, 0, 0, 0, 65])
#guard fixtureBytes false true == some ([1, 0, 0, 0, 65], [])
#guard fixtureBytes true false == some ([1, 1, 0, 0, 0, 65], [1, 1, 0, 0, 0, 65])

#print axioms writeElement_sourceFrame
#print axioms recordCopy_sourceFrame
#print axioms repeatElement_sourceFrame
#print axioms repeatElement_readsSnapshot
#print axioms retireRepeatedSource_consumes

end Goose.Proofs.ConstructionRepeatedSourceSnapshot
