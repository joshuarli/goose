import Goose.Proofs.ExitExecutionCompletedLanding

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionProtocol

theorem storedValueBacking_named_metadata (layout : LayoutEnv) (before : ExecutionState)
    (id count : Nat) (replacement : PendingDestination) (stored : StoredValue)
    (backed : StoredValueBacking layout before stored) (named : stored.destination = some id)
    (present : before.construction.destinations[id]? = some replacement)
    (built : replacement.progress = .built count) :
    stored.storage = replacement.storage ∧ stored.start = replacement.capability.start ∧
      stored.ty = replacement.capability.logicalType := by
  cases backed with
  | detached original element originalFound detached type interval => rw [detached] at named; cases named
  | named originalId originalStorage destination sourceCount originalFound originalNamed originalBinding rawBacking rawType rawStart rawProgress element elementType interval =>
    have sameId := Option.some.inj (originalNamed.symm.trans named)
    subst originalId
    have sameRow := Option.some.inj (originalBinding.symm.trans present)
    subst destination
    exact ⟨by simpa only [built] using rawBacking, rawStart, rawType⟩

theorem completedLandingState_named_backing (layout : LayoutEnv) (before : ExecutionState)
    (id old count : Nat) (replacement superseded : PendingDestination) (storage : ReceivingStorage)
    (parentUpdate : Option (Goose.Core.DestinationId × PendingDestination)) (stored : StoredValue)
    (backed : StoredValueBacking layout before stored) (named : stored.destination = some id)
    (present : before.construction.destinations[id]? = some replacement)
    (storedLookup : before.construction.storage[replacement.storage]? = some storage)
    (built : replacement.progress = .built count)
    (ordered : superseded.capability.start ≤ replacement.capability.start)
    (parentDifferent : ∀ parentId parent, parentUpdate = some (parentId, parent) → parentId ≠ id) :
    StoredValueBacking layout
      { before with construction := completedLandingState before.construction id old count replacement superseded storage parentUpdate }
      { stored with start := superseded.capability.start } := by
  cases backed with
  | detached original element originalFound detached type interval =>
      rw [detached] at named
      cases named
  | named originalId originalStorage destination sourceCount originalFound originalNamed originalBinding rawBacking rawType rawStart rawProgress element elementType interval =>
    have sameId := Option.some.inj (originalNamed.symm.trans named)
    subst originalId
    have sameRow := Option.some.inj (originalBinding.symm.trans present)
    subst destination
    have sourceStorage : stored.storage = replacement.storage := by simpa only [built] using rawBacking
    have sameStorage : originalStorage = storage := Option.some.inj
      (originalFound.symm.trans (by simpa only [sourceStorage] using storedLookup))
    subst originalStorage
    have countSame : count = sourceCount := by
      simpa only [built, progressCount, Option.some.injEq] using rawProgress
    subst sourceCount
    simp only [built] at interval
    let header := if replacement.layout == .packed && replacement.capability.request == .value then 4 else 0
    let runCount := (storedWrittenRun stored ⟨stored.start + header, count, element⟩).count
    change SampledRunBacking layout storage.bytes ⟨stored.start + header, runCount, element⟩ at interval
    obtain ⟨fuel, finish, measured, lower, upper⟩ := interval.interval
    have sourceLower : replacement.capability.start ≤ finish := by
      simp only at lower
      omega
    let endOffset := finish - replacement.capability.start
    have endEq : replacement.capability.start + endOffset = finish := by dsimp only [endOffset]; omega
    have relocation := landingBytes_relocated storage.bytes superseded.capability.start replacement.capability.start ordered (by omega)
    have nativeMeasured : elementsEnd fuel layout element runCount storage.bytes
        (replacement.capability.start + header) = .ok (replacement.capability.start + endOffset) := by
      rw [endEq]
      simpa only [rawStart] using measured
    have endInside : endOffset ≤ storage.bytes.size - replacement.capability.start := by dsimp only [endOffset]; omega
    have translated := relocation.elementsEnd fuel layout element runCount header endOffset nativeMeasured endInside
    let landed := landedReplacementRow replacement superseded count
    let landedStorage := storage.landExit superseded.capability.start replacement.capability.start
    apply StoredValueBacking.named (element := element) id landedStorage landed count
    · change (completedLandingState before.construction id old count replacement superseded storage parentUpdate).storage[stored.storage]? = some landedStorage
      rw [completedLandingState_storage, sourceStorage]
      have bound := (Array.getElem?_eq_some_iff.mp storedLookup).1
      simp only [Array.set!, Array.getElem?_setIfInBounds_self_of_lt bound]
      rfl
    · exact named
    · exact completedLandingState_replacement before.construction id old count replacement superseded storage parentUpdate
        (Array.getElem?_eq_some_iff.mp present).1 parentDifferent
    · exact sourceStorage
    · exact rawType
    · rfl
    · rfl
    · exact elementType
    · change SampledRunBacking layout landedStorage.bytes ⟨superseded.capability.start + header, runCount, element⟩
      refine ⟨fuel, superseded.capability.start + endOffset, translated, ?_, ?_⟩
      · simp only at lower ⊢
        dsimp only [endOffset]
        omega
      · have receivingBound := relocation.receivingBound
        change superseded.capability.start + endOffset ≤ (landingBytes storage.bytes superseded.capability.start replacement.capability.start).size
        omega

theorem storedValueBacking_named_start_bound (layout : LayoutEnv) (before : ExecutionState)
    (id count : Nat) (replacement : PendingDestination) (storage : ReceivingStorage) (stored : StoredValue)
    (backed : StoredValueBacking layout before stored) (named : stored.destination = some id)
    (present : before.construction.destinations[id]? = some replacement)
    (storedLookup : before.construction.storage[replacement.storage]? = some storage)
    (built : replacement.progress = .built count) : replacement.capability.start ≤ storage.bytes.size := by
  obtain ⟨storageEq, startEq, typeEq⟩ := storedValueBacking_named_metadata layout before id count replacement stored backed named present built
  obtain ⟨original, run, originalFound, sampled, interval⟩ := backed.sampled layout before stored
  have same := Option.some.inj (originalFound.symm.trans (by simpa only [storageEq] using storedLookup))
  subst original
  have sourceLower := (sampledStored_start_transport stored stored.start before before storage storage run
    originalFound originalFound rfl (fun _ _ => rfl) sampled).1
  obtain ⟨fuel, finish, measured, lower, upper⟩ := interval.interval
  simp only [storedWrittenRun] at lower
  omega

theorem completedStep_named_backing (layout : LayoutEnv) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (id old count : Nat)
    (replacement superseded : PendingDestination) (storage : ReceivingStorage)
    (parentUpdate : Option (Goose.Core.DestinationId × PendingDestination)) (stored : StoredValue)
    (indexed : DestinationCapabilitiesIndexed before.construction)
    (backed : StoredValueBacking layout before stored) (named : stored.destination = some id)
    (present : before.construction.destinations[id]? = some replacement)
    (storedLookup : before.construction.storage[replacement.storage]? = some storage)
    (built : replacement.progress = .built count)
    (sameStorage : superseded.storage = replacement.storage)
    (ordered : superseded.capability.start ≤ replacement.capability.start)
    (parentBound : ∀ parentId parent, parentUpdate = some (parentId, parent) → parentId < before.construction.destinations.size)
    (parentDifferent : ∀ parentId parent, parentUpdate = some (parentId, parent) → parentId ≠ id) :
    liftConstruction origin (Goose.Proofs.ConstructionExecutionProtocol.completedStep
      id old count replacement superseded parentUpdate) before = .ok ()
        { before with construction := completedLandingState before.construction id old count replacement superseded storage parentUpdate } ∧
      stored.storage = superseded.storage ∧
      StoredValueBacking layout
        { before with construction := completedLandingState before.construction id old count replacement superseded storage parentUpdate }
        { stored with start := superseded.capability.start } := by
  have storageEq := (storedValueBacking_named_metadata layout before id count replacement stored backed named present built).1
  have inside := storedValueBacking_named_start_bound layout before id count replacement storage stored backed named present storedLookup built
  refine ⟨?_, storageEq.trans sameStorage.symm,
    completedLandingState_named_backing layout before id old count replacement superseded storage
      parentUpdate stored backed named present storedLookup built ordered parentDifferent⟩
  have success := completedStep_success before.construction id old count replacement superseded storage parentUpdate
    indexed present storedLookup ordered inside parentBound
  simp only [liftConstruction, success]

#print axioms storedValueBacking_named_metadata
#print axioms completedLandingState_named_backing
#print axioms storedValueBacking_named_start_bound
#print axioms completedStep_named_backing

end Goose.Proofs.ExitExecution
