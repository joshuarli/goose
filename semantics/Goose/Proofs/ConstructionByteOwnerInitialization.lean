import Goose.Proofs.ConstructionRootedBackingAllocation
import Goose.Proofs.ConstructionFixedElementGeometry

set_option Elab.async false

namespace Goose.Proofs.ConstructionRepresentation
open Goose.Construct

private def byteOwnerType : Ty := .grow (.int .u8)

private def byteOwnerState (raw : ByteArray) (phase : DestinationProgress)
    (published : Nat) (total : Nat) (events : List Goose.Core.ConstructionEvent) : ConstructionState :=
  { ConstructionState.initial with
    storage := #[⟨raw, published⟩]
    destinations := #[⟨⟨0, ⟨.local 0 0 0, []⟩, byteOwnerType, byteOwnerType, .value, 0, 0⟩,
      .direct 0, .elements, .receiver, phase, raw.size, 0, some total, none⟩]
    events := events }

private def byteOwnerRuntime (construction : ConstructionState) : ExecutionState :=
  { ExecutionState.initial with nextAct := 1, construction := construction }

def byteOwnerModule (data : List UInt8) : Module :=
  ⟨#["byte-owner.goose"], #[],
    #[⟨"bytes", byteOwnerType, .immutable, .bytes byteOwnerType data 0, 0⟩],
    #[⟨"entry", #[], #[], #[], .mk 0 [] none, .unknown⟩],
    #[⟨0, "entry", [], [], []⟩], 0, #[⟨0, 17, "global"⟩], #[], #[]⟩

theorem byteOwnerModule_accepted (data : List UInt8) : validate (byteOwnerModule data) = .ok () := by
  cbv

private theorem byteOwner_renew (raw : ByteArray) (total : Nat)
    (events : List Goose.Core.ConstructionEvent) :
    renewReceivingDestination 0 (byteOwnerState raw (.open raw.size) 0 total events) =
      .ok 0 (byteOwnerState raw (.open raw.size) 0 total events) := by
  cbv

private theorem byteOwner_write (raw : ByteArray) (byte : UInt8) (total : Nat)
    (events : List Goose.Core.ConstructionEvent) :
    writeElement 0 ⟨#[byte]⟩ (byteOwnerState raw (.open raw.size) 0 total events) =
      .ok () (byteOwnerState (raw ++ ⟨#[byte]⟩) (.open (raw.size + 1)) 0 total
        (events ++ [.write 0 raw.size])) := by
  have available : destinationCanWrite (byteOwnerState raw (.open raw.size) 0 total events) 0 = true := by
    cbv
  simp only [writeElement, writableDestination_result, bind, available]
  simp [byteOwnerState, writingAvailable_result, lookupStorage_result, replaceStorage_result,
    replaceDestination_result, emit_result, bind, pure, PendingDestination.storage,
    DestinationBacking.writeStorage]
  change raw.extract 0 raw.size ++ ⟨#[byte]⟩ ++ raw.extract (raw.size + 1) raw.size = raw ++ ⟨#[byte]⟩
  simp

private theorem byteOwner_runtimeWrite (raw : ByteArray) (byte : UInt8) (total : Nat)
    (events : List Goose.Core.ConstructionEvent) :
    receivingAction 0 0 (fun destination => writeElement destination ⟨#[byte]⟩)
        (byteOwnerRuntime (byteOwnerState raw (.open raw.size) 0 total events)) =
      .ok () (byteOwnerRuntime (byteOwnerState (raw ++ ⟨#[byte]⟩) (.open (raw.size + 1)) 0 total
        (events ++ [.write 0 raw.size]))) := by
  simp only [receivingAction, liftConstruction, byteOwnerRuntime, byteOwner_renew, bind, byteOwner_write]

private theorem byteOwner_writeLoop (data : List UInt8) (raw : ByteArray) (total : Nat)
    (events : List Goose.Core.ConstructionEvent) :
    ∃ following,
      ((forIn data PUnit.unit fun byte _ => do
          receivingAction 0 0 (fun destination => writeElement destination ⟨#[byte]⟩)
          pure (.yield PUnit.unit)) : EvalM PUnit)
        (byteOwnerRuntime (byteOwnerState raw (.open raw.size) 0 total events)) =
      .ok PUnit.unit (byteOwnerRuntime (byteOwnerState (raw ++ ⟨data.toArray⟩) (.open (raw ++ ⟨data.toArray⟩).size)
        0 total following)) := by
  induction data generalizing raw events with
  | nil =>
      refine ⟨events, ?_⟩
      have empty : (⟨(#[] : Array UInt8)⟩ : ByteArray) = ByteArray.empty := rfl
      simp only [List.forIn_nil, pure, bind, empty, ByteArray.append_empty]
  | cons byte rest ih =>
      obtain ⟨following, tail⟩ := ih (raw ++ ⟨#[byte]⟩) (events ++ [.write 0 raw.size])
      refine ⟨following, ?_⟩
      have combined : (raw ++ ⟨#[byte]⟩) ++ ⟨rest.toArray⟩ = raw ++ ⟨(byte :: rest).toArray⟩ := by
        rw [ByteArray.ext_iff]
        simp only [ByteArray.data_append]
        change (raw.data ++ #[byte]) ++ rest.toArray = raw.data ++ (byte :: rest).toArray
        rw [List.toArray_cons byte rest]
        exact Array.append_assoc
      have currentSize : (raw ++ ⟨#[byte]⟩).size = raw.size + 1 := by
        rw [ByteArray.size_append]
        rfl
      simp only [List.forIn_cons, bind, byteOwner_runtimeWrite, pure]
      simpa only [bind, pure, currentSize, combined] using tail

private theorem byteOwner_finish (raw : ByteArray) (total : Nat)
    (events : List Goose.Core.ConstructionEvent) :
    finishDestination 0 (byteOwnerState raw (.open raw.size) 0 total events) =
      .ok () (byteOwnerState raw (.built raw.size) 0 total events) := by
  have available : destinationCanWrite (byteOwnerState raw (.open raw.size) 0 total events) 0 = true := by
    cbv
  simp only [finishDestination, writableDestination_result, bind, available]
  simp [byteOwnerState, hasPrefix_result, replaceDestination_result, bind, pure]

private theorem byteOwner_publish (raw : ByteArray) (total : Nat)
    (events : List Goose.Core.ConstructionEvent) :
    publishOperation [0] (byteOwnerState raw (.built raw.size) 0 total events) =
      .ok () (byteOwnerState raw (.published raw.size) raw.size total (events ++ [.publish 0])) := by
  cbv
  simp
  cases bytes : raw.data.toList <;> simp_all

private theorem byteOwner_runtimeFinish (raw : ByteArray) (total : Nat)
    (events : List Goose.Core.ConstructionEvent) :
    receivingAction 0 0 finishDestination
        (byteOwnerRuntime (byteOwnerState raw (.open raw.size) 0 total events)) =
      .ok () (byteOwnerRuntime (byteOwnerState raw (.built raw.size) 0 total events)) := by
  simp only [receivingAction, liftConstruction, byteOwnerRuntime, byteOwner_renew, bind, byteOwner_finish]

private theorem byteOwner_build (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (data : List UInt8) :
    ∃ events, buildExpr (fuel + 1) config environment 0 (.bytes byteOwnerType data 0)
        (byteOwnerRuntime (byteOwnerState ByteArray.empty (.open 0) 0 data.length [.begin 0])) =
      .ok () (byteOwnerRuntime (byteOwnerState ⟨data.toArray⟩ (.built (⟨data.toArray⟩ : ByteArray).size)
        0 data.length events)) := by
  obtain ⟨events, loop⟩ := byteOwner_writeLoop data ByteArray.empty data.length [.begin 0]
  simp only [ByteArray.empty_append, ByteArray.size_empty, bind, pure] at loop
  refine ⟨events, ?_⟩
  simp only [buildExpr, liftConstruction, byteOwnerRuntime, byteOwner_renew, bind]
  change protectDestination 0 0
    (do
      for byte in data do receivingAction 0 0 (fun destination => writeElement destination ⟨#[byte]⟩)
      receivingAction 0 0 finishDestination)
    (byteOwnerRuntime (byteOwnerState ByteArray.empty (.open 0) 0 data.length [.begin 0])) = _
  simp only [protectDestination, bind, pure, loop, byteOwner_runtimeFinish]
  rfl

private theorem byteOwner_allocate (layout : LayoutEnv) (total : Nat) :
    newDestination layout 0 byteOwnerType .value 0 none (some total) (byteOwnerRuntime .initial) =
      .ok 0 (byteOwnerRuntime (byteOwnerState ByteArray.empty (.open 0) 0 total [.begin 0])) := by
  cbv

private theorem byteOwner_completed (raw : ByteArray) (total : Nat)
    (events : List Goose.Core.ConstructionEvent) :
    completedReceivingDestination 0
      (byteOwnerRuntime (byteOwnerState raw (.built raw.size) 0 total events)) =
    .ok 0 (byteOwnerRuntime (byteOwnerState raw (.built raw.size) 0 total events)) := by
  cbv

private theorem byteOwner_runtimePublish (raw : ByteArray) (total : Nat)
    (events : List Goose.Core.ConstructionEvent) :
    publishCarriers 0 [.completed 0]
      (byteOwnerRuntime (byteOwnerState raw (.built raw.size) 0 total events)) =
    .ok () (byteOwnerRuntime (byteOwnerState raw (.published raw.size) raw.size total (events ++ [.publish 0]))) := by
  simp only [publishCarriers, List.mapM_cons, List.mapM_nil, bind, pure, liftConstruction,
    List.filterMap_cons, List.filterMap_nil, id, byteOwnerRuntime, byteOwner_publish]

private theorem byteOwner_construct (fuel : Nat) (data : List UInt8) (profile : Goose.Core.NumProfile) :
    ∃ events, constructLocal ⟨byteOwnerModule data, #[]⟩ 0 byteOwnerType 0 (.bytes byteOwnerType data 0)
      (fun destination => buildExpr (fuel + 1) ⟨profile, byteOwnerModule data⟩ ⟨0, 0, #[], [], []⟩ destination
        (.bytes byteOwnerType data 0)) (byteOwnerRuntime .initial) =
    .ok (.completed 0) (byteOwnerRuntime (byteOwnerState ⟨data.toArray⟩
      (.published (⟨data.toArray⟩ : ByteArray).size) (⟨data.toArray⟩ : ByteArray).size data.length events)) := by
  obtain ⟨events, built⟩ := byteOwner_build fuel ⟨profile, byteOwnerModule data⟩ ⟨0, 0, #[], [], []⟩ data
  refine ⟨events ++ [.publish 0], ?_⟩
  simp only [constructLocal, producerCount?, literalCount, byteOwner_allocate, bind,
    built, byteOwner_completed, byteOwner_runtimePublish, pure]

private def byteOwnerStored (count : Nat) : StoredValue :=
  ⟨0, 0, byteOwnerType, count, some 0, none, [], count⟩

private def byteOwnerGlobalState (raw : ByteArray) (total : Nat)
    (events : List Goose.Core.ConstructionEvent) : ExecutionState :=
  { byteOwnerRuntime (byteOwnerState raw (.published raw.size) raw.size total events) with
    objects := [(.global 0, .stored (byteOwnerStored raw.size))]
    objectOrdinals := [(.global 0, 0)] }

private theorem byteOwner_initGlobals (fuel : Nat) (data : List UInt8) (profile : Goose.Core.NumProfile) :
    ∃ events, initGlobals (fuel + 1) ⟨profile, byteOwnerModule data⟩ [0] .initial =
      .ok () (byteOwnerGlobalState ⟨data.toArray⟩ data.length events) := by
  obtain ⟨events, constructed⟩ := byteOwner_construct fuel data profile
  refine ⟨events, ?_⟩
  simp only [initGlobals, byteOwnerModule, Array.getElem?_singleton, byteOwnerType,
    Ty.nonfixed, freshAct, EvalM.get, EvalM.set, bind, pure, materializeProducer,
    ordinaryProducerCount?, producerCount?, literalCount, Option.isSome_some, ↓reduceIte]
  change ((constructLocal ⟨byteOwnerModule data, #[]⟩ 0 byteOwnerType 0 (.bytes byteOwnerType data 0)
      (fun destination => buildExpr (fuel + 1) ⟨profile, byteOwnerModule data⟩ ⟨0, 0, #[], [], []⟩ destination
        (.bytes byteOwnerType data 0)) >>= fun carrier => do
          let value ← carrierValue carrier
          bindRoot (.global 0) value
          pure ()) (byteOwnerRuntime .initial)) = _
  simp only [bind, constructed]
  simp only [carrierValue, storedDestination, getDestination, EvalM.get, bind,
    byteOwnerRuntime, byteOwnerState, Array.getElem?_singleton, progressCount, pure, bindRoot,
    ExecutionState.initial, List.lookup, Option.isNone_none, ↓reduceIte, setObjectOrdinal,
    EvalM.set, bindStaticRoot]
  rfl

private theorem byteOwner_elementsEnd (layout : LayoutEnv) (raw : ByteArray) (count start : Nat)
    (bounded : start + count ≤ raw.size) :
    elementsEnd (count + 1) layout (.int .u8) count raw start = .ok (start + count) := by
  simpa only [Nat.mul_one] using elementsEnd_fixed layout raw (.int .u8) 1 rfl count start
    (by simpa only [Nat.mul_one] using bounded)

private theorem byteOwner_storedBacking (layout : LayoutEnv) (raw : ByteArray) (total : Nat)
    (events : List Goose.Core.ConstructionEvent) :
    StoredValueBacking layout (byteOwnerGlobalState raw total events) (byteOwnerStored raw.size) := by
  refine .named 0 ⟨raw, raw.size⟩ _ raw.size rfl rfl rfl rfl rfl rfl rfl (.int .u8) rfl ?_
  refine ⟨raw.size + 1, raw.size, ?_, Nat.zero_le _, Nat.le_refl _⟩
  simpa [byteOwnerStored, storedWrittenRun, byteOwnerType, byteOwnerGlobalState,
    byteOwnerRuntime, byteOwnerState] using
    byteOwner_elementsEnd layout raw raw.size 0 (by omega)

private theorem byteOwner_rootedBacking (layout : LayoutEnv) (raw : ByteArray) (total : Nat)
    (events : List Goose.Core.ConstructionEvent) :
    RootedBackingState layout (byteOwnerGlobalState raw total events) (fun root => root = .global 0) := by
  constructor
  · intro root retained value present
    subst root
    have same : value = .stored (byteOwnerStored raw.size) := by
      simpa only [byteOwnerGlobalState, List.lookup, beq_self_eq_true, Option.some.injEq] using present.symm
    subst value
    exact .stored _ (byteOwner_storedBacking layout raw total events)
  · intro root retained stored present
    subst root
    have same : stored = byteOwnerStored raw.size := by
      simpa only [byteOwnerGlobalState, List.lookup, beq_self_eq_true, Option.some.injEq, Value.stored.injEq] using present.symm
    subst stored
    rfl

private theorem byteOwner_globalRepresentation (raw : ByteArray) (data : List UInt8)
    (events : List Goose.Core.ConstructionEvent) :
    GlobalRepresentations (byteOwnerModule data) 1 (byteOwnerGlobalState raw data.length events) := by
  refine ⟨by simp [byteOwnerModule], ?_⟩
  intro global inside
  have same : global = 0 := by omega
  subst global
  exact ⟨_, _, rfl, rfl, .stored byteOwnerType (byteOwnerStored raw.size) rfl rfl⟩

private theorem byteOwner_entry (fuel : Nat) (data : List UInt8) (profile : Goose.Core.NumProfile)
    (raw : ByteArray) (total : Nat) (events : List Goose.Core.ConstructionEvent) :
    invokeCall (fuel + 5) ⟨profile, byteOwnerModule data⟩ ⟨0, 0, #[], [], []⟩ 0 [] [] 0
        (byteOwnerGlobalState raw total events) =
      .ok [] { byteOwnerGlobalState raw total events with nextAct := 2, nextScope := 1 } := by
  cbv

private theorem byteOwner_runModule (fuel : Nat) (data : List UInt8) (profile : Goose.Core.NumProfile) :
    ∃ events, runModule (fuel + 5) ⟨profile, byteOwnerModule data⟩ .initial =
      .ok () { byteOwnerGlobalState ⟨data.toArray⟩ data.length events with nextAct := 2, nextScope := 1 } := by
  obtain ⟨events, initialized⟩ := byteOwner_initGlobals (fuel + 4) data profile
  have initialized' : initGlobals (fuel + 5) ⟨profile, byteOwnerModule data⟩ [0] .initial =
      .ok () (byteOwnerGlobalState ⟨data.toArray⟩ data.length events) := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using initialized
  refine ⟨events, ?_⟩
  simp only [runModule, byteOwnerModule, Array.size_singleton, List.range_succ, List.range_zero,
    List.nil_append, List.map_nil, List.map_cons]
  change ((initGlobals (fuel + 5) ⟨profile, byteOwnerModule data⟩ [0] >>= fun _ => do
      let (_, implementation) ← getImplementation ⟨profile, byteOwnerModule data⟩ 0
      let channels ← channelsFor (.ofModule (byteOwnerModule data)) 0 implementation.results.toList 0
      let carriers ← invokeCall (fuel + 5) ⟨profile, byteOwnerModule data⟩ ⟨0, 0, #[], [], []⟩ 0 [] channels 0
      publishCarriers 0 carriers) .initial) = _
  simp only [bind, initialized']
  simp only [getImplementation, byteOwnerModule, Array.getElem?_singleton, bind, pure,
    channelsFor, Array.toList_empty, List.mapM_nil]
  change ((invokeCall (fuel + 5) ⟨profile, byteOwnerModule data⟩ ⟨0, 0, #[], [], []⟩ 0 [] [] 0 >>=
    fun carriers => publishCarriers 0 carriers) (byteOwnerGlobalState ⟨data.toArray⟩ data.length events)) = _
  simp only [bind, byteOwner_entry]
  cbv

theorem accepted_byteOwner_execution (fuel : Nat) (data : List UInt8) (profile : Goose.Core.NumProfile) :
    validate (byteOwnerModule data) = .ok () ∧
    ∃ state, runModule (fuel + 5) ⟨profile, byteOwnerModule data⟩ .initial = .ok () state ∧
      GlobalRepresentations (byteOwnerModule data) 1 state ∧
      RootedBackingState (.ofModule (byteOwnerModule data)) state (fun root => root = .global 0) := by
  obtain ⟨events, evaluated⟩ := byteOwner_runModule fuel data profile
  have backed := byteOwner_rootedBacking (.ofModule (byteOwnerModule data)) ⟨data.toArray⟩ data.length events
  refine ⟨byteOwnerModule_accepted data, _, evaluated,
    byteOwner_globalRepresentation ⟨data.toArray⟩ data events, ?_⟩
  constructor
  · intro root retained value present
    exact ValueStorageBacked.construction_frame
      (before := byteOwnerGlobalState ⟨data.toArray⟩ data.length events) rfl
      (backed.values root retained value present)
  · exact backed.identities

theorem accepted_byteOwner_initialization (fuel : Nat) (data : List UInt8) (profile : Goose.Core.NumProfile) :
    validate (byteOwnerModule data) = .ok () ∧
    ∃ state, initGlobals (fuel + 1) ⟨profile, byteOwnerModule data⟩ [0] .initial = .ok () state ∧
      GlobalRepresentations (byteOwnerModule data) 1 state ∧
      RootedBackingState (.ofModule (byteOwnerModule data)) state (fun root => root = .global 0) := by
  obtain ⟨events, initialized⟩ := byteOwner_initGlobals fuel data profile
  exact ⟨byteOwnerModule_accepted data, _, initialized,
    byteOwner_globalRepresentation ⟨data.toArray⟩ data events,
    byteOwner_rootedBacking _ ⟨data.toArray⟩ data.length events⟩

theorem accepted_byteOwner_allocation (fuel : Nat) (data : List UInt8) (profile : Goose.Core.NumProfile)
    (owner : Goose.Core.ActId) (ty : Ty) (request : Goose.Core.ConstructionRequest)
    (origin : Goose.Core.OriginId) (knownCount : Option Nat) :
    validate (byteOwnerModule data) = .ok () ∧
    ∃ state, initGlobals (fuel + 1) ⟨profile, byteOwnerModule data⟩ [0] .initial = .ok () state ∧
      RootedBackingState (.ofModule (byteOwnerModule data))
        (Goose.Proofs.Exit.stepState
          (newDestination (.ofModule (byteOwnerModule data)) owner ty request origin none knownCount state))
        (fun root => root = .global 0) ∧
      ∀ id after, newDestination (.ofModule (byteOwnerModule data)) owner ty request origin none knownCount state =
        .ok id after → ∃ destination, after.construction.destinations[id]? = some destination ∧
          0 ≠ destination.storage ∧ 0 ≠ destination.backing.receiverStorage := by
  obtain ⟨events, initialized⟩ := byteOwner_initGlobals fuel data profile
  refine ⟨byteOwnerModule_accepted data, _, initialized,
    (byteOwner_rootedBacking _ ⟨data.toArray⟩ data.length events).newDestination_frame
      _ owner ty request origin knownCount _ _, ?_⟩
  intro id after evaluated
  exact newDestination_existing_storage_separate _ owner ty request origin knownCount _ after id 0
    ⟨⟨data.toArray⟩, (⟨data.toArray⟩ : ByteArray).size⟩ rfl evaluated

#print axioms byteOwnerModule_accepted
#print axioms accepted_byteOwner_initialization
#print axioms accepted_byteOwner_allocation
#print axioms accepted_byteOwner_execution

end Goose.Proofs.ConstructionRepresentation
