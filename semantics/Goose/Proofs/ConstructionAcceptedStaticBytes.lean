import Goose.Proofs.ConstructionAcceptedBindings
import Goose.Proofs.ConstructionAcceptedFreshness
import Goose.Proofs.ConstructionAcceptedValues

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ExitExecution

theorem evalValue_staticBytes_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (interpretation : RootInterpretation)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (liveRoots : RootInst → Prop) (bytes : List UInt8) (origin : Nat)
    {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (world : AcceptedWorld config initialized state ambient types liveRoots regions pending)
    (globalCount : interpretation.globalCount = config.module.globals.size) :
    ∃ after nextTypes root,
      evalValue (fuel + 1) config environment (.bytes (.slice .readOnly (.int .u8)) bytes origin) state =
        .ok (.slice ⟨root, []⟩ 0 bytes.length) after ∧
      RootTypesExtend types nextTypes ∧
      AcceptedWorld config initialized after ambient nextTypes (fun other => other = root ∨ liveRoots other) regions pending ∧
      AcceptedValue config.layout nextTypes interpretation after (.slice .readOnly (.int .u8)) [.static]
        (.slice ⟨root, []⟩ 0 bytes.length) := by
  let root := RootInst.global (config.module.globals.size + state.nextScope)
  let values := (bytes.map (fun byte => Value.int .u8 byte.toNat)).toArray
  let ownerTy := Ty.arr (.int .u8) bytes.length
  let scopeState := { state with nextScope := state.nextScope + 1 }
  let after := { scopeState with objects := (root, .fixed values) :: scopeState.objects.filter (fun entry => entry.1 != root) }
  have noType : types root = none := by
    cases present : types root with
    | none => rfl
    | some ty =>
      have bounded := world.syntheticFrontier (config.module.globals.size + state.nextScope) ty present (by omega)
      exact (Nat.lt_irrefl _ bounded).elim
  have compatible : RootTypeCompatible types root ownerTy := by
    intro previous present
    rw [noType] at present
    cases present
  have represented : ValueRepresentation ownerTy (.fixed values) := by
    refine .array (.int .u8) bytes.length values rfl (by simp [values]) ?_
    intro value present
    simp only [values, List.toList_toArray, List.mem_map] at present
    obtain ⟨byte, _, rfl⟩ := present
    exact .integer .u8 byte.toNat
  have pointers : PointerTypedValue types ownerTy (.fixed values) := by
    apply PointerTypedValue.array
    intro value present
    simp only [values, List.toList_toArray, List.mem_map] at present
    obtain ⟨byte, _, rfl⟩ := present
    exact .integer .u8 byte.toNat
  have valueBacking : ValueStorageBacked config.layout after (.fixed values) := by
    apply ValueStorageBacked.array
    intro value present
    simp only [values, List.toList_toArray, List.mem_map] at present
    obtain ⟨byte, _, rfl⟩ := present
    exact .integer .u8 byte.toNat
  have scopeWorld := (freshScope_acceptedWorld config initialized state ambient types liveRoots world).2
  obtain ⟨typedAfter, typedResult, extended, heap⟩ := bindRoot_registeredHeap types scopeState root ownerTy
    (.fixed values) compatible scopeWorld.heap represented pointers
  obtain ⟨boundAfter, boundResult, objects⟩ := bindRoot_objects root (.fixed values) scopeState
  have same := (ExecutionStep.ok.inj (typedResult.symm.trans boundResult)).2
  subst boundAfter
  have typedObjects : typedAfter.objects = after.objects := objects
  have noStored : ∀ stored, ¬ StoredOccurrence (.fixed values) stored := by
    intro stored occurrence
    cases occurrence with
    | array _ value stored member child =>
      simp only [values, List.mem_map] at member
      obtain ⟨byte, _, rfl⟩ := member
      cases child
  have afterBacking : RootedBackingState config.layout after (fun other => other = root ∨ liveRoots other) := by
    constructor
    · intro other retained value present
      by_cases same : other = root
      · subst other
        have equal : Value.fixed values = value := by simpa only [after, List.lookup, beq_self_eq_true, Option.some.injEq] using present
        subst value
        exact valueBacking
      · have old : state.objects.lookup other = some value := by
          rw [← typedObjects, bindRoot_lookup_other root other (.fixed values) scopeState typedAfter typedResult same] at present
          exact present
        exact ValueStorageBacked.construction_frame (before := state) (after := after) rfl
          (world.backing.values other (retained.resolve_left same) value old)
    · intro other retained stored present
      by_cases same : other = root
      · subst other
        have impossible : Value.fixed values = Value.stored stored := by
          simpa only [after, List.lookup, beq_self_eq_true, Option.some.injEq] using present
        cases impossible
      · have old : state.objects.lookup other = some (.stored stored) := by
          rw [← typedObjects, bindRoot_lookup_other root other (.fixed values) scopeState typedAfter typedResult same] at present
          exact present
        exact world.backing.identities other (retained.resolve_left same) stored old
  refine ⟨after, registerRootType types root ownerTy, root, ?_, extended, ?_, ?_⟩
  · simp only [evalValue, freshScope, bindStaticRoot, EvalM.get, EvalM.set, bind, pure, root, after, scopeState, values]
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact ⟨scopeWorld.ownership.source, scopeWorld.ownership.retention,
        ⟨scopeWorld.ownership.runtime.activations, scopeWorld.ownership.runtime.breaks⟩,
        scopeWorld.ownership.reservations, scopeWorld.ownership.receiving, scopeWorld.ownership.bounds,
        ⟨scopeWorld.ownership.identities.activations, scopeWorld.ownership.identities.breaks⟩⟩
    · refine ⟨world.globals.1, ?_⟩
      intro id available
      obtain ⟨descriptor, value, declared, found, represented⟩ := world.globals.2 id available
      have different : RootInst.global id ≠ root := by
        dsimp only [root]
        intro same
        have equal : id = config.module.globals.size + state.nextScope := RootInst.global.inj same
        have initializedBound := world.globals.1
        omega
      refine ⟨descriptor, value, declared, ?_, represented⟩
      rw [← typedObjects, bindRoot_lookup_other root (.global id) (.fixed values) scopeState typedAfter typedResult different]
      exact found
    · intro id descriptor declared
      exact extended _ _ (world.globalTypes id descriptor declared)
    · exact registerRootType_layouts config.layout types root ownerTy world.layouts (by trivial)
    · exact registerRootType_frontier types scopeState root ownerTy scopeWorld.typeFrontier
        (by intro act scope id impossible; dsimp only [root] at impossible; cases impossible)
    · apply registerRootType_synthetic_frontier config types scopeState root ownerTy scopeWorld.syntheticFrontier
      intro id equal outside
      dsimp only [root] at equal
      cases equal
      change config.module.globals.size + state.nextScope < config.module.globals.size + (state.nextScope + 1)
      omega
    · intro other ty value declared present
      rw [← typedObjects] at present
      exact heap other ty value declared present
    · intro other value present
      by_cases same : other = root
      · subst other
        exact ⟨ownerTy, by simp only [registerRootType, ↓reduceIte]⟩
      · rw [← typedObjects, bindRoot_lookup_other root other (.fixed values) scopeState typedAfter typedResult same] at present
        obtain ⟨ty, declared⟩ := world.objectsRegistered other value present
        exact ⟨ty, extended other ty declared⟩
    · intro other ordinal present
      obtain ⟨ty, declared⟩ := world.ordinalsRegistered other ordinal present
      exact ⟨ty, extended other ty declared⟩
    · exact afterBacking
    · intro region member
      have valid := world.protections region member
      refine ⟨valid.present, ⟨⟨?_, ?_⟩, ?_⟩, valid.cutoff, valid.landing, valid.authority, ?_⟩
      · intro other retained value present
        exact afterBacking.values other retained.1 value present
      · intro other retained stored present
        exact afterBacking.identities other retained.1 stored present
      · intro other retained value present stored occurrence
        by_cases same : other = root
        · subst other
          have equal : Value.fixed values = value := by simpa only [after, List.lookup, beq_self_eq_true, Option.some.injEq] using present
          subst value
          exact (noStored stored occurrence).elim
        · have old : state.objects.lookup other = some value := by
            rw [← typedObjects, bindRoot_lookup_other root other (.fixed values) scopeState typedAfter typedResult same] at present
            exact present
          obtain ⟨storage, run, fuel, finish, found, sampled, measured, lower, upper⟩ :=
            (valid.observations.observations other ⟨retained.1.resolve_left same, retained.2⟩ value old stored occurrence).observed
          refine ⟨storage, run, fuel, finish, found, ?_, measured, lower, upper⟩
          exact sampledStored_storage_transport stored state after storage storage run found found rfl
            (by intro id named; rfl) sampled
      · intro other retained outside value present stored occurrence id named
        by_cases same : other = root
        · subst other
          have equal : Value.fixed values = value := by simpa only [after, List.lookup, beq_self_eq_true, Option.some.injEq] using present
          subst value
          exact (noStored stored occurrence).elim
        · have old : state.objects.lookup other = some value := by
            rw [← typedObjects, bindRoot_lookup_other root other (.fixed values) scopeState typedAfter typedResult same] at present
            exact present
          exact valid.names other (retained.resolve_left same) outside value old stored occurrence id named
    · intro frame member
      obtain ⟨ready, backing⟩ := world.carriers frame member
      exact ⟨⟨ready.lengths, fun channel carrier pair =>
        carrierReady_construction_frame state after rfl channel carrier (ready.pairs channel carrier pair)⟩,
        fun carrier present => carrierBacking_construction_frame config.layout state after rfl carrier (backing carrier present)⟩
    · intro id available
      exact Or.inr (world.globalLive id available)
  · refine ⟨.slice .readOnly (.int .u8) ⟨root, []⟩ 0 bytes.length,
      .slice .readOnly (.int .u8) ownerTy ⟨root, []⟩ 0 bytes.length ?_ rfl, .slice _ _ _, ?_⟩
    · exact ⟨ownerTy, by simp only [registerRootType, ↓reduceIte], .root ownerTy⟩
    · intro location reference
      cases reference
      exact ⟨.static, List.mem_cons_self, .static _ (by rw [globalCount]; omega)⟩

theorem evalValue_checkedStaticBytes_world (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (liveRoots : RootInst → Prop) (bytes : List UInt8) (origin : Nat) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (world : AcceptedWorld config frame.initialized state ambient types liveRoots regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (checked : CheckedValue frame (.bytes (.slice .readOnly (.int .u8)) bytes origin) ty roots typingAfter rootsAfter) :
    ∃ after nextTypes root,
      evalValue (fuel + 1) config frame.interpretation.environment
        (.bytes (.slice .readOnly (.int .u8)) bytes origin) state = .ok (.slice ⟨root, []⟩ 0 bytes.length) after ∧
      RootTypesExtend types nextTypes ∧
      AcceptedWorld config frame.initialized after ambient nextTypes (fun other => other = root ∨ liveRoots other)
        regions pending ∧
      AcceptedValue config.layout nextTypes frame.interpretation after ty roots (.slice ⟨root, []⟩ 0 bytes.length) := by
  have typing := checked.typing
  have provenance := checked.provenance
  cases h : frame.typingFuel with
  | zero =>
    rw [h] at typing
    change Except.error _ = Except.ok _ at typing
    cases typing
  | succ typeFuel =>
    simp only [h, typeExpr, pure] at typing
    simp only [rpExpr, pure, StateT.run] at provenance
    obtain ⟨rfl, _⟩ := provenance
    obtain ⟨⟨rfl, _⟩, _⟩ := typing
    exact evalValue_staticBytes_world fuel config frame.initialized frame.interpretation.environment frame.interpretation
      state ambient types liveRoots bytes origin world source.compatible.globalCount

#print axioms evalValue_staticBytes_world
#print axioms evalValue_checkedStaticBytes_world

end Goose.Proofs.ConstructionAcceptedExecution
