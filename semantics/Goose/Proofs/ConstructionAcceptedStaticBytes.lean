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

theorem evalValue_staticBytes_world (fuel : Nat) (config : EvalConfig) (initialized : Nat)
    (environment : RuntimeActivation) (interpretation : RootInterpretation)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (liveRoots : RootInst → Prop) (bytes : List UInt8) (origin : Nat)
    (world : AcceptedWorld config initialized state ambient types liveRoots [] [])
    (globalCount : interpretation.globalCount = config.module.globals.size) :
    ∃ after nextTypes root,
      evalValue (fuel + 1) config environment (.bytes (.slice .readOnly (.int .u8)) bytes origin) state =
        .ok (.slice ⟨root, []⟩ 0 bytes.length) after ∧
      RootTypesExtend types nextTypes ∧
      AcceptedWorld config initialized after ambient nextTypes (fun other => other = root ∨ liveRoots other) [] [] ∧
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
    · constructor
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
    · intro region present
      cases present
    · intro frame present
      cases present
    · intro id available
      exact Or.inr (world.globalLive id available)
  · refine ⟨.slice .readOnly (.int .u8) ⟨root, []⟩ 0 bytes.length,
      .slice .readOnly (.int .u8) ownerTy ⟨root, []⟩ 0 bytes.length ?_ rfl, .slice _ _ _, ?_⟩
    · exact ⟨ownerTy, by simp only [registerRootType, ↓reduceIte], .root ownerTy⟩
    · intro location reference
      cases reference
      exact ⟨.static, List.mem_cons_self, .static _ (by rw [globalCount]; omega)⟩

#print axioms evalValue_staticBytes_world

end Goose.Proofs.ConstructionAcceptedExecution
