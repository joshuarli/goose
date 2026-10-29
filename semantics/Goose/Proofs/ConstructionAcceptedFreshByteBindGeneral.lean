import Goose.Proofs.ConstructionAcceptedByteBinding
import Goose.Proofs.ConstructionAcceptedFreshByteInvokePublishGeneral

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Core (RootInst)
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem freshByteCall_bind_world (config : EvalConfig) (initialized : Nat)
    (before evaluated : ExecutionState) (frame : FreshDestinationFrame { evaluated with construction := { before.construction with
      exitReservations := before.construction.exitReservations.push .released } } evaluated)
    (sameOrdinals : evaluated.objectOrdinals = before.objectOrdinals)
    (actsMonotone : before.nextAct ≤ evaluated.nextAct) (scopesMonotone : before.nextScope ≤ evaluated.nextScope)
    (stored : StoredValue) (root : RootInst) (ty : Ty)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending)
    (nextWorld : AcceptedWorld config initialized evaluated ambient types live regions pending)
    (represented : ValueRepresentation ty (.stored stored)) (backed : StoredValueBacking config.layout evaluated stored)
    (identity : stored.storage = before.construction.storage.size)
    (named : stored.destination = some before.construction.destinations.size)
    (compatible : RootTypeCompatible types root ty) (conforms : LayoutConforms config.layout ty)
    (fresh : before.objectOrdinals.lookup root = none)
    (freshType : ∀ act scope id, root = .local act scope id → act < before.nextAct ∧ scope < before.nextScope)
    (freshSynthetic : ∀ id, root = .global id → config.module.globals.size ≤ id →
      id < config.module.globals.size + before.nextScope) :
    ∃ after, bindRoot root (.stored stored) evaluated = .ok () after ∧
      RootTypesExtend types (registerRootType types root ty) ∧
      AcceptedWorld config initialized after ambient (registerRootType types root ty)
        (fun other => other = root ∨ live other)
        (regions.map (fun region => extendReceivingLimit region stored.storage (storageExtent evaluated stored.storage))) pending := by
  have unrelated : ∀ region ∈ regions, ∀ row,
      evaluated.construction.destinations[region.destination]? = some row → row.storage ≠ stored.storage := by
    intro region member row present
    obtain ⟨old, oldPresent⟩ := (world.protections region member).present
    have inside := (Array.getElem?_eq_some_iff.mp oldPresent).1
    have current := (frame.lookup region.destination inside).trans oldPresent
    have equal : row = old := Option.some.inj (present.symm.trans current)
    subst row
    have bounded := (world.ownership.source.structural.1.1.1.2.2.1 region.destination old oldPresent).1
    rw [identity]
    exact Nat.ne_of_lt bounded
  have excluded : ∀ region ∈ regions, ¬ region.mutableRoots root → ∀ id,
      stored.destination = some id → id ∉ region.mutableDestinations := by
    intro region member immutable id destination included
    have equal : before.construction.destinations.size = id := Option.some.inj (named.symm.trans destination)
    have bounded := (world.protections region member).authorityBound id included
    omega
  obtain ⟨after, bound, extended, finalWorld⟩ := bindRoot_freshStored_extendedWorld config initialized evaluated
    ambient types live root ty stored regions pending nextWorld compatible conforms
    represented backed (by simpa only [sameOrdinals] using fresh) unrelated excluded
    (by intro act scope id same; obtain ⟨a, s⟩ := freshType act scope id same; exact ⟨Nat.lt_of_lt_of_le a actsMonotone, Nat.lt_of_lt_of_le s scopesMonotone⟩)
    (by intro id same lower; exact Nat.lt_of_lt_of_le (freshSynthetic id same lower) (Nat.add_le_add_left scopesMonotone _))
  exact ⟨after, bound, extended, finalWorld⟩

#print axioms freshByteCall_bind_world
end Goose.Proofs.ConstructionAcceptedExecution
