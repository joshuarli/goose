import Goose.Lower.Validation.SummaryPreservationRootBounds
import Goose.Lower.Validation.SummaryPreservationTransfer

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def contextSlotUpper (module : Core.Module) (ctx : Context) (impl : Impl) : Array (List RootRef) :=
  impl.vars.mapIdx fun slot _ => allowedRoots (lowerContextAt module ctx impl)
    ((ctx.varRoots.find? (·.1 == slot)).map (·.2) |>.getD [])

theorem contextSlotUpper_at {module : Core.Module} {ctx : Context} {impl : Impl}
    {slot : SlotId} {localVar : LocalVar} (lookup : impl.vars[slot]? = some localVar) :
    rootsAt (contextSlotUpper module ctx impl) slot = allowedRoots (lowerContextAt module ctx impl)
      ((ctx.varRoots.find? (·.1 == slot)).map (·.2) |>.getD []) := by
  simp [rootsAt, contextSlotUpper, Array.getElem?_mapIdx, lookup]

theorem contextSlotUpper_represent (module : Core.Module) (ctx : Context) (impl : Impl)
    (slot : SlotId) :
    RootsRepresent (lowerContextAt module ctx impl) (rootsAt (contextSlotUpper module ctx impl) slot)
      ((ctx.varRoots.find? (·.1 == slot)).map (·.2) |>.getD []) := by
  cases lookup : impl.vars[slot]? with
  | none =>
    have empty : rootsAt (contextSlotUpper module ctx impl) slot = [] := by
      simp [rootsAt, contextSlotUpper, Array.getElem?_mapIdx, lookup]
    rw [empty]
    exact rootsRepresent_empty _ _
  | some localVar =>
    rw [contextSlotUpper_at lookup]
    exact allowedRoots_represent _ _

theorem bindRootsV_slot_bound {module : Core.Module} {ctx : Context} {impl : Impl}
    {scopes chain : List Nat} {slot : SlotId} {actual source : List RootRef}
    (checked : bindRootsV ⟨module, impl, ctx, scopes⟩ chain slot source = .ok ())
    (represented : RootsRepresent (lowerContextAt module ctx impl) actual source)
    (parameters : ∀ index, RootRef.param index ∈ actual →
      index < (lowerContextAt module ctx impl).params.length) :
    ∀ root ∈ actual, root ∈ rootsAt (contextSlotUpper module ctx impl) slot := by
  obtain ⟨localVar, annotation, variableRow, annotationRow, subset, _⟩ :=
    bindRootsV_ok _ _ _ _ checked
  intro root member
  rw [contextSlotUpper_at variableRow]
  change (ctx.varRoots.find? (·.1 == slot)).map (·.2) = some annotation at annotationRow
  rw [annotationRow]
  exact allowedRoots_complete (rootsRepresent_mono represented subset) parameters root member

theorem slotInit_roots_closed {module : Core.Module} {ctx : Context} {impl : Impl}
    {res : Array (List RootRef)} {vt : Array (Option VTy)} {provenance : Prov}
    {scopes chain : List Nat} {slot : SlotId} {value : ValueId}
    {origin : Option OriginId} {source : List RootRef}
    (checked : bindRootsV ⟨module, impl, ctx, scopes⟩ chain slot source = .ok ())
    (represented : RootsRepresent (lowerContextAt module ctx impl)
      (rootsAt provenance.vals value) source)
    (parameters : ∀ index, RootRef.param index ∈ rootsAt provenance.vals value →
      index < (lowerContextAt module ctx impl).params.length)
    (slots : provenance.slots = contextSlotUpper module ctx impl) :
    InstructionRootsClosed res vt (lowerContextAt module ctx impl) provenance
      (.eff (.slotInit slot value origin)) := by
  intro root member
  rw [slots]
  exact bindRootsV_slot_bound checked represented parameters root member

theorem store_local_roots_closed {module : Core.Module} {ctx : Context} {impl : Impl}
    {res : Array (List RootRef)} {vt : Array (Option VTy)} {provenance : Prov}
    {scopes chain : List Nat} {slot : SlotId} {address value : ValueId}
    {origin : Option OriginId} {source : List RootRef}
    (checked : bindRootsV ⟨module, impl, ctx, scopes⟩ chain slot source = .ok ())
    (represented : RootsRepresent (lowerContextAt module ctx impl)
      (rootsAt provenance.vals value) source)
    (parameters : ∀ index, RootRef.param index ∈ rootsAt provenance.vals value →
      index < (lowerContextAt module ctx impl).params.length)
    (addressRoots : rootsAt provenance.vals address = [.local slot])
    (slots : provenance.slots = contextSlotUpper module ctx impl) :
    InstructionRootsClosed res vt (lowerContextAt module ctx impl) provenance
      (.eff (.store address value origin)) := by
  intro target targetMember root member
  rw [addressRoots] at targetMember
  have same : target = slot := RootRef.local.inj (List.mem_singleton.mp targetMember)
  subst target
  rw [slots]
  exact bindRootsV_slot_bound checked represented parameters root member

end Goose.Lower.Validation.SummaryPreservation
