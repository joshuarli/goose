import Goose.GIR.ReplacementContentFlowProofsScopedContentCalls
import Goose.GIR.ReplacementContentFlowProofsCanonicalFacts

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

theorem scoped_slotInit_source
    {module : Module} {func : Func} {types : Array (Option VTy)}
    {slot source : Nat} {origin : Option OriginId}
    (typed : InstructionTyping module func types (.eff (.slotInit slot source origin)))
    {selected slots : Nat → Prop}
    (slotsTyped : ∀ slot, slots slot → ∃ storage, func.slots[slot]? = some storage ∧ storage.ty.isSlice = true)
    (chosen : slots slot)
    (select : ∀ type, types[source]? = some (some (.data type)) → type.isSlice = true → selected source) :
    selected source := by
  cases typed with
  | slotInit _ _ _ storage row canonical =>
    obtain ⟨actual, actualAt, slice⟩ := slotsTyped slot chosen
    have same : storage = actual := Option.some.inj (row.symm.trans actualAt)
    exact select storage.ty canonical (same ▸ slice)
  | effect _ ordinary _ => exact False.elim (ordinary slot source origin rfl)

theorem canonical_scoped_store_memory
    {module : Module} {func : Func} {types : Array (Option VTy)} {provenance : Prov}
    {final current : State} {address source : Nat} {origin : Option OriginId}
    {selected slots : Nat → Prop} {predicate : Atom → Prop}
    (canonical : final.CanonicalWithin func types provenance)
    (growth : current.Extends final)
    (typed : InstructionTyping module func types (.eff (.store address source origin)))
    (bounded : address < func.numValues)
    (reference : valRefLike types source = true)
    (before : current.ScopedContentWithin selected slots (fun _ => False) predicate)
    (slotsTyped : ∀ slot, slots slot → ∃ storage, func.slots[slot]? = some storage ∧ storage.ty.isSlice = true)
    (select : ∀ slot type, slots slot → RootRef.local slot ∈ rootsAt provenance.vals address →
      types[source]? = some (some (.data type)) → type.isSlice = true → selected source) :
    (write func (touchValues types current [address]) (flowAt current.values address)
      (flowAt current.values source)).ScopedMemoryWithin slots (fun _ => False) predicate := by
  cases typed with
  | store _ _ _ mutability payload addressType sourceType =>
    have payloadReference : payload.isRefLike = true := by
      simpa only [valRefLike, sourceType, Option.getD_some, VTy.refLike] using reference
    have physical := (growth.values.values address).atomsWithin
      (canonical.holderValues address (by rw [canonical.shape.values]; exact bounded)
        mutability payload addressType payloadReference)
    change HolderRoots func payload (rootsAt provenance.vals address) (flowAt current.values address) at physical
    apply write_scoped_memory before.memory.touchValues
    · intro unknown
      rw [unknown] at physical
      exact physical
    · intro addresses addressAt slot chosen member
      rw [addressAt] at physical
      obtain ⟨storage, row, type, included⟩ := (physical (.local slot) member).local
      obtain ⟨actual, actualAt, slice⟩ := slotsTyped slot chosen
      have same : actual = storage := Option.some.inj (actualAt.symm.trans row)
      have payloadSlice : payload.isSlice = true := by simpa only [same, type] using slice
      exact before.values source (select slot payload chosen included sourceType payloadSlice)
    · intro addresses addressAt index impossible
      exact False.elim impossible
  | effect _ _ nonstore => exact False.elim (nonstore address source origin rfl)

#print axioms scoped_slotInit_source
#print axioms canonical_scoped_store_memory

end Goose.GIR.ReplacementContentFlow.Model
