import Goose.Lower.Validation.SummaryPreservationReplayEntry
import Goose.Lower.Validation.SummaryPreservationStart

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem entryRootValues_at {types : List VTy} {index : Nat} {ty : VTy}
    (row : types[index]? = some ty) :
    rootsAt (entryRootValues types) index = if ty.refLike then [.param index] else [] := by
  simp [rootsAt, entryRootValues, row]

theorem provStart_below_retained_entry {types : List VTy} {vt : Array (Option VTy)}
    {func : Func} {upper : Prov}
    (slotSeeds : RootsBelow func.slotRootSeeds upper.slots)
    (valueSeeds : RootsBelow func.valueRootSeeds upper.vals)
    (entry : ∀ block, func.blocks[0]? = some block →
      block.params = (List.range types.length).zip types)
    (typed : ∀ (index : Nat) (ty : VTy), types[index]? = some ty → vt[index]? = some (some ty))
    (retained : ∀ index, index < types.length →
      rootsAt upper.vals index = rootsAt (entryRootValues types) index) :
    ProvenanceBelow (provStart vt func) upper := by
  apply provStart_below_of_entry_seeds slotSeeds valueSeeds
  intro block blockAt pair member reference
  rw [entry block blockAt] at member
  obtain ⟨⟨value, ty⟩, index⟩ := pair
  have lookup := List.mk_mem_zipIdx_iff_getElem?.mp member
  obtain ⟨valueAt, typeAt⟩ := List.getElem?_zip_eq_some.mp lookup
  have bound : index < types.length := (List.getElem?_eq_some_iff.mp typeAt).1
  rw [List.getElem?_range bound] at valueAt
  have same : value = index := (Option.some.inj valueAt).symm
  subst value
  have refLike : ty.refLike = true := by
    simpa only [valRefLike, typed index ty typeAt] using reference
  rw [retained index bound, entryRootValues_at typeAt, if_pos refLike]
  exact List.mem_singleton_self _

end Goose.Lower.Validation.SummaryPreservation
