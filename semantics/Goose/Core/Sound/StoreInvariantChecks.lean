import Goose.Core.Sound.Store

namespace Goose.Core.Sound.StoreInvariantChecks
open Goose.Core Goose.Proofs.Memory

def backing : RootInst := .global 0
def ghost : RootInst := .global 1
def snapshot : St :=
  { St.initial with store := (Store.empty
      |>.introduce backing (.resizable .bool #[.bool true])
      |>.introduce ghost (.slice ⟨backing, []⟩ 0 1)) }

example (m : Module) :
    HasTy m 0 snapshot.store (.slice ⟨backing, []⟩ 0 1) (.slice .readOnly .bool) := by
  refine ⟨⟨backing, []⟩, 0, 1, rfl, rfl,
    .resizable .bool #[.bool true], #[.bool true], ?_, rfl, by decide, Or.inl ?_⟩
  · simp [snapshot, ghost, backing, Store.read, get_introduce, Val.get?]
  · refine ⟨rfl, ?_⟩
    intro index value present
    have bound := (Array.getElem?_eq_some_iff.mp present).1
    have zero : index = 0 := by simp at bound; omega
    subst index
    change some (Val.bool true) = some value at present
    cases present
    trivial

example (m : Module) (G : Nat) (demanded : RootInst → Prop) :
    ¬ StoreInv m G snapshot demanded := by
  intro invariant
  apply invariant.globalNonRefs 1 (.slice ⟨backing, []⟩ 0 1) _ trivial
  simp [snapshot, ghost, backing, get_introduce]

def flatSnapshot : St :=
  { St.initial with store := Store.empty.introduce ghost (.bool true) }

example (m : Module) : StoreInv m 0 flatSnapshot := by
  have shape : ∀ (r : RootInst) (v : Val),
      flatSnapshot.store.roots[r]? = some v → v = .bool true := by
    intro r v present
    by_cases equal : ghost = r
    · simpa [flatSnapshot, get_introduce, equal] using present.symm
    · simp [flatSnapshot, get_introduce, equal, St.initial, Store.empty] at present
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r v present _
    rw [shape r v present]
    trivial
  · intro r v present target targeted
    rw [shape r v present] at targeted
    cases targeted
  · intro activation scope localId present
    simp [flatSnapshot, ghost, get_introduce, St.initial, Store.empty] at present
  · intro g gl initialized
    omega
  · intro g v present
    rw [shape (.global g) v present]
    simp [IsRef]

end Goose.Core.Sound.StoreInvariantChecks
