import Goose.Lower.Validation.SummaryPreservationProvenance

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem roots_set_below {table upper : Array (List RootRef)} {index : Nat} {roots : List RootRef}
    (prior : RootsBelow table upper) (inserted : ∀ root ∈ roots, root ∈ rootsAt upper index) :
    RootsBelow (table.set! index roots) upper := by
  intro cell root member
  simp only [rootsAt, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at member
  split at member
  · rename_i same
    subst cell
    split at member
    · exact inserted root member
    · cases member
  · exact prior _ _ member

theorem empty_roots_below (size : Nat) (upper : Array (List RootRef)) :
    RootsBelow (Array.replicate size []) upper := by
  intro index root member
  simp only [rootsAt, Array.getElem?_replicate] at member
  split at member <;> cases member

theorem provStart_below_of_entry_seeds {vt : Array (Option VTy)} {func : Func} {upper : Prov}
    (slotSeeds : RootsBelow func.slotRootSeeds upper.slots)
    (valueSeeds : RootsBelow func.valueRootSeeds upper.vals)
    (seeds : ∀ block, func.blocks[0]? = some block →
      ∀ pair ∈ block.params.zipIdx,
        valRefLike vt pair.1.1 = true → RootRef.param pair.2 ∈ rootsAt upper.vals pair.1.1) :
    ProvenanceBelow (provStart vt func) upper := by
  refine ⟨slotSeeds, ?_⟩
  unfold provStart
  cases entry : func.blocks[0]? with
  | none => exact valueSeeds
  | some block =>
    apply List.foldlRecOn (motive := fun table => RootsBelow table upper.vals)
      block.params.zipIdx _ valueSeeds
    intro table prior pair member
    rcases pair with ⟨⟨value, paramTy⟩, index⟩
    change RootsBelow (if valRefLike vt value && value < table.size then
      table.set! value (unionRoots (rootsAt table value) [.param index]) else table) upper.vals
    split
    · rename_i active
      apply roots_set_below prior
      intro root rootMember
      rcases Goose.Core.Sound.unionRoots_mem _ _ _ rootMember with old | parameter
      · exact prior value root old
      · have same : root = .param index := List.mem_singleton.mp parameter
        subst root
        simp only [Bool.and_eq_true] at active
        exact seeds block entry ((value, paramTy), index) member active.1
    · exact prior

end Goose.Lower.Validation.SummaryPreservation
