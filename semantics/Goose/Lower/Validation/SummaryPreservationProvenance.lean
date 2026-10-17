import Goose.GIR.Effects
import Goose.Lower.Validation.SummaryPreservationRoots

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

def RootsBelow (left right : Array (List RootRef)) : Prop :=
  ∀ index root, root ∈ rootsAt left index → root ∈ rootsAt right index

structure ProvenanceBelow (left right : Prov) : Prop where
  slots : RootsBelow left.slots right.slots
  vals : RootsBelow left.vals right.vals

theorem rootsOfDef_mono {res res' : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {before after : Prov} {result : ValueId}
    (results : RootsBelow res res') (provenance : ProvenanceBelow before after) (op : Op) :
    ∀ root ∈ rootsOfDef res vt func before result op,
      root ∈ rootsOfDef res' vt func after result op := by
  cases op with
  | load address =>
    intro root member
    simp only [rootsOfDef] at member ⊢
    split at member
    · rename_i refLike
      rw [if_pos refLike]
      rcases mem_unionRoots_iff.mp member with stored | content
      · apply unionRoots_left
        obtain ⟨source, sourceMember, rootMember⟩ := List.mem_flatMap.mp stored
        apply List.mem_flatMap.mpr
        refine ⟨source, provenance.vals _ _ sourceMember, ?_⟩
        cases source with
        | «local» slot => exact provenance.slots _ _ rootMember
        | _ => exact rootMember
      · apply unionRoots_right
        cases valueType : vt[result]? with
        | none => simpa [valueType] using content
        | some maybeType =>
          cases maybeType with
          | none => simpa [valueType] using content
          | some ty =>
            cases ty with
            | view mutability element => simpa [valueType] using content
            | data ty =>
              cases ty <;> try simpa [valueType] using content
              rename_i mutability element
              simp only [valueType] at content ⊢
              obtain ⟨source, sourceMember, rootMember⟩ := List.mem_flatMap.mp content
              exact List.mem_flatMap.mpr ⟨source, provenance.vals _ _ sourceMember, rootMember⟩
    · rename_i notRefLike
      rw [if_neg notRefLike]
      exact member
  | call callee args origin =>
    intro root member
    obtain ⟨source, sourceMember, rootMember⟩ := List.mem_flatMap.mp member
    apply List.mem_flatMap.mpr
    refine ⟨source, results _ _ sourceMember, ?_⟩
    cases source with
    | param index =>
      cases argument : args[index]? with
      | none => simpa [argument] using rootMember
      | some value =>
        simp only [argument] at rootMember ⊢
        exact provenance.vals _ _ rootMember
    | _ => exact rootMember
  | _ =>
    all_goals intro root member
    all_goals first
      | exact provenance.vals _ _ member
      | exact member

theorem addTo_origin {table : Array (List RootRef)} {index cell : Nat}
    {roots : List RootRef} {root : RootRef}
    (member : root ∈ rootsAt (addTo table index roots).1 cell) :
    root ∈ rootsAt table cell ∨ cell = index ∧ root ∈ roots := by
  unfold addTo at member
  dsimp only at member
  split at member
  · exact Or.inl member
  · simp only [rootsAt, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at member
    split at member
    · rename_i same
      subst cell
      split at member
      · simp only [Option.getD_some] at member
        exact (mem_unionRoots_iff.mp member).elim Or.inl (fun found => Or.inr ⟨rfl, found⟩)
      · simp at member
    · exact Or.inl member

theorem addTo_below {table upper : Array (List RootRef)} {index : Nat}
    {roots : List RootRef} (prior : RootsBelow table upper)
    (inserted : ∀ root ∈ roots, root ∈ rootsAt upper index) :
    RootsBelow (addTo table index roots).1 upper := by
  intro cell root member
  rcases addTo_origin (table := table) (index := index) (roots := roots) member with
    priorRoot | ⟨same, insertedRoot⟩
  · exact prior _ _ priorRoot
  · rw [same]
    exact inserted _ insertedRoot

theorem provFix_below {res : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper initial : Prov}
    (rounds : ∀ current, ProvenanceBelow current upper →
      ProvenanceBelow (provRound res vt func current).1 upper)
    (start : ProvenanceBelow initial upper) (fuel : Nat) :
    ProvenanceBelow (provFix res vt func fuel initial) upper := by
  induction fuel generalizing initial with
  | zero => exact start
  | succ fuel ih =>
    simp only [provFix]
    split
    · exact ih (rounds initial start)
    · exact rounds initial start

end Goose.Lower.Validation.SummaryPreservation
