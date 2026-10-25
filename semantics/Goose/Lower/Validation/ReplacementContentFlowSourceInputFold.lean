import Goose.Lower.Validation.ReplacementContentFlowSourceAdmittedInputs
import Goose.GIR.ReplacementContentFlowProofsBounds

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

private theorem input_fold_covers (next : RootRef → Option ContentInputBound)
    (caller : Func) (sourceArgs : List (List RootRef)) (declared : List RootRef)
    (known : ∀ root ∈ declared, ∃ upper, next root = some upper ∧
      ∀ mapped, mapCalleeRoots sourceArgs root = .ok mapped →
        upper.covers (some (mapped.flatMap caller.expandParameterRoot)) = true)
    (accumulator result : List RootRef) (initial : ContentInputBound)
    (mapped : mapResultRoots sourceArgs accumulator declared = .ok result)
    (covered : initial.covers (some (accumulator.flatMap caller.expandParameterRoot)) = true) :
    ∃ upper, declared.foldlM (fun upper root => do
      let bound ← next root
      pure (upper.join bound)) initial = some upper ∧
      upper.covers (some (result.flatMap caller.expandParameterRoot)) = true := by
  induction declared generalizing accumulator initial with
  | nil =>
    have same : accumulator = result := (Except.ok.inj mapped)
    exact ⟨initial, rfl, same ▸ covered⟩
  | cons root rest ih =>
    obtain ⟨rootBound, rootKnown, rootCovered⟩ := known root (by simp)
    obtain ⟨roots, rootMapping, remaining⟩ := (ex_bind_ok _ _ _).mp mapped
    have joined := ContentInputBound.join_covers covered (rootCovered roots rootMapping)
    have unionCovered : (initial.join rootBound).covers
        (some ((unionRoots accumulator roots).flatMap caller.expandParameterRoot)) = true := by
      apply ContentInputBound.covers_subset joined
      intro actual member
      obtain ⟨source, sourceMember, expanded⟩ := List.mem_flatMap.mp member
      rcases (unionRoots_mem_iff _ _ _).mp sourceMember with old | fresh
      · exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨source, old, expanded⟩))
      · exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨source, fresh, expanded⟩))
    obtain ⟨upper, finished, finalCovered⟩ := ih
      (fun item member => known item (by simp [member])) (unionRoots accumulator roots)
      (initial.join rootBound) remaining unionCovered
    refine ⟨upper, ?_, finalCovered⟩
    simpa only [List.foldlM_cons, rootKnown, bind, Option.bind, pure, Pure.pure] using finished

theorem contentInputBound_covers_source_mapping {caller callee : Func}
    {argumentRoots : Nat → Option (List RootRef)} {sourceArgs : List (List RootRef)}
    {declared sourceResult : List RootRef}
    (mapping : mapResultRoots sourceArgs [] declared = .ok sourceResult)
    (parameters : ∀ index, RootRef.param index ∈ declared →
      ∃ upper, admittedArgumentBound callee argumentRoots index = some upper ∧
        upper.covers (some ((sourceArgs[index]?.getD []).flatMap caller.expandParameterRoot)) = true) :
    ∃ upper, contentInputBound callee argumentRoots declared = some upper ∧
      upper.covers (some (sourceResult.flatMap caller.expandParameterRoot)) = true := by
  let next := fun root => match root with
    | RootRef.global global => some (ContentInputBound.roots [.global global])
    | .param index => admittedArgumentBound callee argumentRoots index
    | .local _ => none
  obtain ⟨upper, finished, covered⟩ := input_fold_covers next caller sourceArgs declared (by
    intro root member
    cases root with
    | «local» slot =>
      have impossible := (mapResultRoots_ok sourceArgs declared [] sourceResult mapping).2 (.local slot) member
      exact False.elim impossible
    | global global =>
      refine ⟨.roots [.global global], rfl, ?_⟩
      intro roots mapped
      have same : roots = [.global global] := (Except.ok.inj mapped).symm
      subst roots
      simp [ContentInputBound.covers, Func.expandParameterRoot]
    | param index =>
      obtain ⟨bound, found, covered⟩ := parameters index member
      refine ⟨bound, found, ?_⟩
      intro roots mapped
      cases row : sourceArgs[index]? with
      | none => simp [mapCalleeRoots, row, reject] at mapped
      | some actual =>
        have same : actual = roots := by simpa [mapCalleeRoots, row, pure, Except.pure] using mapped
        subst actual
        simpa only [row, Option.getD_some] using covered) [] sourceResult (.roots []) mapping rfl
  refine ⟨upper, ?_, covered⟩
  unfold contentInputBound
  calc
    _ = declared.foldlM (fun accumulated root => do
        let bound ← next root
        pure (accumulated.join bound)) (.roots []) := by
      congr 1
      funext accumulated root
      cases root <;> rfl
    _ = some upper := finished

#print axioms contentInputBound_covers_source_mapping

#print axioms input_fold_covers

end Goose.Lower.Validation.ReplacementContentFlowSource
