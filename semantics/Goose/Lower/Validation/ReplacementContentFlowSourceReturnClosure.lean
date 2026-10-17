import Goose.Lower.Validation.ReplacementContentFlowSourceRegionCertificates
import Goose.GIR.ReplacementContentFlowProofsRefinement
import Goose.GIR.ReplacementContentFlowProofsClosure

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

private theorem returned_fold_within (module : GIR.Module) (callees : Array State) (func : Func)
    (types : Array (Option VTy)) (instructions : List Inst) (state : State) (upper : List RootRef)
    (before : state.returned.NormalizedWithin func upper)
    (operands : ∀ value origin, Inst.term (.ret [value] origin) ∈ instructions →
      (flowAt (instructions.foldl (step module callees func types) state).values value).NormalizedWithin func upper) :
    (instructions.foldl (step module callees func types) state).returned.NormalizedWithin func upper := by
  induction instructions generalizing state with
  | nil => exact before
  | cons inst rest ih =>
    have growth : state.Extends (rest.foldl (step module callees func types)
        (step module callees func types state inst)) :=
      (step_extends module callees func types state inst).trans
        (state_foldl_extends rest (step module callees func types)
          (step_extends module callees func types) _)
    have next : (step module callees func types state inst).returned.NormalizedWithin func upper := by
      rw [step_returned]
      cases inst with
      | «def» value op => exact before
      | eff effect => exact before
      | term term =>
        cases term <;> try exact before
        case ret values origin =>
          cases values with
          | nil => exact before
          | cons value tail =>
            cases tail with
            | nil => exact before.join ((growth.values.values value).normalizedWithin
                (operands value origin (by simp)))
            | cons next more => exact before
    exact ih _ next (fun value origin member => operands value origin (by simp [member]))

private theorem round_instructions (module : GIR.Module) (callees : Array State) (func : Func)
    (types : Array (Option VTy)) (state : State) :
    round module callees func types state =
      (func.blocks.toList.flatMap (·.insts)).foldl (step module callees func types) state := by
  simp only [round, ← Array.foldl_toList, List.foldl_flatMap]

theorem round_returned_within {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {state : State} {upper : List RootRef}
    (before : state.returned.NormalizedWithin func upper)
    (operands : ∀ block ∈ func.blocks.toList, ∀ value origin,
      Inst.term (.ret [value] origin) ∈ block.insts →
      (flowAt (round module callees func types state).values value).NormalizedWithin func upper) :
    (round module callees func types state).returned.NormalizedWithin func upper := by
  rw [round_instructions]
  apply returned_fold_within _ _ _ _ _ _ _ before
  intro value origin member
  obtain ⟨block, blockMember, instruction⟩ := List.mem_flatMap.mp member
  rw [← round_instructions]
  exact operands block blockMember value origin instruction

theorem reachable_returned_within {module : GIR.Module} {callees : Array State} {func : Func}
    {types : Array (Option VTy)} {initial final : State} {upper : List RootRef}
    (reachable : FunctionReachable module callees func types initial final)
    (before : initial.returned.NormalizedWithin func upper)
    (operands : ∀ block ∈ func.blocks.toList, ∀ value origin,
      Inst.term (.ret [value] origin) ∈ block.insts →
      (flowAt final.values value).NormalizedWithin func upper) :
    final.returned.NormalizedWithin func upper := by
  induction reachable with
  | refl => exact before
  | @next current reachable ih =>
      have earlier : ∀ block ∈ func.blocks.toList, ∀ value origin,
          Inst.term (.ret [value] origin) ∈ block.insts →
          (flowAt current.values value).NormalizedWithin func upper := by
        intro block member value origin instruction
        exact ((round_extends module callees func types current).values.values value).normalizedWithin
          (operands block member value origin instruction)
      exact round_returned_within (ih earlier) operands

theorem reachable_checkReturned_of_value_bounds {module : GIR.Module} {callees : Array State}
    {func : Func} {types : Array (Option VTy)} {provenance : Prov} {final : State}
    {type : Ty} {declared : List RootRef}
    (checked : func.checkAdmittedRegions module types provenance = .ok ())
    (result : func.results = [type]) (reference : type.isRefLike = true)
    (row : func.roots.results[0]? = some declared)
    (reachable : FunctionReachable module callees func types (start func types) final)
    (typed : ∀ block ∈ func.blocks.toList, ∀ value origin,
      Inst.term (.ret [value] origin) ∈ block.insts → valRefLike types value = true)
    (values : ∀ value, (flowAt final.values value).NormalizedWithin func
      ((rootsAt provenance.vals value).flatMap func.expandParameterRoot)) :
    checkReturned func final = true := by
  have initial : (start func types).returned = .known (declared.eraseDups.map Atom.ofRootRef) := by
    cases entry : func.blocks[0]? <;> simp [start, entry, declaredReturn, result, reference, row]
  obtain ⟨roots, known, members⟩ := normalize_rootMap_dedup_known func declared
  have initialBound : (start func types).returned.NormalizedWithin func
      (declared.flatMap func.expandParameterRoot) := by
    rw [initial]
    exact Or.inr ⟨roots, known, fun root member => (members root).mp member⟩
  have finalBound := reachable_returned_within reachable initialBound (by
    intro block member value origin instruction
    apply (values value).mono
    intro root included
    obtain ⟨source, sourceMember, expanded⟩ := List.mem_flatMap.mp included
    have permitted := func.checkAdmittedRegions_return checked member instruction
      (value := value) (index := 0) (by simp) (typed block member value origin instruction) source sourceMember
    rw [row, Option.getD_some] at permitted
    exact List.mem_flatMap.mpr ⟨source, permitted, expanded⟩)
  apply checkReturned_of_normalized_bound result reference row finalBound
  exact reachable.extends.returned.ready (by rw [initial]; simp)

#print axioms reachable_checkReturned_of_value_bounds
#print axioms round_returned_within
#print axioms reachable_returned_within

end Goose.Lower.Validation.ReplacementContentFlowSource
