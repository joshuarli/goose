import Goose.Lower.Validation.ReplacementContentFlowSourceRoots
import Goose.Lower.Validation.SummaryPreservationRoots
import Goose.GIR.ReplacementContentFlowProofsNormalization

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem checkResultV_step_return_normalized {env : PEnv} {sourceRoots bound priorRoots valueRoots : List RootRef}
    {state : State} {states : Array State} {value : ValueId} {origin : Option OriginId}
    (checked : checkResultV env sourceRoots = .ok ())
    (resultRoots : env.ctx.resultRoots = [bound])
    (priorKnown : normalize (lowerContextAt env.mod env.ctx env.impl) state.returned = some priorRoots)
    (priorWithin : ∀ root ∈ priorRoots,
      root ∈ bound.flatMap (lowerContextAt env.mod env.ctx env.impl).expandParameterRoot)
    (valueKnown : normalize (lowerContextAt env.mod env.ctx env.impl) (flowAt state.values value) = some valueRoots)
    (valueWithin : ∀ root ∈ valueRoots,
      root ∈ sourceRoots.flatMap (lowerContextAt env.mod env.ctx env.impl).expandParameterRoot) :
    let func := lowerContextAt env.mod env.ctx env.impl
    ∃ actual, normalize func
        (step (lower env.mod) states func (func.valueTypes (lower env.mod)) state
          (.term (.ret [value] origin))).returned = some actual ∧
      ∀ root ∈ actual, root ∈ bound.flatMap func.expandParameterRoot := by
  dsimp only
  obtain ⟨noLocal, declared, declaredRow, sourceWithin⟩ := checkResultV_ok env sourceRoots checked
  have same : declared = bound := List.cons.inj (declaredRow.symm.trans resultRoots) |>.1
  subst declared
  obtain ⟨actual, known, within⟩ := normalize_join_known
    (lowerContextAt env.mod env.ctx env.impl) state.returned (flowAt state.values value)
    priorRoots valueRoots priorKnown valueKnown
  refine ⟨actual, known, ?_⟩
  intro root member
  rcases within root member with old | returned
  · exact priorWithin root old
  · obtain ⟨sourceRoot, sourceMember, expanded⟩ := List.mem_flatMap.mp (valueWithin root returned)
    exact List.mem_flatMap.mpr ⟨sourceRoot, sourceWithin sourceRoot sourceMember, expanded⟩

#print axioms checkResultV_step_return_normalized

theorem lowerContextAt_source_result_expanded {module : Core.Module} {ctx : Context} {impl : Impl}
    {index : Nat} (bounded : index < impl.results.size) :
    ∀ root ∈ (ctx.resultRoots[index]?.getD []).flatMap (lowerContextAt module ctx impl).expandParameterRoot,
      root ∈ (((lowerContextAt module ctx impl).roots.results[index]?).getD []).flatMap
        (lowerContextAt module ctx impl).expandParameterRoot := by
  intro root member
  obtain ⟨sourceRoot, sourceMember, expanded⟩ := List.mem_flatMap.mp member
  refine List.mem_flatMap.mpr ⟨sourceRoot, ?_, expanded⟩
  change sourceRoot ∈ ((lowerContextRootInfo ctx impl).results[index]?).getD []
  rw [SummaryPreservation.lowerContextRootInfo_result_eq bounded]
  exact unionRoots_left _ _ _ sourceMember

theorem checkReturned_of_source_result_bound {module : Core.Module} {ctx : Context} {impl : Impl}
    {type : Ty} {sourceRoots actual : List RootRef} {state : State}
    (results : impl.results.toList = [type]) (reference : type.isRefLike = true)
    (declared : ctx.resultRoots = [sourceRoots])
    (known : normalize (lowerContextAt module ctx impl) state.returned = some actual)
    (within : ∀ root ∈ actual,
      root ∈ sourceRoots.flatMap (lowerContextAt module ctx impl).expandParameterRoot) :
    checkReturned (lowerContextAt module ctx impl) state = true := by
  have resultBound : 0 < impl.results.size := by
    have length := congrArg List.length results
    simp only [Array.length_toList, List.length_singleton] at length
    omega
  have row := SummaryPreservation.lowerContextRootInfo_result_eq resultBound (ctx := ctx)
  have expanded := lowerContextAt_source_result_expanded (module := module) (ctx := ctx) resultBound
  simp only [declared, List.getElem?_cons_zero, Option.getD_some] at expanded
  have resultTypes : (lowerContextAt module ctx impl).results = [type] := results
  change (lowerContextAt module ctx impl).roots.results[0]? = some _ at row
  rw [row] at expanded
  simp only [Option.getD_some] at expanded
  unfold checkReturned
  rw [resultTypes]
  simp only [reference, ite_true, row, Option.any_some, rootsWithin, known]
  apply List.all_eq_true.mpr
  intro root member
  exact List.contains_iff_mem.mpr (expanded root (within root member))

#print axioms lowerContextAt_source_result_expanded
#print axioms checkReturned_of_source_result_bound

end Goose.Lower.Validation.ReplacementContentFlowSource
