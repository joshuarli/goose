import Goose.Lower.Validation.ReplacementContentFlowSourceContents
import Goose.GIR.ReplacementContentFlowProofsNormalization
import Goose.GIR.ReplacementContentFlowProofsWrites
import Goose.GIR.ReplacementContentFlowProofsRank

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model

theorem checkStore_join_normalized {env : PEnv} {varId : VarId}
    {localVar : LocalVar} {storedRoots bound currentRoots valueRoots : List RootRef}
    {current value : Roots}
    (varIdRow : env.impl.vars[varId]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (contentRow : env.cont varId = some bound)
    (checked : checkStore env (.deref (.read (.var varId))) storedRoots = .ok ())
    (currentKnown : normalize (lowerContextAt env.mod env.ctx env.impl) current = some currentRoots)
    (valueKnown : normalize (lowerContextAt env.mod env.ctx env.impl) value = some valueRoots)
    (currentWithin : ∀ root ∈ currentRoots,
      root ∈ bound.flatMap (lowerContextAt env.mod env.ctx env.impl).expandParameterRoot)
    (valueWithin : ∀ root ∈ valueRoots,
      root ∈ storedRoots.flatMap (lowerContextAt env.mod env.ctx env.impl).expandParameterRoot) :
    ∃ actual, normalize (lowerContextAt env.mod env.ctx env.impl) (current.join value) = some actual ∧
      ∀ root ∈ actual,
        root ∈ bound.flatMap (lowerContextAt env.mod env.ctx env.impl).expandParameterRoot := by
  have sliceVariable : env.isRefSliceVar varId = true := by
    simp [PEnv.isRefSliceVar, varIdRow, reference]
  obtain ⟨actualBound, actualContentRow, sourceWithin⟩ :=
    checkStore_ok env _ storedRoots checked varId rfl sliceVariable
  have same : actualBound = bound := Option.some.inj (actualContentRow.symm.trans contentRow)
  subst actualBound
  obtain ⟨actual, known, within⟩ := normalize_join_known _ current value currentRoots valueRoots currentKnown valueKnown
  refine ⟨actual, known, ?_⟩
  intro root member
  rcases within root member with old | written
  · exact currentWithin root old
  · obtain ⟨sourceRoot, sourceMember, expanded⟩ := List.mem_flatMap.mp (valueWithin root written)
    exact List.mem_flatMap.mpr ⟨sourceRoot, sourceWithin sourceRoot sourceMember, expanded⟩

#print axioms checkStore_join_normalized

theorem checkStore_parameter_write_normalized {env : PEnv} {index : Nat} {param : Param}
    {localVar : LocalVar} {storedRoots bound currentRoots valueRoots : List RootRef}
    {state : State} {value : Roots}
    (parameter : env.impl.params[index]? = some param)
    (variableRow : env.impl.vars[param.var]? = some localVar)
    (reference : localVar.ty.isRefSlice = true)
    (contentRow : env.cont param.var = some bound)
    (checked : checkStore env (.deref (.read (.var param.var))) storedRoots = .ok ())
    (shape : state.Shape (lowerContextAt env.mod env.ctx env.impl))
    (currentKnown : normalize (lowerContextAt env.mod env.ctx env.impl)
      (flowAt state.contents index) = some currentRoots)
    (valueKnown : normalize (lowerContextAt env.mod env.ctx env.impl) value = some valueRoots)
    (currentWithin : ∀ root ∈ currentRoots,
      root ∈ bound.flatMap (lowerContextAt env.mod env.ctx env.impl).expandParameterRoot)
    (valueWithin : ∀ root ∈ valueRoots,
      root ∈ storedRoots.flatMap (lowerContextAt env.mod env.ctx env.impl).expandParameterRoot) :
    let func := lowerContextAt env.mod env.ctx env.impl
    ∃ actual, normalize func (flowAt (write func state (.known [.param index]) value).contents index) =
      some actual ∧ ∀ root ∈ actual, root ∈ bound.flatMap func.expandParameterRoot := by
  dsimp only
  have typeRow := SummaryPreservation.lowerContext_parameter_type (module := env.mod) (ctx := env.ctx) parameter variableRow
  have formalReference : ((lowerContextAt env.mod env.ctx env.impl).params[index]?).any Ty.isRefSlice = true := by
    simp [typeRow, reference]
  rw [write_parameter_content _ _ index value formalReference (by
    rw [shape.contents]
    exact (List.getElem?_eq_some_iff.mp typeRow).1)]
  exact checkStore_join_normalized variableRow reference contentRow checked
    currentKnown valueKnown currentWithin valueWithin

#print axioms checkStore_parameter_write_normalized

end Goose.Lower.Validation.ReplacementContentFlowSource
