import Goose.Lower.Validation.ReplacementContentFlowSourceContents
import Goose.GIR.ReplacementContentFlowProofsNormalization

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

end Goose.Lower.Validation.ReplacementContentFlowSource
