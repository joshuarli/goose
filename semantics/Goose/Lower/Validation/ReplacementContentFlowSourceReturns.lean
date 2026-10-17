import Goose.GIR.ReplacementContentFlowProofsNormalization
import Goose.Lower.Validation.ReplacementContentFlowSourceResults

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model
open SummaryPreservation

theorem accepted_context_return_normalized {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    ∃ actual, normalize (lowerContextAt module ctx impl)
        (declaredReturn (lowerContextAt module ctx impl)) = some actual ∧
      ∀ root ∈ actual, root ∈ (ctx.resultRoots[0]?.getD []).flatMap
        (lowerContextAt module ctx impl).expandParameterRoot := by
  obtain ⟨bodyType, next, typed, shape⟩ :=
    ((Core.Sound.validate_modOk module accepted).impl ctx.impl impl implementationRow).body
  rcases shape with ⟨empty, _⟩ | ⟨type, singleton, _⟩
  · refine ⟨[], ?_, by simp⟩
    simp [declaredReturn, lowerContextAt, lowerImpl, empty, normalize]
  · by_cases reference : type.isRefLike = true
    · have bound : 0 < impl.results.size := by
        have size : impl.results.size = 1 := by
          simpa using congrArg List.length singleton
        omega
      let declared := ((lowerContextAt module ctx impl).roots.results[0]?).getD []
      have row : (lowerContextRootInfo ctx impl).results[0]? = some declared := by
        simp only [declared, lowerContextAt]
        rw [lowerContextRootInfo_result_eq bound]
        rfl
      obtain ⟨actual, normalized, members⟩ :=
        normalize_rootMap_known (lowerContextAt module ctx impl) declared
      refine ⟨actual, ?_, ?_⟩
      · simpa only [declaredReturn, lowerContextAt, lowerImpl, singleton, reference, ite_true, row]
          using normalized
      · intro root member
        exact accepted_context_result_expanded accepted contextRow implementationRow bound root
          ((members root).mp member)
    · refine ⟨[], ?_, by simp⟩
      simp [declaredReturn, lowerContextAt, lowerImpl, singleton, reference, normalize]

theorem accepted_global_return_normalized {module : Core.Module} {index : GlobalId}
    {global : Core.Global} (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global) :
    normalize (lowerGlobal module global).init (declaredReturn (lowerGlobal module global).init) =
      some [] := by
  rw [accepted_global_return_seed accepted globalRow]
  exact normalize_empty _

#print axioms accepted_context_return_normalized
#print axioms accepted_global_return_normalized

end Goose.Lower.Validation.ReplacementContentFlowSource
