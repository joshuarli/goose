import Goose.GIR.ReplacementContentFlowProofsNormalization
import Goose.Lower.Validation.ReplacementContentFlowSourceResults

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.GIR.ReplacementContentFlow.Model
open SummaryPreservation

theorem accepted_context_return_normalized {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {types : Array (Option VTy)}
    (accepted : Core.validate module = .ok ())
    (contextRow : module.contexts[context]? = some ctx)
    (implementationRow : module.impls[ctx.impl]? = some impl) :
    ∃ actual, normalize (lowerContextAt module ctx impl)
        (start (lowerContextAt module ctx impl) types).returned = some actual ∧
      ∀ root ∈ actual, root ∈ (ctx.resultRoots[0]?.getD []).flatMap
        (lowerContextAt module ctx impl).expandParameterRoot := by
  refine ⟨[], ?_, by simp⟩
  rw [start_returned]
  exact normalize_empty _

theorem accepted_global_return_normalized {module : Core.Module} {index : GlobalId}
    {global : Core.Global} {types : Array (Option VTy)}
    (accepted : Core.validate module = .ok ())
    (globalRow : module.globals[index]? = some global) :
    normalize (lowerGlobal module global).init (start (lowerGlobal module global).init types).returned =
      some [] := by
  rw [start_returned]
  exact normalize_empty _

#print axioms accepted_context_return_normalized
#print axioms accepted_global_return_normalized

end Goose.Lower.Validation.ReplacementContentFlowSource
