import Goose.Lower.Validation.SummaryPreservationSourceScopeBounds
import Goose.Lower.Validation.SourceSymbolRefs
import Goose.Lower.Validation.InterfaceTypes
import Goose.Lower.Validation.Entry

namespace Goose.Lower.Validation

open Goose.Core

namespace SummaryPreservation

theorem SourceScopesWithin.of_scopeTableContains {parents : Array (Option Nat)}
    {scopes : List (Nat × Option Nat)} (contains : ScopeTableContains parents scopes) :
    SourceScopesWithin parents.size scopes := by
  intro entry member
  exact contains.scope_bound member

theorem accepted_impl_scope_bounds {module : Core.Module} {implementation : ImplId} {impl : Impl}
    (accepted : Core.validate module = .ok ()) (implAt : module.impls[implementation]? = some impl) :
    SourceScopesWithin (lowerImpl module impl).scopes.size (blockScopes none impl.body) := by
  have checked := validate_implementation_checks accepted
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? implAt))
  exact SourceScopesWithin.of_scopeTableContains (lowerImpl_lexicalScopeTable checked)

theorem accepted_context_scope_bounds {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} (accepted : Core.validate module = .ok ())
    (_contextAt : module.contexts[context]? = some ctx)
    (implAt : module.impls[ctx.impl]? = some impl) :
    SourceScopesWithin (lowerContextAt module ctx impl).scopes.size (blockScopes none impl.body) :=
  accepted_impl_scope_bounds accepted implAt

theorem accepted_global_scope_bounds {module : Core.Module} {index : GlobalId} {global : Core.Global}
    (accepted : Core.validate module = .ok ()) (globalAt : module.globals[index]? = some global) :
    SourceScopesWithin (lowerGlobal module global).init.scopes.size (exprScopes none global.init) :=
  SourceScopesWithin.of_scopeTableContains
    (lowerGlobal_lexicalScopeTable (validate_global_checks accepted globalAt))

end SummaryPreservation
end Goose.Lower.Validation
