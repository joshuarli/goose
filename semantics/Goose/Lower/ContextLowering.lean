import Goose.Lower.CoreToGir

namespace Goose.Lower

open Goose.Core

theorem lower_func_at {m : Module} {c : ContextId} {ctx : Context} {impl : Impl}
    (contextAt : m.contexts[c]? = some ctx) (implAt : m.impls[ctx.impl]? = some impl) :
    (lower m).funcs[c]? = some (lowerContextAt m ctx impl) := by
  simp [lower, Array.getElem?_map, contextAt, implAt, lowerContextAt]

theorem lower_context_sigs_at {m : Module} {c : ContextId} {ctx : Context} {impl : Impl}
    (vars : Array LocalVar) (results : List Ty)
    (contextAt : m.contexts[c]? = some ctx) (implAt : m.impls[ctx.impl]? = some impl) :
    (lowerEnv m vars results).sigs[c]? =
      some (impl.params.toList.map (tyOfVar impl ·.var), impl.results.toList) := by
  simp [lowerEnv, Array.getElem?_map, contextAt, implAt]

theorem lowerContextAt_blocks (m : Module) (ctx : Context) (impl : Impl) :
    (lowerContextAt m ctx impl).blocks = (lowerImpl m impl).blocks := rfl

theorem lowerContextAt_params (m : Module) (ctx : Context) (impl : Impl) :
    (lowerContextAt m ctx impl).params = (lowerImpl m impl).params := rfl

theorem lowerContextAt_results (m : Module) (ctx : Context) (impl : Impl) :
    (lowerContextAt m ctx impl).results = (lowerImpl m impl).results := rfl

theorem lowerContextAt_slots (m : Module) (ctx : Context) (impl : Impl) :
    (lowerContextAt m ctx impl).slots = (lowerImpl m impl).slots := rfl

theorem lowerContextAt_scopes (m : Module) (ctx : Context) (impl : Impl) :
    (lowerContextAt m ctx impl).scopes = (lowerImpl m impl).scopes := rfl

theorem lower_invalid_context {m : Module} {c : ContextId} {ctx : Context}
    (contextAt : m.contexts[c]? = some ctx) (implMissing : m.impls[ctx.impl]? = none) :
    (lower m).funcs[c]? = some (invalidContextFunction ctx) := by
  simp [lower, Array.getElem?_map, contextAt, implMissing]

end Goose.Lower
