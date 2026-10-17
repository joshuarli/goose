import Goose.Core.DeclarativeTyping
import Goose.Core.DeclarativeRoots
import Goose.Core.DeclarativeDemand

namespace Goose.Core

structure WellFormed (m : Module) : Prop where
  tables : DeclarativeTables m
  implementationTyping : ∀ (index : ImplId) (impl : Impl),
    m.impls[index]? = some impl → Declarative.ImplementationTyping m impl
  globalTyping : ∀ (index : GlobalId) (global : Global),
    m.globals[index]? = some global → Declarative.GlobalTyping m index global
  contextRoots : ∀ (index : ContextId) (context : Context),
    m.contexts[index]? = some context → ∃ impl,
      m.impls[context.impl]? = some impl ∧ Declarative.ContextRoots m impl context
  globalRoots : ∀ (index : GlobalId) (global : Global),
    m.globals[index]? = some global → Declarative.GlobalRoots m index global
  demand : DeclarativeDemand m

end Goose.Core
