import Goose.Lower.Validation.SourceReadableEnvironment
import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Lower.Validation.SummaryPreservationEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

structure SourceContextEnvironment (typingEnv : TEnv) (env : PEnv) (context : ContextId) : Prop where
  accepted : Core.validate env.mod = .ok ()
  tables : SourceRootTables typingEnv env
  implementation : typingEnv.impl = some env.impl
  contextRow : env.mod.contexts[context]? = some env.ctx
  implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl

namespace SourceContextEnvironment

variable {typingEnv nextEnv : TEnv} {env : PEnv} {context : ContextId}

theorem readable (source : SourceContextEnvironment typingEnv env context) :
    SourceReadableEnvironment typingEnv := by
  apply SourceReadableEnvironment.implementation
  · simpa only [source.tables.moduleEq] using source.accepted
  · simpa only [source.tables.moduleEq] using source.implementationRow
  · exact source.tables.variablesEq.symm

theorem contextOk (source : SourceContextEnvironment typingEnv env context) :
    CtxOk env.mod env.impl env.ctx := by
  obtain ⟨impl, row, checked⟩ := (validate_modOk env.mod source.accepted).ctx context env.ctx source.contextRow
  rw [source.implementationRow] at row
  cases row
  exact checked

theorem parameters (source : SourceContextEnvironment typingEnv env context) :
    ParameterRootsClosed (lowerContextAt env.mod env.ctx env.impl) :=
  lowerContextAt_parameterRoots_closed source.accepted source.contextRow source.implementationRow

theorem typingTables (source : SourceContextEnvironment typingEnv env context)
    (moduleEq : nextEnv.mod = typingEnv.mod) (variablesEq : nextEnv.vars = typingEnv.vars)
    (implementationEq : nextEnv.impl = typingEnv.impl) :
    SourceContextEnvironment nextEnv env context :=
  ⟨source.accepted, ⟨source.tables.moduleEq.trans moduleEq.symm,
      source.tables.variablesEq.trans variablesEq.symm⟩,
    implementationEq.trans source.implementation, source.contextRow, source.implementationRow⟩

theorem expression (source : SourceContextEnvironment typingEnv env context) :
    SourceContextEnvironment (exprEnv typingEnv) env context :=
  source.typingTables rfl rfl rfl

theorem scopes (source : SourceContextEnvironment typingEnv env context) (scopes : List ScopeId) :
    SourceContextEnvironment typingEnv { env with scopes := scopes } context :=
  ⟨source.accepted, ⟨source.tables.moduleEq, source.tables.variablesEq⟩,
    source.implementation, source.contextRow, source.implementationRow⟩

#print axioms readable
#print axioms contextOk
#print axioms parameters
#print axioms typingTables
#print axioms expression
#print axioms scopes

end SourceContextEnvironment
end Goose.Lower.Validation.SummaryPreservation
