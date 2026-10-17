import Goose.Lower.Validation.SourceRootShape
import Goose.Lower.Validation.SourceReadable
import Goose.Lower.Validation.SummaryPreservationEffects

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

structure SourceGlobalEnvironment (typingEnv : TEnv) (env : PEnv) (func : Func) : Prop where
  accepted : Core.validate env.mod = .ok ()
  tables : SourceRootTables typingEnv env
  variables : typingEnv.vars = #[]
  inside : typingEnv.inExpr = true
  noParameters : env.impl.params = #[]
  parameterIdentity : ∀ index, func.parameterRoots index = [.param index]

namespace SourceGlobalEnvironment

variable {typingEnv nextEnv : TEnv} {env : PEnv} {func : Func}

theorem parameters (source : SourceGlobalEnvironment typingEnv env func) : ParameterRootsClosed func := by
  intro index root member
  exact Or.inl (by simpa only [source.parameterIdentity index, List.mem_singleton] using member)

theorem readable (source : SourceGlobalEnvironment typingEnv env func) : SourceReadableEnvironment typingEnv :=
  SourceReadableEnvironment.empty (by simpa only [source.tables.moduleEq] using source.accepted) source.variables

theorem typingTables (source : SourceGlobalEnvironment typingEnv env func)
    (moduleEq : nextEnv.mod = typingEnv.mod) (variablesEq : nextEnv.vars = typingEnv.vars)
    (modeEq : nextEnv.inExpr = typingEnv.inExpr) : SourceGlobalEnvironment nextEnv env func :=
  ⟨source.accepted, ⟨source.tables.moduleEq.trans moduleEq.symm, source.tables.variablesEq.trans variablesEq.symm⟩,
    variablesEq.trans source.variables, modeEq.trans source.inside, source.noParameters, source.parameterIdentity⟩

theorem expression (source : SourceGlobalEnvironment typingEnv env func) :
    SourceGlobalEnvironment (exprEnv typingEnv) env func :=
  ⟨source.accepted, ⟨source.tables.moduleEq, source.tables.variablesEq⟩, source.variables, rfl, source.noParameters, source.parameterIdentity⟩

theorem scopes (source : SourceGlobalEnvironment typingEnv env func) (scopes : List ScopeId) :
    SourceGlobalEnvironment typingEnv {env with scopes := scopes} func :=
  ⟨source.accepted, ⟨source.tables.moduleEq, source.tables.variablesEq⟩, source.variables, source.inside, source.noParameters, source.parameterIdentity⟩

end SourceGlobalEnvironment


theorem global_initializer_parameterRoots_identity (module : Core.Module) (global : Core.Global) :
    ∀ index, (lowerGlobal module global).init.parameterRoots index = [.param index] := by
  intro index
  simp [Func.parameterRoots, lowerGlobal]

end Goose.Lower.Validation.SummaryPreservation
