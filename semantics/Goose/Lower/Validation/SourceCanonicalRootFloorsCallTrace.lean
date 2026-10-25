import Goose.Lower.Validation.SourceCanonicalRootFloorsInduction
import Goose.Lower.Validation.SourceCanonicalRootFloorsContextFacts
import Goose.Lower.Validation.SourceCanonicalRootFloorsGlobalFacts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceCallTrace

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource

theorem callArgumentsTrace_canonical_floor {env : PEnv} {func : Func}
    (tables : SourceCanonicalTables env func) {syntaxArgs : List Arg} {args : List ValueId}
    {calleeId : FnId} {origin : OriginId}
    (trace : CallArgumentsTrace env syntaxArgs args func calleeId origin)
    {before after : RState} {argumentRoots : List (List RootRef)}
    (replayed : rpArgs env syntaxArgs before = .ok (argumentRoots, after)) :
    ∀ (index : Nat) (roots : List RootRef), argumentRoots[index]? = some roots →
      ∃ value, args[index]? = some value ∧ roots ⊆ canonicalValueRoots env func value := by
  obtain ⟨returnTypes, initial, final, siteRoot, sourcePath, run, generated, live, continuation,
    location, valid, projects, typing, start, finish, type, moduleEq, variablesEq, source⟩ := trace
  have sourceTables : SourceRootTables typing env := ⟨moduleEq.symm, variablesEq.symm⟩
  have typedRun : lowerArgs syntaxArgs (lowerEnv typing.mod typing.vars returnTypes) initial = (args, final) := by
    simpa only [moduleEq, variablesEq] using run
  obtain ⟨context, callee, argsStart, argsFinish, resultStart, contextAt, calleeAt,
    arity, argumentsSource, resultSource⟩ := tyExpr_call_tables source
  have locations : ∀ (index : Nat) (argument : Arg), syntaxArgs[index]? = some argument →
      ∃ path, DemandNodeAt siteRoot path (argumentSourceNode argument) := by
    intro index argument present
    refine ⟨sourcePath ++ [index], location.snoc index ?_⟩
    cases argument <;> simp [DemandNode.child?, DemandNode.children, present, argumentSourceNode]
  exact arguments_canonical_floor syntaxArgs tables sourceTables valid locations arity argumentsSource
    replayed typedRun generated live continuation projects

theorem lowerContext_callArgumentsTrace_canonical_floor {module : Core.Module} {context : Context} {impl : Impl}
    {contextId : ContextId} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[contextId]? = some context) (implAt : module.impls[context.impl]? = some impl)
    (scopes : List ScopeId) {syntaxArgs : List Arg} {args : List ValueId} {calleeId : FnId} {origin : OriginId}
    (trace : CallArgumentsTrace ⟨module, impl, context, scopes⟩ syntaxArgs args
      (lowerContextAt module context impl) calleeId origin)
    {before after : RState} {argumentRoots : List (List RootRef)}
    (replayed : rpArgs ⟨module, impl, context, scopes⟩ syntaxArgs before = .ok (argumentRoots, after)) :
    ∀ (index : Nat) (roots : List RootRef), argumentRoots[index]? = some roots →
      ∃ value, args[index]? = some value ∧
        roots ⊆ canonicalValueRoots ⟨module, impl, context, scopes⟩ (lowerContextAt module context impl) value :=
  callArgumentsTrace_canonical_floor (sourceCanonicalTables_context accepted contextAt implAt scopes) trace replayed

theorem lowerGlobal_callArgumentsTrace_canonical_floor {module : Core.Module} {global : Core.Global}
    {globalId : GlobalId} (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[globalId]? = some global) (scopes : List ScopeId)
    {syntaxArgs : List Arg} {args : List ValueId} {calleeId : FnId} {origin : OriginId}
    (trace : CallArgumentsTrace ⟨module, initImpl, initContext, scopes⟩ syntaxArgs args
      (lowerGlobal module global).init calleeId origin)
    {before after : RState} {argumentRoots : List (List RootRef)}
    (replayed : rpArgs ⟨module, initImpl, initContext, scopes⟩ syntaxArgs before = .ok (argumentRoots, after)) :
    ∀ (index : Nat) (roots : List RootRef), argumentRoots[index]? = some roots →
      ∃ value, args[index]? = some value ∧ roots ⊆
        canonicalValueRoots ⟨module, initImpl, initContext, scopes⟩ (lowerGlobal module global).init value :=
  callArgumentsTrace_canonical_floor (sourceCanonicalTables_global accepted globalAt scopes) trace replayed

end Goose.Lower.Validation.SourceCanonicalRootFloors
