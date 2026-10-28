import Goose.Proofs.ConstructionAcceptedArgumentTargets
import Goose.Proofs.ConstructionAcceptedCallCheckedEffects
import Goose.Proofs.ConstructionAcceptedArgumentPrefixPosition

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem rpExpr_singleByValue_access {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {parameter : Param} {expression : Expr} {before middle after : RState} {roots : List RootRef}
    {argumentRoots : List (List RootRef)} {origin : Nat}
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter])
    (arguments : rpArgs env [.byVal expression] before = .ok (argumentRoots, middle))
    (checked : rpExpr env (.call target [.byVal expression] origin) before = .ok (roots, after)) :
    EffectTargetsIncluded (callEffects callee context argumentRoots {}) after.eff := by
  unfold rpExpr at checked
  simp only [arguments, bind, StateT.bind, Except.bind, contextAt, calleeAt, parameters,
    List.zip, List.zipWith, List.forIn_cons, List.forIn_nil, pure, StateT.pure, Except.pure] at checked
  cases content : checkContents env target [.byVal expression] argumentRoots with
  | error failure => simp [content, liftV] at checked
  | ok result =>
    cases result
    simp only [content, liftV] at checked
    split at checked
    · simp only [bind, StateT.bind] at checked
      cases updated : noteResultConstruction env middle with
      | error failure => simp [updated, Except.bind] at checked
      | ok pair =>
        have call : rpCall env target argumentRoots pair.2 = .ok (roots, after) := by
          simpa [updated, Except.bind] using checked
        exact rpCall_access argumentRoots contextAt calleeAt call
    · exact rpCall_access argumentRoots contextAt calleeAt checked

theorem CheckedValue.singleByValue_callEffectsAvailable (config : EvalConfig) (caller : ConstructionSourceFrame)
    (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (expression : Expr)
    (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (sourceModule : caller.source.mod = config.module) (parameters : callee.params = #[parameter])
    (checked : CheckedValue caller (.call target [.byVal expression] origin) ty roots typingAfter rootsAfter) :
    ∃ argumentRoots middle,
      rpArgs caller.source [.byVal expression] caller.rootCursor = .ok (argumentRoots, middle) ∧
      GlobalEffectsAvailable caller.interpretation caller.initialized (callEffects callee context argumentRoots {}) := by
  have callerContext : caller.source.mod.contexts[target]? = some context := by rw [sourceModule]; exact contextAt
  have callerCallee : caller.source.mod.impls[context.impl]? = some callee := by rw [sourceModule]; exact calleeAt
  obtain ⟨selected, selectedCallee, argumentRoots, middle, selectedAt, selectedCalleeAt, arguments, contents⟩ :=
    rpExpr_call_argumentChecks checked.provenance
  have sameContext : selected = context := Option.some.inj (selectedAt.symm.trans callerContext)
  subst selected
  have sameCallee : selectedCallee = callee := Option.some.inj (selectedCalleeAt.symm.trans callerCallee)
  subst selectedCallee
  have included := rpExpr_singleByValue_access callerContext callerCallee parameters arguments checked.provenance
  refine ⟨argumentRoots, middle, arguments, ?_⟩
  intro effect member global instantiated
  exact checked.available effect (included member) global instantiated

theorem checkedValue_singleByValue_bodyGlobals (config : EvalConfig) (caller : ConstructionSourceFrame)
    (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (expression : Expr)
    (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (sourceModule : caller.source.mod = config.module) (parameters : callee.params = #[parameter])
    (checked : CheckedValue caller (.call target [.byVal expression] origin) ty roots typingAfter rootsAfter)
    (aliases : List (RootRef × RootRef)) (calls : List (Goose.Core.ContextId × List (List RootRef)))
    (escaping : Array (List (Nat × List (List RootRef)))) (names : Array (List RootRef))
    (facts : ContextRootFactsAt config.module context aliases calls escaping names)
    (summary : Summary) (known : callee.summary = .known summary) :
    ∃ argumentRoots middle bodyContext actualEscapes value state,
      rpArgs caller.source [.byVal expression] caller.rootCursor = .ok (argumentRoots, middle) ∧
      parameterBodyRootContext config.module callee context = .ok bodyContext ∧ bodyTargets config.module = .ok actualEscapes ∧
      rpBlockValue { mod := config.module, impl := callee, ctx := bodyContext, scopes := [], escaping := escaping, targetEscapes := actualEscapes, aliases := aliases, calleeNames := names }
        [] callee.body ⟨callee.params.size, {}, []⟩ = .ok (value, state) ∧
      ∀ global, .global global ∈ state.eff.accessTargets → global < caller.initialized := by
  obtain ⟨argumentRoots, middle, arguments, available⟩ := checked.singleByValue_callEffectsAvailable config caller target origin context callee
    parameter expression ty roots typingAfter rootsAfter contextAt calleeAt sourceModule parameters
  obtain ⟨bodyContext, actualEscapes, value, state, closed, targets, rooted, globals⟩ :=
    contextRootFactsAt_parameterized_globalAvailable config.module context callee aliases calls escaping names facts calleeAt summary known
      argumentRoots {} caller.interpretation caller.initialized available
  exact ⟨argumentRoots, middle, bodyContext, actualEscapes, value, state, arguments, closed, targets, rooted, globals⟩

theorem checkedValue_singleByValue_bodyAvailable (config : EvalConfig) (caller : ConstructionSourceFrame)
    (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (expression : Expr)
    (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (sourceModule : caller.source.mod = config.module) (parameters : callee.params = #[parameter])
    (checked : CheckedValue caller (.call target [.byVal expression] origin) ty roots typingAfter rootsAfter)
    (aliases : List (RootRef × RootRef)) (calls : List (Goose.Core.ContextId × List (List RootRef)))
    (escaping : Array (List (Nat × List (List RootRef)))) (names : Array (List RootRef))
    (facts : ContextRootFactsAt config.module context aliases calls escaping names)
    (summary : Summary) (known : callee.summary = .known summary) (activation : RuntimeActivation)
    (noParameterEffects : ∀ bodyContext actualEscapes value state,
      parameterBodyRootContext config.module callee context = .ok bodyContext → bodyTargets config.module = .ok actualEscapes →
      rpBlockValue { mod := config.module, impl := callee, ctx := bodyContext, scopes := [], escaping := escaping, targetEscapes := actualEscapes, aliases := aliases, calleeNames := names }
        [] callee.body ⟨callee.params.size, {}, []⟩ = .ok (value, state) →
      ∀ id, .param id ∉ state.eff.accessTargets) :
    ∃ argumentRoots middle bodyContext actualEscapes value state,
      rpArgs caller.source [.byVal expression] caller.rootCursor = .ok (argumentRoots, middle) ∧
      parameterBodyRootContext config.module callee context = .ok bodyContext ∧ bodyTargets config.module = .ok actualEscapes ∧
      rpBlockValue { mod := config.module, impl := callee, ctx := bodyContext, scopes := [], escaping := escaping, targetEscapes := actualEscapes, aliases := aliases, calleeNames := names }
        [] callee.body ⟨callee.params.size, {}, []⟩ = .ok (value, state) ∧
      GlobalEffectsAvailable (CallInterpretation caller.interpretation activation argumentRoots) caller.initialized state.eff := by
  obtain ⟨argumentRoots, middle, arguments, available⟩ := checked.singleByValue_callEffectsAvailable config caller target origin context callee
    parameter expression ty roots typingAfter rootsAfter contextAt calleeAt sourceModule parameters
  obtain ⟨bodyContext, actualEscapes, value, state, closed, targets, rooted, effectsAvailable⟩ :=
    contextRootFactsAt_parameterized_bodyAvailable config.module context callee aliases calls escaping names facts calleeAt summary known
      argumentRoots {} caller.interpretation activation caller.initialized available noParameterEffects
  exact ⟨argumentRoots, middle, bodyContext, actualEscapes, value, state, arguments, closed, targets, rooted, effectsAvailable⟩

theorem checkedValue_singleByValue_summaryAvailable (config : EvalConfig) (caller : ConstructionSourceFrame)
    (target origin : Nat) (context : Context) (callee : Impl) (parameter : Param) (expression : Expr)
    (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (sourceModule : caller.source.mod = config.module) (parameters : callee.params = #[parameter])
    (checked : CheckedValue caller (.call target [.byVal expression] origin) ty roots typingAfter rootsAfter)
    (aliases : List (RootRef × RootRef)) (calls : List (Goose.Core.ContextId × List (List RootRef)))
    (escaping : Array (List (Nat × List (List RootRef)))) (names : Array (List RootRef))
    (facts : ContextRootFactsAt config.module context aliases calls escaping names)
    (summary : Summary) (known : callee.summary = .known summary) (activation : RuntimeActivation)
    (noParameters : ∀ id, .param id ∉ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks) :
    ∃ argumentRoots middle bodyContext actualEscapes value state,
      rpArgs caller.source [.byVal expression] caller.rootCursor = .ok (argumentRoots, middle) ∧
      parameterBodyRootContext config.module callee context = .ok bodyContext ∧ bodyTargets config.module = .ok actualEscapes ∧
      rpBlockValue { mod := config.module, impl := callee, ctx := bodyContext, scopes := [], escaping := escaping, targetEscapes := actualEscapes, aliases := aliases, calleeNames := names }
        [] callee.body ⟨callee.params.size, {}, []⟩ = .ok (value, state) ∧
      ∀ interpretation, GlobalEffectsAvailable interpretation caller.initialized state.eff := by
  obtain ⟨argumentRoots, middle, arguments, available⟩ := checked.singleByValue_callEffectsAvailable config caller target origin context callee
    parameter expression ty roots typingAfter rootsAfter contextAt calleeAt sourceModule parameters
  obtain ⟨bodyContext, actualEscapes, value, state, closed, targets, rooted, effectsAvailable⟩ :=
    contextRootFactsAt_parameterized_summaryAvailable config.module context callee aliases calls escaping names facts calleeAt summary known
      noParameters argumentRoots {} caller.interpretation activation caller.initialized available
  refine ⟨argumentRoots, middle, bodyContext, actualEscapes, value, state, arguments, closed, targets, rooted, ?_⟩
  intro interpretation
  exact effectsAvailable.1.retarget_noParameters _ interpretation caller.initialized state.eff effectsAvailable.2

#print axioms checkedValue_singleByValue_summaryAvailable
#print axioms checkedValue_singleByValue_bodyAvailable
#print axioms checkedValue_singleByValue_bodyGlobals
#print axioms CheckedValue.singleByValue_callEffectsAvailable
#print axioms rpExpr_singleByValue_access
end Goose.Proofs.ConstructionAcceptedExecution
