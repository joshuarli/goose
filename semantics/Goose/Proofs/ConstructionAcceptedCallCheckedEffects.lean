import Goose.Proofs.ConstructionAcceptedCallEffects
import Goose.Proofs.ConstructionRootCorrespondenceCursors

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem rpExpr_zeroArgument_access {env : PEnv} {target : Goose.Core.ContextId} {context : Context} {callee : Impl}
    {before after : RState} {roots : List RootRef} {origin : Nat}
    (contextAt : env.mod.contexts[target]? = some context) (calleeAt : env.mod.impls[context.impl]? = some callee)
    (parameters : callee.params = #[])
    (checked : rpExpr env (.call target [] origin) before = .ok (roots, after)) :
    EffectTargetsIncluded (callEffects callee context [] {}) after.eff := by
  unfold rpExpr at checked
  simp only [rpArgs, pure, StateT.pure, Except.pure, bind, StateT.bind, Except.bind, contextAt, calleeAt,
    parameters, Array.toList_empty, List.zip, List.zipWith, List.forIn_nil] at checked
  cases content : checkContents env target [] [] with
  | error failure => simp [content, liftV] at checked
  | ok result =>
    cases result
    simp only [content, liftV] at checked
    split at checked
    · simp only [bind, StateT.bind] at checked
      cases updated : noteResultConstruction env before with
      | error failure => simp [updated, Except.bind] at checked
      | ok pair =>
        have call : rpCall env target [] pair.2 = .ok (roots, after) := by
          simpa [updated, Except.bind] using checked
        exact rpCall_zeroArgument_access contextAt calleeAt call
    · exact rpCall_zeroArgument_access contextAt calleeAt checked
theorem checkedValue_zeroArgument_bodyAvailable (config : EvalConfig) (caller : ConstructionSourceFrame)
    (target : Goose.Core.ContextId) (context : Context) (callee : Impl) (origin : Nat)
    (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (contextAt : config.module.contexts[target]? = some context) (calleeAt : config.module.impls[context.impl]? = some callee)
    (sourceModule : caller.source.mod = config.module) (parameters : callee.params = #[])
    (checked : CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter)
    (aliases : List (RootRef × RootRef)) (calls : List (Goose.Core.ContextId × List (List RootRef)))
    (escaping : Array (List (Nat × List (List RootRef)))) (names : Array (List RootRef))
    (facts : ContextRootFactsAt config.module context aliases calls escaping names)
    (summary : Summary) (known : callee.summary = .known summary) (activation : RuntimeActivation) :
    ∃ bodyContext actualEscapes value state,
      parameterBodyRootContext config.module callee context = .ok bodyContext ∧
      bodyTargets config.module = .ok actualEscapes ∧
      rpBlockValue { mod := config.module, impl := callee, ctx := bodyContext, scopes := [], escaping := escaping, targetEscapes := actualEscapes, aliases := aliases, calleeNames := names }
        [] callee.body ⟨callee.params.size, {}, []⟩ = .ok (value, state) ∧
      GlobalEffectsAvailable (Goose.Proofs.ConstructionRootCorrespondence.CallInterpretation caller.interpretation activation []) caller.initialized state.eff := by
  have callerContext : caller.source.mod.contexts[target]? = some context := by rw [sourceModule]; exact contextAt
  have callerCallee : caller.source.mod.impls[context.impl]? = some callee := by rw [sourceModule]; exact calleeAt
  have included := rpExpr_zeroArgument_access callerContext callerCallee parameters checked.provenance
  have available : GlobalEffectsAvailable caller.interpretation caller.initialized (callEffects callee context [] {}) := by
    intro target member global instantiated
    exact checked.available target (included member) global instantiated
  exact contextRootFactsAt_zeroArgument_bodyAvailable config.module context callee aliases calls escaping names facts calleeAt
    summary known parameters {} caller.interpretation activation caller.initialized available

theorem CheckedValue.zeroArgument_calleeFrame_effects {config : EvalConfig} (accepted : AcceptedModule config)
    (caller calleeFrame : ConstructionSourceFrame) (target : Nat) (context : Context) (implementation : Impl)
    (activation : RuntimeActivation) (origin : Nat) (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (callerCompatible : SourceFrameCompatible accepted caller) (calleeCompatible : SourceFrameCompatible accepted calleeFrame)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[]) (summary : Summary) (known : implementation.summary = .known summary)
    (phase : calleeFrame.phase = .implementation target) (implementationEq : calleeFrame.source.impl = implementation)
    (interpretation : calleeFrame.interpretation = Goose.Proofs.ConstructionRootCorrespondence.CallInterpretation caller.interpretation activation [])
    (initialized : calleeFrame.initialized = caller.initialized) (bodyFrame : implementationBodyFrame config calleeFrame = calleeFrame)
    (checked : CheckedValue caller (.call target [] origin) ty roots typingAfter rootsAfter) :
    ∀ result after, rpBlockValue calleeFrame.source [] calleeFrame.source.impl.body calleeFrame.rootCursor = .ok (result, after) →
      GlobalEffectsAvailable calleeFrame.interpretation calleeFrame.initialized after.eff := by
  have originFact := calleeCompatible.origin
  unfold SourceOrigin at originFact
  rw [phase] at originFact
  obtain ⟨original, calls, originalAt, implAt, environment, typing, closed, aliasesEq, facts, covered, targets, rootedValue, rootedAfter, rooted⟩ := originFact
  have sameContext : original = context := Option.some.inj (originalAt.symm.trans contextAt)
  subst original
  have sourceModule := calleeCompatible.rootModule
  have sourceImpl := implementationEq
  obtain ⟨bodyContext, actualEscapes, value, state, closed', targets', rooted', available⟩ :=
    checkedValue_zeroArgument_bodyAvailable config caller target context implementation origin ty roots typingAfter rootsAfter
      contextAt implementationAt callerCompatible.rootModule parameters checked calleeFrame.source.aliases calls
      calleeFrame.source.escaping calleeFrame.source.calleeNames facts summary known activation
  rw [implementationEq] at closed
  have sameContext : bodyContext = calleeFrame.source.ctx := Except.ok.inj (closed'.symm.trans closed)
  have sameEscapes : actualEscapes = calleeFrame.source.targetEscapes := Except.ok.inj (targets'.symm.trans targets)
  subst bodyContext actualEscapes
  have sourceScopes : calleeFrame.source.scopes = [] := by
    have equal := congrArg (fun f : ConstructionSourceFrame => f.source.scopes) bodyFrame
    simpa [implementationBodyFrame] using equal.symm
  have sourceValue : calleeFrame.source.valueBlock = none := by
    have equal := congrArg (fun f : ConstructionSourceFrame => f.source.valueBlock) bodyFrame
    simpa [implementationBodyFrame] using equal.symm
  have sourceInitializing : calleeFrame.source.initializing = [] := by
    have equal := congrArg (fun f : ConstructionSourceFrame => f.source.initializing) bodyFrame
    simpa [implementationBodyFrame] using equal.symm
  have cursor : calleeFrame.rootCursor = ⟨0, {}, []⟩ := by
    have equal := congrArg (fun f : ConstructionSourceFrame => f.rootCursor) bodyFrame
    simpa [implementationBodyFrame, sourceImpl, parameters] using equal.symm
  have sourceEqual : { mod := config.module, impl := implementation, ctx := calleeFrame.source.ctx, scopes := [], escaping := calleeFrame.source.escaping, targetEscapes := calleeFrame.source.targetEscapes, aliases := calleeFrame.source.aliases, calleeNames := calleeFrame.source.calleeNames } = calleeFrame.source := by
    cases h : calleeFrame.source
    simp_all
  have actualRooted : rpBlockValue calleeFrame.source [] calleeFrame.source.impl.body calleeFrame.rootCursor = .ok (value, state) := by
    simpa [sourceEqual, sourceImpl, cursor, parameters] using rooted'
  intro result after checkedRoot
  have same := Prod.mk.inj (Except.ok.inj (checkedRoot.symm.trans actualRooted))
  rw [same.2]
  simpa [interpretation, initialized] using available

#print axioms CheckedValue.zeroArgument_calleeFrame_effects
#print axioms checkedValue_zeroArgument_bodyAvailable
#print axioms rpExpr_zeroArgument_access
end Goose.Proofs.ConstructionAcceptedExecution
