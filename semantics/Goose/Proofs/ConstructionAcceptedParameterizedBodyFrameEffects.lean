import Goose.Proofs.ConstructionAcceptedParameterizedFrameEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

theorem CheckedValue.singleByValue_normalizedBody_effects_noParameterBody {config : EvalConfig} (accepted : AcceptedModule config)
    (caller calleeFrame : ConstructionSourceFrame) (target : Nat) (context : Context) (implementation : Impl)
    (parameter : Param) (expression : Expr) (activation : RuntimeActivation) (origin : Nat)
    (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (callerCompatible : SourceFrameCompatible accepted caller) (calleeCompatible : SourceFrameCompatible accepted calleeFrame)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (summary : Summary) (known : implementation.summary = .known summary)
    (noParameterEffects : ∀ bodyContext actualEscapes value state,
      parameterBodyRootContext config.module implementation context = .ok bodyContext →
      bodyTargets config.module = .ok actualEscapes →
      rpBlockValue { mod := config.module, impl := implementation, ctx := bodyContext, scopes := [], escaping := calleeFrame.source.escaping, targetEscapes := actualEscapes, aliases := calleeFrame.source.aliases, calleeNames := calleeFrame.source.calleeNames }
        [] implementation.body ⟨implementation.params.size, {}, []⟩ = .ok (value, state) →
      ∀ id, .param id ∉ state.eff.accessTargets)
    (phase : calleeFrame.phase = .implementation target) (implementationEq : calleeFrame.source.impl = implementation)
    (initialized : calleeFrame.initialized = caller.initialized)
    (checked : CheckedValue caller (.call target [.byVal expression] origin) ty roots typingAfter rootsAfter) :
    ∀ result after, rpBlockValue (implementationBodyFrame config calleeFrame).source [] implementation.body
      (implementationBodyFrame config calleeFrame).rootCursor = .ok (result, after) →
      GlobalEffectsAvailable calleeFrame.interpretation calleeFrame.initialized after.eff := by
  have originFact := calleeCompatible.origin
  unfold SourceOrigin at originFact
  rw [phase] at originFact
  obtain ⟨original, calls, originalAt, implAt, environment, typing, closed, aliasesEq, facts, covered, targets, rootedValue, rootedAfter, rooted⟩ := originFact
  have sameContext : original = context := Option.some.inj (originalAt.symm.trans contextAt)
  subst original
  have sourceModule := calleeCompatible.rootModule
  have sourceImpl := implementationEq
  obtain ⟨argumentRoots, middle, bodyContext, actualEscapes, value, state, arguments, closed', targets', rooted', available⟩ :=
    checkedValue_singleByValue_bodyAvailable config caller target origin context implementation parameter expression ty roots typingAfter rootsAfter
      contextAt implementationAt callerCompatible.rootModule parameters checked calleeFrame.source.aliases calls
      calleeFrame.source.escaping calleeFrame.source.calleeNames facts summary known activation noParameterEffects
  have noBodyParams := noParameterEffects bodyContext actualEscapes value state closed' targets' rooted'
  rw [implementationEq] at closed
  have sameContext : bodyContext = calleeFrame.source.ctx := Except.ok.inj (closed'.symm.trans closed)
  have sameEscapes : actualEscapes = calleeFrame.source.targetEscapes := Except.ok.inj (targets'.symm.trans targets)
  subst bodyContext actualEscapes
  have sourceEqual : { mod := config.module, impl := implementation, ctx := calleeFrame.source.ctx, scopes := [], escaping := calleeFrame.source.escaping, targetEscapes := calleeFrame.source.targetEscapes, aliases := calleeFrame.source.aliases, calleeNames := calleeFrame.source.calleeNames } = (implementationBodyFrame config calleeFrame).source := by
    cases h : calleeFrame.source
    simp_all [implementationBodyFrame]
  have actualRooted : rpBlockValue (implementationBodyFrame config calleeFrame).source [] implementation.body
      (implementationBodyFrame config calleeFrame).rootCursor = .ok (value, state) := by
    simpa [sourceEqual, implementationBodyFrame, sourceImpl] using rooted'
  intro result after checkedRoot
  have same := Prod.mk.inj (Except.ok.inj (checkedRoot.symm.trans actualRooted))
  rw [same.2, initialized]
  exact available.retarget_noParameters _ calleeFrame.interpretation caller.initialized state.eff noBodyParams

#print axioms CheckedValue.singleByValue_normalizedBody_effects_noParameterBody
end Goose.Proofs.ConstructionAcceptedExecution
