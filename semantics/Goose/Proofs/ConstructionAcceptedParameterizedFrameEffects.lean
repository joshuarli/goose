import Goose.Proofs.ConstructionAcceptedParameterizedCallEffects
import Goose.Proofs.ConstructionAcceptedRegisterCallCompose

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

theorem CheckedValue.singleByValue_calleeFrame_effects {config : EvalConfig} (accepted : AcceptedModule config)
    (caller calleeFrame : ConstructionSourceFrame) (target : Nat) (context : Context) (implementation : Impl)
    (parameter : Param) (expression : Expr) (activation : RuntimeActivation) (origin : Nat)
    (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (callerCompatible : SourceFrameCompatible accepted caller) (calleeCompatible : SourceFrameCompatible accepted calleeFrame)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (summary : Summary) (known : implementation.summary = .known summary)
    (noParameters : ∀ id, .param id ∉ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks)
    (phase : calleeFrame.phase = .implementation target) (implementationEq : calleeFrame.source.impl = implementation)
    (initialized : calleeFrame.initialized = caller.initialized) (bodyFrame : implementationBodyFrame config calleeFrame = calleeFrame)
    (checked : CheckedValue caller (.call target [.byVal expression] origin) ty roots typingAfter rootsAfter) :
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
  obtain ⟨argumentRoots, middle, bodyContext, actualEscapes, value, state, arguments, closed', targets', rooted', available⟩ :=
    checkedValue_singleByValue_summaryAvailable config caller target origin context implementation parameter expression ty roots typingAfter rootsAfter
      contextAt implementationAt callerCompatible.rootModule parameters checked calleeFrame.source.aliases calls
      calleeFrame.source.escaping calleeFrame.source.calleeNames facts summary known activation noParameters
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
  have cursor : calleeFrame.rootCursor = ⟨implementation.params.size, {}, []⟩ := by
    have equal := congrArg (fun f : ConstructionSourceFrame => f.rootCursor) bodyFrame
    simpa [implementationBodyFrame, sourceImpl] using equal.symm
  have sourceEqual : { mod := config.module, impl := implementation, ctx := calleeFrame.source.ctx, scopes := [], escaping := calleeFrame.source.escaping, targetEscapes := calleeFrame.source.targetEscapes, aliases := calleeFrame.source.aliases, calleeNames := calleeFrame.source.calleeNames } = calleeFrame.source := by
    cases h : calleeFrame.source
    simp_all
  have actualRooted : rpBlockValue calleeFrame.source [] calleeFrame.source.impl.body calleeFrame.rootCursor = .ok (value, state) := by
    simpa [sourceEqual, sourceImpl, cursor] using rooted'
  intro result after checkedRoot
  have same := Prod.mk.inj (Except.ok.inj (checkedRoot.symm.trans actualRooted))
  rw [same.2, initialized]
  exact available calleeFrame.interpretation

theorem acceptedSingleByValueCalleeSource (config : EvalConfig) (accepted : AcceptedModule config)
    (caller : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes) (target origin : Nat)
    (context : Context) (implementation : Impl) (parameter : Param) (expression : Expr) (channels : List Channel)
    (source : AcceptedFrame config accepted caller state types)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (summary : Summary) (known : implementation.summary = .known summary)
    (noParameters : ∀ id, .param id ∉ summary.reads ++ summary.writes ++ summary.grows ++ summary.shrinks)
    (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue caller (.call target [.byVal expression] origin) ty roots typingAfter rootsAfter) :
    ∃ argumentRoots middle frame,
      rpArgs caller.source [.byVal expression] caller.rootCursor = .ok (argumentRoots, middle) ∧
      frame.phase = .implementation target ∧ frame.source.impl = implementation ∧ frame.initialized = caller.initialized ∧
      frame.interpretation = CallInterpretation caller.interpretation
        ⟨context.impl, state.nextAct, implementation.vars, [], channels⟩ argumentRoots ∧
      implementationBodyFrame config frame = frame ∧ SourceFrameCompatible accepted frame ∧
      SourcePosition accepted frame (.block implementation.body) ∧
      (∀ result after, rpBlockValue frame.source [] implementation.body frame.rootCursor = .ok (result, after) →
        GlobalEffectsAvailable frame.interpretation frame.initialized after.eff) := by
  obtain ⟨argumentRoots, middle, arguments, available⟩ := checked.singleByValue_callEffectsAvailable config caller target origin context implementation
    parameter expression ty roots typingAfter rootsAfter contextAt implementationAt source.compatible.rootModule parameters
  obtain ⟨frame, phase, impl, aliases, interpretation, initialized, bodyFrame, compatible, fresh, frontier⟩ :=
    acceptedCalleeSourceFrame config accepted caller state target context implementation argumentRoots channels source.compatible source.frontier
      contextAt implementationAt
  have position : SourcePosition accepted frame (.block implementation.body) := by
    have position := SourcePosition.implementationBody frame target phase compatible
    simpa [bodyFrame, impl] using position
  have effects := checked.singleByValue_calleeFrame_effects accepted caller frame target context implementation parameter expression
    ⟨context.impl, state.nextAct, implementation.vars, [], channels⟩ origin ty roots typingAfter rootsAfter source.compatible compatible
    contextAt implementationAt parameters summary known noParameters phase impl initialized bodyFrame
  refine ⟨argumentRoots, middle, frame, arguments, phase, impl, initialized, interpretation, bodyFrame, compatible, position, ?_⟩
  intro result after checkedBody
  exact effects result after (by simpa [impl] using checkedBody)

#print axioms acceptedSingleByValueCalleeSource
#print axioms CheckedValue.singleByValue_calleeFrame_effects
end Goose.Proofs.ConstructionAcceptedExecution
