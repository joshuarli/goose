import Goose.Proofs.ConstructionAcceptedScalarLocalParameterEffects
import Goose.Proofs.ConstructionAcceptedParameterizedBodyFrameEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

theorem CheckedValue.singleByValue_scalarLocalRecursiveBody_effects {config : EvalConfig} (accepted : AcceptedModule config)
    (caller calleeFrame : ConstructionSourceFrame) (target : Nat) (context : Context) (implementation : Impl)
    (parameter : Param) (expression : Expr) (activation : RuntimeActivation) (origin : Nat)
    (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (callerCompatible : SourceFrameCompatible accepted caller) (calleeCompatible : SourceFrameCompatible accepted calleeFrame)
    (contextAt : config.module.contexts[target]? = some context)
    (implementationAt : config.module.impls[context.impl]? = some implementation)
    (parameters : implementation.params = #[parameter]) (summary : Summary) (known : implementation.summary = .known summary)
    (tailTarget tailOrigin : Nat) (statements : List Stmt) (argument : Expr) (integer : Goose.Core.IntTy)
    (tailContext : Context) (tailCallee : Impl) (tailParameter : Param) (tailSummary : Summary)
    (body : implementation.body = ⟨implementation.body.scope, statements, some (.call tailTarget [.byVal argument] tailOrigin)⟩)
    (statementsForm : ScalarLocalStatements statements) (argumentForm : RecursiveArgumentExpression config integer implementation argument)
    (tailContextAt : config.module.contexts[tailTarget]? = some tailContext)
    (tailCalleeAt : config.module.impls[tailContext.impl]? = some tailCallee)
    (tailParameters : tailCallee.params = #[tailParameter]) (tailKnown : tailCallee.summary = .known tailSummary)
    (scalar : ∀ id initializer location, .letS id initializer location ∈ statements → ∀ descriptor,
      implementation.vars[id]? = some descriptor → (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (phase : calleeFrame.phase = .implementation target) (implementationEq : calleeFrame.source.impl = implementation)
    (initialized : calleeFrame.initialized = caller.initialized)
    (checked : CheckedValue caller (.call target [.byVal expression] origin) ty roots typingAfter rootsAfter) :
    ∀ result after, rpBlockValue (implementationBodyFrame config calleeFrame).source [] implementation.body
      (implementationBodyFrame config calleeFrame).rootCursor = .ok (result, after) →
      GlobalEffectsAvailable calleeFrame.interpretation calleeFrame.initialized after.eff := by
  apply checked.singleByValue_normalizedBody_effects_noParameterBody accepted caller calleeFrame target context implementation parameter expression
    activation origin ty roots typingAfter rootsAfter callerCompatible calleeCompatible contextAt implementationAt parameters summary known
  · intro bodyContext actualEscapes result state closed targets rooted id
    rw [body] at rooted
    have clear : NoParameterAccess ({} : Eff) := by simp [NoParameterAccess, Eff.accessTargets]
    exact scalarLocalRecursiveTail_noParameter config integer implementation _ implementation.body.scope tailTarget tailOrigin statements argument
      tailContext tailCallee tailParameter tailSummary _ state result statementsForm argumentForm rfl rfl tailContextAt tailCalleeAt
      tailParameters tailKnown scalar clear rooted id
  · exact phase
  · exact implementationEq
  · exact initialized

#print axioms CheckedValue.singleByValue_scalarLocalRecursiveBody_effects
end Goose.Proofs.ConstructionAcceptedExecution
