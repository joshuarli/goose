import Goose.Proofs.ConstructionAcceptedParameterSource
import Goose.Proofs.ConstructionAcceptedScalarEffects
import Goose.Proofs.ConstructionAcceptedPositions

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem checkedScalarCallArgument {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (contextId : Nat) (context : Context) (callee : Impl)
    (parameter : Param) (descriptor : LocalVar) (expression : Expr) (origin fuel : Nat)
    (compatible : SourceFrameCompatible accepted frame)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[parameter]) (mode : parameter.mode = .byValue)
    (declared : callee.vars[parameter.var]? = some descriptor)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (form : AcceptedBinaryExpression expression)
    (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (fuelEq : frame.typingFuel = fuel + 2)
    (position : SourcePosition accepted frame (.expression (.call contextId [.byVal expression] origin))) :
    ∃ roots typingAfter rootsAfter,
      CheckedValue (ordinaryOperandFrame frame fuel) expression descriptor.ty roots typingAfter rootsAfter := by
  obtain ⟨callTypes, callTypingAfter, callRoots, callRootsAfter, callTyped, callRooted⟩ :=
    position.checked accepted frame (.expression (.call contextId [.byVal expression] origin))
  have typingContext : frame.typing.module.contexts[contextId]? = some context := by
    simpa [compatible.module] using contextAt
  have typingCallee : frame.typing.module.impls[context.impl]? = some callee := by
    simpa [compatible.module] using calleeAt
  obtain ⟨argumentTy, typingAfter, typed, passing⟩ := typeExpr_call_scalarOperand fuel frame.typing contextId
    context callee parameter descriptor expression origin frame.typingCounter callTypingAfter callTypes
    typingContext typingCallee parameters mode declared (by simpa [fuelEq] using callTyped)
  have same : argumentTy = descriptor.ty := scalarParameter_passesTo_eq argumentTy descriptor.ty scalar passing
  subst argumentTy
  obtain ⟨selected, selectedCallee, allRoots, argsAfter, foundContext, foundCallee, argsChecked, contents⟩ :=
    rpExpr_call_argumentChecks callRooted
  have argument : ∃ argumentRoots argumentAfter,
      rpExpr frame.source expression frame.rootCursor = .ok (argumentRoots, argumentAfter) := by
    have args := argsChecked
    unfold rpArgs at args
    cases argumentChecked : rpExpr frame.source expression frame.rootCursor with
    | error failure => simp [argumentChecked, bind, StateT.bind, Except.bind] at args
    | ok pair => cases pair with | mk roots after => exact ⟨roots, after, rfl⟩
  obtain ⟨argumentRoots, argumentAfter, rooted⟩ := argument
  have limit : ({ frame.typing with use := .ordinary, request := .value, resultRequests := [] } : TypingEnv).globalLimit ≤
      config.module.globals.size := compatible.globals
  have argumentBounded := recursiveScalar_effects_bounded form fuel
    { frame.typing with use := .ordinary, request := .value, resultRequests := [] } frame.source
    config.module.globals.size frame.typingCounter typingAfter frame.rootCursor argumentAfter [descriptor.ty]
    argumentRoots limit bounded typed rooted
  have available : GlobalEffectsAvailable frame.interpretation frame.initialized argumentAfter.eff := by
    rw [initialized, ← compatible.globalCount]
    exact (globalEffectsAvailable_iff_bounded frame.interpretation argumentAfter.eff).2
      (by simpa only [compatible.globalCount] using argumentBounded)
  refine ⟨argumentRoots, typingAfter, argumentAfter, ?_, ?_, ?_⟩
  · simpa [ordinaryOperandFrame] using typed
  · exact rooted
  · simpa [ordinaryOperandFrame] using available

#print axioms checkedScalarCallArgument
end Goose.Proofs.ConstructionAcceptedExecution
