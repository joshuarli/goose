import Goose.Proofs.ConstructionAcceptedStatefulBlockCursors
import Goose.Proofs.ConstructionAcceptedTwoArgumentPosition
import Goose.Proofs.ConstructionAcceptedScalarEffects

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

def secondStatefulArgumentFrame (frame : ConstructionSourceFrame) (fuel : Nat) (leftAfter : RState) : ConstructionSourceFrame :=
  { ordinaryOperandFrame frame fuel with rootCursor := { leftAfter with eff := {} } }

theorem checkedStatefulCallArguments {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes) (checkFuel contextId callOrigin : Nat)
    (context : Context) (callee : Impl) (first second : Param) (firstDescriptor secondDescriptor : LocalVar)
    (scope id origin blockOrigin : Nat) (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int) (right : Expr)
    (form : AcceptedBinaryExpression expression) (rightForm : AcceptedBinaryExpression right)
    (source : AcceptedFrame config accepted frame state types)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[first, second])
    (firstMode : first.mode = .byValue) (secondMode : second.mode = .byValue)
    (firstDeclared : callee.vars[first.var]? = some firstDescriptor)
    (secondDeclared : callee.vars[second.var]? = some secondDescriptor)
    (firstScalar : (∃ t, firstDescriptor.ty = .int t) ∨ firstDescriptor.ty = .bool)
    (secondScalar : (∃ t, secondDescriptor.ty = .int t) ∨ secondDescriptor.ty = .bool)
    (initialized : frame.initialized = config.module.globals.size)
    (fresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ scope)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (nesting : frame.typingFuel = checkFuel + 6)
    (position : SourcePosition accepted frame (.expression (.call contextId
      [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] callOrigin))) :
    ∃ leftAfter rightRoots rightTypingAfter rightAfter,
      leftAfter.nextVar = frame.rootCursor.nextVar ∧
      SourcePosition accepted (ordinaryOperandFrame frame (checkFuel + 4)) (.expression (.blockE
        ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin)) ∧
      CheckedValue (secondStatefulArgumentFrame frame (checkFuel + 3) leftAfter) right secondDescriptor.ty
        rightRoots rightTypingAfter rightAfter := by
  let left : Expr := .blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin
  have firstPosition := position.twoArgumentFirst accepted frame (checkFuel + 3) contextId callOrigin context callee
    first second firstDescriptor secondDescriptor left right source.compatible contextAt calleeAt parameters firstMode secondMode
    firstDeclared secondDeclared firstScalar secondScalar (by simpa [Nat.add_assoc] using nesting)
  obtain ⟨callTypes, callTypingAfter, callRoots, callRootsAfter, callTyped, callRooted⟩ := position.checked accepted frame _
  rw [nesting] at callTyped
  have typedContext : frame.typing.module.contexts[contextId]? = some context := by simpa [source.compatible.module] using contextAt
  have typedCallee : frame.typing.module.impls[context.impl]? = some callee := by simpa [source.compatible.module] using calleeAt
  obtain ⟨firstAfter, rightTypingAfter, firstTyped, rightTyped⟩ := typeExpr_twoScalarCall_operands (checkFuel + 3)
    frame.typing contextId callOrigin context callee first second firstDescriptor secondDescriptor left right
    frame.typingCounter callTypingAfter callTypes typedContext typedCallee parameters firstMode secondMode firstDeclared secondDeclared
    firstScalar secondScalar (by simpa [left, Nat.add_assoc] using callTyped)
  obtain ⟨selected, selectedCallee, allRoots, argsAfter, foundContext, foundCallee, argsChecked, contents⟩ :=
    rpExpr_call_argumentChecks callRooted
  obtain ⟨leftRoots, leftAfter, rightRoots, rightAfter, leftRooted, rightRooted⟩ :=
    rpArgs_twoByValue_operands frame.source left right frame.rootCursor argsAfter allRoots argsChecked
  have firstSource := ordinaryOperandFrame_accepted accepted frame (checkFuel + 4) state types source
  have cursors := statefulBlock_expression_cursors checkFuel config accepted (ordinaryOperandFrame frame (checkFuel + 4))
    state types scope id origin blockOrigin expression intTy literal form firstSource initialized fresh absent firstPosition rfl
    [firstDescriptor.ty] firstAfter leftRoots leftAfter firstTyped leftRooted
  have limit : ({ frame.typing with use := .ordinary, request := .value, resultRequests := [] } : TypingEnv).globalLimit ≤
      config.module.globals.size := source.compatible.globals
  have bounded : GlobalEffectTargetsBounded ({ leftAfter with eff := {} } : RState).eff config.module.globals.size := by
    simp [GlobalEffectTargetsBounded, Eff.accessTargets]
  have rightBounded := recursiveScalar_effects_bounded rightForm (checkFuel + 3)
    { frame.typing with use := .ordinary, request := .value, resultRequests := [] } frame.source
    config.module.globals.size firstAfter rightTypingAfter { leftAfter with eff := {} } rightAfter [secondDescriptor.ty]
    rightRoots limit bounded rightTyped rightRooted
  have available : GlobalEffectsAvailable frame.interpretation frame.initialized rightAfter.eff := by
    rw [initialized, ← source.compatible.globalCount]
    exact (globalEffectsAvailable_iff_bounded frame.interpretation rightAfter.eff).2
      (by simpa only [source.compatible.globalCount] using rightBounded)
  refine ⟨leftAfter, rightRoots, rightTypingAfter, rightAfter, ?_, ?_, ?_⟩
  · simpa [ordinaryOperandFrame] using cursors.2
  · exact firstPosition
  · refine ⟨?_, rightRooted, ?_⟩
    · simpa [secondStatefulArgumentFrame, ordinaryOperandFrame, cursors.1] using rightTyped
    · simpa [secondStatefulArgumentFrame, ordinaryOperandFrame] using available

#print axioms checkedStatefulCallArguments
end Goose.Proofs.ConstructionAcceptedExecution
