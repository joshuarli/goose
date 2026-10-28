import Goose.Proofs.ConstructionAcceptedArgumentListPosition
import Goose.Proofs.ConstructionAcceptedStatefulBlockCursors
import Goose.Proofs.ConstructionAcceptedScalarArgumentListChecks
import Goose.Proofs.ConstructionAcceptedIntegerBlockTyping

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem checkedStatefulArgumentList_cursors {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes) (checkFuel contextId callOrigin : Nat)
    (context : Context) (callee : Impl) (first : Param) (remaining : List Param) (firstDescriptor : LocalVar)
    (scope id origin blockOrigin : Nat) (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int) (rest : List Expr)
    (form : AcceptedBinaryExpression expression) (source : AcceptedFrame config accepted frame state types)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params.toList = first :: remaining)
    (firstMode : first.mode = .byValue) (firstDeclared : callee.vars[first.var]? = some firstDescriptor)
    (firstScalar : (∃ t, firstDescriptor.ty = .int t) ∨ firstDescriptor.ty = .bool)
    (initialized : frame.initialized = config.module.globals.size)
    (fresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ scope)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (nesting : frame.typingFuel = checkFuel + 6)
    (position : SourcePosition accepted frame (.expression (.call contextId
      (.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) :: rest.map Arg.byVal) callOrigin))) :
    ∃ (middle : Nat) (leftAfter tailAfter : RState) (tailRoots : List (List RootRef)),
      firstDescriptor.ty = .int intTy ∧
      leftAfter.nextVar = frame.rootCursor.nextVar ∧
      SourcePosition accepted (ordinaryOperandFrame frame (checkFuel + 4)) (.expression (.blockE
        ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin)) ∧
      typeArguments (checkFuel + 4) frame.typing callee remaining (rest.map Arg.byVal) frame.typingCounter = .ok ((), middle) ∧
      rpArgs frame.source (rest.map Arg.byVal) { leftAfter with eff := {} } = .ok (tailRoots, tailAfter) := by
  let left : Expr := .blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin
  have firstPosition := position.callFirstByValueList accepted frame (checkFuel + 4) contextId callOrigin context callee
    first remaining firstDescriptor left (rest.map Arg.byVal) source.compatible contextAt calleeAt parameters firstMode
    firstDeclared firstScalar (by simpa [Nat.add_assoc] using nesting)
  obtain ⟨callTypes, callTypingAfter, callRoots, callRootsAfter, callTyped, callRooted⟩ := position.checked accepted frame _
  rw [nesting] at callTyped
  have typedContext : frame.typing.module.contexts[contextId]? = some context := by simpa [source.compatible.module] using contextAt
  have typedCallee : frame.typing.module.impls[context.impl]? = some callee := by simpa [source.compatible.module] using calleeAt
  obtain ⟨middle, arguments⟩ := typeExpr_call_arguments (checkFuel + 5) frame.typing contextId context callee
    (.byVal left :: rest.map Arg.byVal) callOrigin frame.typingCounter callTypingAfter callTypes typedContext typedCallee
    (by simpa [left, Nat.add_assoc] using callTyped)
  have arguments' : typeArguments (checkFuel + 5) frame.typing callee (first :: remaining) (.byVal left :: rest.map Arg.byVal)
      frame.typingCounter = .ok ((), middle) := by simpa [parameters] using arguments
  obtain ⟨firstAfter, firstTyped, tailTyped⟩ := typeArguments_scalarByValue_cons (checkFuel + 4) frame.typing callee first firstDescriptor
    remaining left (rest.map Arg.byVal) frame.typingCounter middle firstMode firstDeclared firstScalar (by simpa [Nat.add_assoc] using arguments')
  obtain ⟨selected, selectedCallee, allRoots, argsAfter, foundContext, foundCallee, argsChecked, contents⟩ :=
    rpExpr_call_argumentChecks callRooted
  obtain ⟨leftRoots, leftAfter, tailRoots, tailAfter, leftRooted, tailRooted⟩ :=
    rpArgs_byValue_cons frame.source left (rest.map Arg.byVal) frame.rootCursor argsAfter allRoots argsChecked
  have firstSource := ordinaryOperandFrame_accepted accepted frame (checkFuel + 4) state types source
  have cursors := statefulBlock_expression_cursors checkFuel config accepted (ordinaryOperandFrame frame (checkFuel + 4))
    state types scope id origin blockOrigin expression intTy literal form firstSource initialized fresh absent firstPosition rfl
    [firstDescriptor.ty] firstAfter leftRoots leftAfter firstTyped leftRooted
  have firstType := typeExpr_integerTail_result (checkFuel + 1)
    { frame.typing with use := .ordinary, request := .value, resultRequests := [] } scope
    [.assign (.global id) expression origin] intTy literal blockOrigin frame.typingCounter firstAfter [firstDescriptor.ty]
    (by simpa [left, Nat.add_assoc] using firstTyped)
  refine ⟨middle, leftAfter, tailAfter, tailRoots, ?_, ?_, firstPosition, ?_, tailRooted⟩
  · simpa using firstType
  · simpa [ordinaryOperandFrame] using cursors.2
  · simpa [ordinaryOperandFrame] using cursors.1 ▸ tailTyped

#print axioms checkedStatefulArgumentList_cursors
end Goose.Proofs.ConstructionAcceptedExecution
