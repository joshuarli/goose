import Goose.Proofs.ConstructionAcceptedStatefulCallFuel

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem SourcePosition.statefulListCallInitializer_fuel {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (localId statementOrigin contextId callOrigin scope id origin blockOrigin : Nat)
    (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int) (rest : List Expr)
    (context : Context) (callee : Impl) (first : Param) (remaining : List Param) (descriptor : LocalVar)
    (compatible : SourceFrameCompatible accepted frame)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params.toList = first :: remaining) (mode : first.mode = .byValue)
    (declared : callee.vars[first.var]? = some descriptor)
    (position : SourcePosition accepted frame (.statement (.letS localId (.call contextId
      (.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) :: rest.map Arg.byVal) callOrigin) statementOrigin))) :
    ∃ checkFuel, frame.typingFuel = checkFuel + 7 := by
  let left : Expr := .blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin
  let arguments : List Arg := .byVal left :: rest.map Arg.byVal
  obtain ⟨next, counter, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
  cases nesting : frame.typingFuel with
  | zero => rw [nesting] at typed; change Except.error _ = Except.ok _ at typed; cases typed
  | succ callFuel =>
    obtain ⟨localDescriptor, localDeclared, typingOrder, rootOrder, callPosition⟩ :=
      position.callInitializer frame localId statementOrigin contextId callOrigin callFuel arguments nesting
    obtain ⟨types, after, roots, rootAfter, callTyped, callRooted⟩ := callPosition.checked accepted _ _
    cases callFuel with
    | zero => change Except.error _ = Except.ok _ at callTyped; cases callTyped
    | succ argumentFuel =>
      let initial := letInitializerFrame frame localId (argumentFuel + 1)
      have ctx : initial.typing.module.contexts[contextId]? = some context := by
        simpa [initial, letInitializerFrame, ordinaryOperandFrame, compatible.module] using contextAt
      have impl : initial.typing.module.impls[context.impl]? = some callee := by
        simpa [initial, letInitializerFrame, ordinaryOperandFrame, compatible.module] using calleeAt
      obtain ⟨middle, argumentsTyped⟩ := typeExpr_call_arguments argumentFuel initial.typing contextId context callee
        arguments callOrigin initial.typingCounter after types ctx impl callTyped
      cases argumentFuel with
      | zero => change Except.error _ = Except.ok _ at argumentsTyped; cases argumentsTyped
      | succ operandFuel =>
        have exactArguments : typeArguments (operandFuel + 1) initial.typing callee (first :: remaining)
            (.byVal left :: rest.map Arg.byVal) initial.typingCounter = .ok ((), middle) := by
          simpa [arguments, parameters] using argumentsTyped
        obtain ⟨operandTypes, operandAfter, operandTyped⟩ := typeArguments_firstByValue operandFuel initial.typing callee first descriptor
          remaining left (rest.map Arg.byVal) initial.typingCounter middle mode declared exactArguments
        have enough := typeExpr_statefulBlock_fuel operandFuel
          { initial.typing with use := .ordinary, request := .value, resultRequests := [] } scope id origin blockOrigin expression
          intTy literal initial.typingCounter operandAfter operandTypes (by simpa [left] using operandTyped)
        exact ⟨operandFuel - 4, by omega⟩


#print axioms SourcePosition.statefulListCallInitializer_fuel
end Goose.Proofs.ConstructionAcceptedExecution
