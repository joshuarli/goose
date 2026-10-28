import Goose.Proofs.ConstructionAcceptedStatefulInitializerBinding

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem typeExpr_statefulBlock_fuel (fuel : Nat) (environment : TypingEnv) (scope id origin blockOrigin : Nat)
    (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int) (before after : Nat) (result : List Ty)
    (checked : typeExpr fuel environment (.blockE
      ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) before = .ok (result, after)) :
    4 ≤ fuel := by
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at checked; cases checked
  | succ fuel =>
    cases fuel with
    | zero =>
      simp [typeExpr, blockResultTypes?] at checked
      change Except.error _ = Except.ok _ at checked
      cases checked
    | succ fuel =>
      cases fuel with
      | zero =>
        simp [typeExpr, blockResultTypes?, expressionResultTypes?] at checked
        change Except.error _ = Except.ok _ at checked
        cases checked
      | succ fuel =>
        cases fuel with
        | zero =>
          simp only [typeExpr, blockResultTypes?, expressionResultTypes?, DeclarationEnv.exprType?, bind, StateT.bind] at checked
          simp only [typeBlock, typeStatements, typeStatement] at checked
          change Except.error _ = Except.ok _ at checked
          cases checked
        | succ fuel => omega

theorem typeArguments_firstByValue (fuel : Nat) (environment : TypingEnv) (callee : Impl) (first : Param)
    (descriptor : LocalVar) (parameters : List Param) (left : Expr) (arguments : List Arg) (before after : Nat)
    (mode : first.mode = .byValue) (declared : callee.vars[first.var]? = some descriptor)
    (checked : typeArguments (fuel + 1) environment callee (first :: parameters) (.byVal left :: arguments) before = .ok ((), after)) :
    ∃ types middle, typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] } left before = .ok (types, middle) := by
  simp only [typeArguments, declared, mode, bind, StateT.bind] at checked
  cases nonfixed : descriptor.ty.nonfixed with
  | true =>
    simp only [nonfixed] at checked
    change Except.error _ = Except.ok _ at checked
    cases checked
  | false =>
    simp only [nonfixed] at checked
    change (typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] } left before).bind _ = _ at checked
    cases operand : typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] } left before with
    | error failure => simp [operand, Except.bind] at checked
    | ok result => exact ⟨result.1, result.2, rfl⟩

theorem SourcePosition.statefulCallInitializer_fuel {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (localId statementOrigin contextId callOrigin scope id origin blockOrigin : Nat)
    (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int) (right : Expr)
    (context : Context) (callee : Impl) (first second : Param) (descriptor : LocalVar)
    (compatible : SourceFrameCompatible accepted frame)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[first, second]) (mode : first.mode = .byValue)
    (declared : callee.vars[first.var]? = some descriptor)
    (position : SourcePosition accepted frame (.statement (.letS localId (.call contextId
      [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] callOrigin) statementOrigin))) :
    ∃ checkFuel, frame.typingFuel = checkFuel + 7 := by
  let left : Expr := .blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin
  let arguments : List Arg := [.byVal left, .byVal right]
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
        have exactArguments : typeArguments (operandFuel + 1) initial.typing callee [first, second]
            [.byVal left, .byVal right] initial.typingCounter = .ok ((), middle) := by
          simpa [arguments, parameters] using argumentsTyped
        obtain ⟨operandTypes, operandAfter, operandTyped⟩ := typeArguments_firstByValue operandFuel initial.typing callee first descriptor
          [second] left [.byVal right] initial.typingCounter middle mode declared exactArguments
        have enough := typeExpr_statefulBlock_fuel operandFuel
          { initial.typing with use := .ordinary, request := .value, resultRequests := [] } scope id origin blockOrigin expression
          intTy literal initial.typingCounter operandAfter operandTypes (by simpa [left] using operandTyped)
        exact ⟨operandFuel - 4, by omega⟩

#print axioms SourcePosition.statefulCallInitializer_fuel
#print axioms typeArguments_firstByValue
#print axioms typeExpr_statefulBlock_fuel
end Goose.Proofs.ConstructionAcceptedExecution
