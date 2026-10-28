import Goose.Proofs.ConstructionAcceptedStatefulArgumentExecution

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem typeExpr_integerTail_result (fuel : Nat) (environment : TypingEnv) (scope : Nat) (statements : List Stmt)
    (intTy : Goose.Core.IntTy) (literal : Int) (origin before after : Nat) (result : List Ty)
    (typed : typeExpr (fuel + 3) environment (.blockE ⟨scope, statements, some (.lit intTy literal)⟩ origin) before = .ok (result, after)) :
    result = [.int intTy] := by
  obtain ⟨expected, query, blockTyped, same⟩ := typeExpr_blockE_tail (fuel + 2) environment scope statements
    (.lit intTy literal) origin before after result (by simpa [Nat.add_assoc] using typed)
  simp only [typeBlock, bind, StateT.bind] at blockTyped
  cases statementsTyped : typeStatements (fuel + 1)
      { environment with valueBreakTarget := some ⟨expected, environment.use, environment.request, environment.resultRequests⟩, scope := scope }
      statements before with
  | error failure =>
    rw [statementsTyped] at blockTyped
    cases blockTyped
  | ok output =>
    rcases output with ⟨next, middle⟩
    rw [statementsTyped] at blockTyped
    change typeExpr (fuel + 1) next (.lit intTy literal) middle = .ok (result, after) at blockTyped
    simp [typeExpr, pure, StateT.pure, Except.pure] at blockTyped
    exact blockTyped.1.symm

theorem statefulCall_firstParameterType {config : EvalConfig} {accepted : AcceptedModule config}
    (frame : ConstructionSourceFrame) (checkFuel contextId callOrigin : Nat) (context : Context) (callee : Impl)
    (first second : Param) (firstDescriptor secondDescriptor : LocalVar) (scope id origin blockOrigin : Nat)
    (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int) (right : Expr)
    (compatible : SourceFrameCompatible accepted frame)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[first, second])
    (firstMode : first.mode = .byValue) (secondMode : second.mode = .byValue)
    (firstDeclared : callee.vars[first.var]? = some firstDescriptor)
    (secondDeclared : callee.vars[second.var]? = some secondDescriptor)
    (firstScalar : (∃ t, firstDescriptor.ty = .int t) ∨ firstDescriptor.ty = .bool)
    (secondScalar : (∃ t, secondDescriptor.ty = .int t) ∨ secondDescriptor.ty = .bool)
    (nesting : frame.typingFuel = checkFuel + 6)
    (position : SourcePosition accepted frame (.expression (.call contextId
      [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] callOrigin))) :
    firstDescriptor.ty = .int intTy := by
  obtain ⟨types, typingAfter, roots, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
  rw [nesting] at typed
  have typedContext : frame.typing.module.contexts[contextId]? = some context := by simpa [compatible.module] using contextAt
  have typedCallee : frame.typing.module.impls[context.impl]? = some callee := by simpa [compatible.module] using calleeAt
  obtain ⟨firstAfter, secondAfter, firstTyped, secondTyped⟩ := typeExpr_twoScalarCall_operands (checkFuel + 3)
    frame.typing contextId callOrigin context callee first second firstDescriptor secondDescriptor
    (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) right
    frame.typingCounter typingAfter types typedContext typedCallee parameters firstMode secondMode firstDeclared secondDeclared
    firstScalar secondScalar (by simpa [Nat.add_assoc] using typed)
  have same := typeExpr_integerTail_result (checkFuel + 1)
    { frame.typing with use := .ordinary, request := .value, resultRequests := [] } scope
    [.assign (.global id) expression origin] intTy literal blockOrigin frame.typingCounter firstAfter [firstDescriptor.ty]
    (by simpa [Nat.add_assoc] using firstTyped)
  simpa using same

#print axioms statefulCall_firstParameterType
#print axioms typeExpr_integerTail_result
end Goose.Proofs.ConstructionAcceptedExecution
