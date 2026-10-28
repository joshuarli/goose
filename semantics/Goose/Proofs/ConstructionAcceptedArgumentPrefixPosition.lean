import Goose.Proofs.ConstructionAcceptedArgumentListPosition

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem SourcePosition.call_arguments {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (contextId origin fuel : Nat) (context : Context) (callee : Impl) (arguments : List Arg)
    (compatible : SourceFrameCompatible accepted frame)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (nesting : frame.typingFuel = fuel + 1)
    (position : SourcePosition accepted frame (.expression (.call contextId arguments origin))) :
    SourcePosition accepted { frame with typingFuel := fuel } (.arguments callee callee.params.toList arguments) := by
  obtain ⟨types, typingAfter, roots, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
  have selected : frame.typing.module.contexts[contextId]? = some context := by simpa [compatible.module] using contextAt
  have implementation : frame.typing.module.impls[context.impl]? = some callee := by simpa [compatible.module] using calleeAt
  obtain ⟨middle, argumentsTyped⟩ := typeExpr_call_arguments fuel frame.typing contextId context callee arguments origin
    frame.typingCounter typingAfter types selected implementation (by simpa [nesting] using typed)
  obtain ⟨selectedContext, selectedCallee, argumentRoots, argumentAfter, foundContext, foundCallee, argumentsRooted, contents⟩ :=
    rpExpr_call_argumentChecks rooted
  exact .child position (.callArguments frame contextId origin fuel context callee arguments nesting selected implementation)
    ⟨middle, argumentRoots, argumentAfter, argumentsTyped, argumentsRooted⟩

theorem SourcePosition.arguments_byValue {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (callee : Impl) (parameter : Param) (descriptor : LocalVar)
    (parameters : List Param) (expression : Expr) (arguments : List Arg) (fuel : Nat)
    (nesting : frame.typingFuel = fuel + 1) (mode : parameter.mode = .byValue)
    (declared : callee.vars[parameter.var]? = some descriptor)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (position : SourcePosition accepted frame (.arguments callee (parameter :: parameters) (.byVal expression :: arguments))) :
    ∃ typingAfter roots rootsAfter,
      SourcePosition accepted (ordinaryOperandFrame frame fuel) (.expression expression) ∧
      SourcePosition accepted { frame with typingFuel := fuel, typingCounter := typingAfter, rootCursor := { rootsAfter with eff := {} } } (.arguments callee parameters arguments) ∧
      typeExpr fuel { frame.typing with use := .ordinary, request := .value, resultRequests := [] }
        expression frame.typingCounter = .ok ([descriptor.ty], typingAfter) ∧
      rpExpr frame.source expression frame.rootCursor = .ok (roots, rootsAfter) := by
  obtain ⟨after, allRoots, rootAfter, typed, rooted⟩ := position.checked accepted frame _
  obtain ⟨typingAfter, headTyped, tailTyped⟩ := typeArguments_scalarByValue_cons fuel frame.typing callee parameter descriptor
    parameters expression arguments frame.typingCounter after mode declared scalar (by simpa [nesting] using typed)
  obtain ⟨roots, rootsAfter, tailRoots, tailAfter, headRooted, tailRooted⟩ :=
    rpArgs_byValue_cons frame.source expression arguments frame.rootCursor rootAfter allRoots rooted
  refine ⟨typingAfter, roots, rootsAfter, ?_, ?_, headTyped, headRooted⟩
  · exact .child position (.argumentsByValueHead frame callee parameter parameters expression arguments fuel nesting)
      ⟨[descriptor.ty], typingAfter, roots, rootsAfter, headTyped, headRooted⟩
  · exact .child position (.argumentsByValueTail frame callee parameter descriptor parameters expression arguments fuel
      typingAfter roots rootsAfter nesting mode declared headTyped headRooted) ⟨after, tailRoots, tailAfter, tailTyped, tailRooted⟩

#print axioms SourcePosition.call_arguments
#print axioms SourcePosition.arguments_byValue
end Goose.Proofs.ConstructionAcceptedExecution
