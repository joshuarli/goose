import Goose.Proofs.ConstructionAcceptedScalarArgumentListTyping
import Goose.Proofs.ConstructionAcceptedArgumentListRoots
import Goose.Proofs.ConstructionAcceptedPositions

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem SourcePosition.callFirstByValueList {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (fuel contextId origin : Nat) (context : Context) (callee : Impl)
    (first : Param) (remaining : List Param) (descriptor : LocalVar) (expression : Expr) (rest : List Arg)
    (compatible : SourceFrameCompatible accepted frame)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params.toList = first :: remaining)
    (mode : first.mode = .byValue)
    (declared : callee.vars[first.var]? = some descriptor)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (nesting : frame.typingFuel = fuel + 2)
    (position : SourcePosition accepted frame (.expression (.call contextId (.byVal expression :: rest) origin))) :
    SourcePosition accepted (ordinaryOperandFrame frame fuel) (.expression expression) := by
  obtain ⟨types, typingAfter, roots, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
  rw [nesting] at typed
  have typedContext : frame.typing.module.contexts[contextId]? = some context := by simpa [compatible.module] using contextAt
  have typedCallee : frame.typing.module.impls[context.impl]? = some callee := by simpa [compatible.module] using calleeAt
  obtain ⟨middle, arguments⟩ := typeExpr_call_arguments (fuel + 1) frame.typing contextId context callee
    (.byVal expression :: rest) origin frame.typingCounter typingAfter types typedContext typedCallee typed
  have argumentCheck : typeArguments (fuel + 1) frame.typing callee (first :: remaining) (.byVal expression :: rest)
      frame.typingCounter = .ok ((), middle) := by simpa [parameters] using arguments
  obtain ⟨firstAfter, firstTyped, tailTyped⟩ := typeArguments_scalarByValue_cons fuel frame.typing callee first descriptor
    remaining expression rest frame.typingCounter middle mode declared scalar argumentCheck
  obtain ⟨selected, selectedCallee, allRoots, argsAfter, foundContext, foundCallee, argsChecked, contents⟩ :=
    rpExpr_call_argumentChecks rooted
  obtain ⟨firstRoots, firstRootAfter, tailRoots, tailAfter, firstRooted, tailRooted⟩ :=
    rpArgs_byValue_cons frame.source expression rest frame.rootCursor argsAfter allRoots argsChecked
  exact .child position (.callFirstByValueList frame contextId origin fuel expression rest nesting)
    ⟨[descriptor.ty], firstAfter, firstRoots, firstRootAfter, firstTyped, firstRooted⟩

#print axioms SourcePosition.callFirstByValueList
end Goose.Proofs.ConstructionAcceptedExecution
