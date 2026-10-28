import Goose.Proofs.ConstructionAcceptedTwoArgumentRoots
import Goose.Proofs.ConstructionAcceptedTwoArgumentTyping
import Goose.Proofs.ConstructionAcceptedPositions

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem SourcePosition.twoArgumentFirst {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (fuel contextId origin : Nat) (context : Context) (callee : Impl)
    (first second : Param) (firstDescriptor secondDescriptor : LocalVar) (left right : Expr)
    (compatible : SourceFrameCompatible accepted frame)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[first, second])
    (firstMode : first.mode = .byValue) (secondMode : second.mode = .byValue)
    (firstDeclared : callee.vars[first.var]? = some firstDescriptor)
    (secondDeclared : callee.vars[second.var]? = some secondDescriptor)
    (firstScalar : (∃ intTy, firstDescriptor.ty = .int intTy) ∨ firstDescriptor.ty = .bool)
    (secondScalar : (∃ intTy, secondDescriptor.ty = .int intTy) ∨ secondDescriptor.ty = .bool)
    (nesting : frame.typingFuel = fuel + 3)
    (position : SourcePosition accepted frame (.expression (.call contextId [.byVal left, .byVal right] origin))) :
    SourcePosition accepted (ordinaryOperandFrame frame (fuel + 1)) (.expression left) := by
  obtain ⟨types, typingAfter, roots, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
  rw [nesting] at typed
  have typedContext : frame.typing.module.contexts[contextId]? = some context := by simpa [compatible.module] using contextAt
  have typedCallee : frame.typing.module.impls[context.impl]? = some callee := by simpa [compatible.module] using calleeAt
  obtain ⟨firstAfter, secondAfter, firstTyped, secondTyped⟩ := typeExpr_twoScalarCall_operands fuel frame.typing contextId origin context callee
    first second firstDescriptor secondDescriptor left right frame.typingCounter typingAfter types
    typedContext typedCallee parameters firstMode secondMode firstDeclared secondDeclared firstScalar secondScalar typed
  obtain ⟨selected, selectedCallee, allRoots, argsAfter, foundContext, foundCallee, argsChecked, contents⟩ :=
    rpExpr_call_argumentChecks rooted
  obtain ⟨leftRoots, leftAfter, rightRoots, rightAfter, leftRooted, rightRooted⟩ :=
    rpArgs_twoByValue_operands frame.source left right frame.rootCursor argsAfter allRoots argsChecked
  exact .child position (.callFirstByValue frame contextId origin fuel left right nesting)
    ⟨[firstDescriptor.ty], firstAfter, leftRoots, leftAfter, firstTyped, leftRooted⟩

#print axioms SourcePosition.twoArgumentFirst
end Goose.Proofs.ConstructionAcceptedExecution
