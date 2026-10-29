import Goose.Proofs.ConstructionAcceptedRecursiveCallLocalTail

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem ScalarLocalReplay.registerCall_withArguments_tail_checked_fromBlock {config : EvalConfig} (accepted : AcceptedModule config)
    (blockFrame child final : ConstructionSourceFrame) (scope stamp fuel target origin : Nat) (statements : List Stmt)
    (context : Context) (callee : Impl) (arguments : List Arg) (ty : Ty)
    (position : SourcePosition accepted blockFrame (.block ⟨scope, statements, some (.call target arguments origin)⟩))
    (nesting : blockFrame.typingFuel = (fuel + 1) + 1)
    (childTyping : child.typing = { blockFrame.typing with scope := scope })
    (childFuel : child.typingFuel = fuel + 1) (childCounter : child.typingCounter = blockFrame.typingCounter)
    (childSource : child.source = { blockFrame.source with scopes := scope :: blockFrame.source.scopes })
    (childCursor : child.rootCursor = blockFrame.rootCursor)
    (childInterpretation : child.interpretation = blockFrame.interpretation.enterScope scope stamp)
    (childInitialized : child.initialized = blockFrame.initialized) (finalInitialized : final.initialized = child.initialized)
    (replay : ScalarLocalReplay child final statements) (form : ScalarLocalStatements statements)
    (contextAt : blockFrame.typing.module.contexts[target]? = some context)
    (calleeAt : blockFrame.typing.module.impls[context.impl]? = some callee)
    (results : callee.results = #[⟨ty, .register, none⟩])
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (requests : blockFrame.typing.resultRequests = [.register])
    (available : ∀ result after, rpBlockValue blockFrame.source [] ⟨scope, statements, some (.call target arguments origin)⟩ blockFrame.rootCursor =
      .ok (result, after) → GlobalEffectsAvailable blockFrame.interpretation blockFrame.initialized after.eff) :
    ∃ roots typingAfter rootsAfter,
      CheckedValue { final with typingFuel := fuel + 1 } (.call target arguments origin) ty roots typingAfter rootsAfter := by
  obtain ⟨middleRoots, tailRoots, lastRoots, rootedStatements, rootedTail, _, tailAvailable⟩ :=
    position.blockTail_effects accepted blockFrame scope statements (.call target arguments origin) available
  have finalAvailable : ∀ roots afterRoots, rpExpr final.source (.call target arguments origin) final.rootCursor = .ok (roots, afterRoots) →
      GlobalEffectsAvailable final.interpretation final.initialized afterRoots.eff := by
    intro roots afterRoots rooted
    obtain ⟨_, rootedReplay, sourceSame, interpretationSame⟩ := replay
    rw [sourceSame, childSource] at rooted
    have sameMiddle : final.rootCursor = middleRoots := by
      rw [childSource, childCursor] at rootedReplay
      exact (Prod.mk.inj (Except.ok.inj (rootedReplay.symm.trans rootedStatements))).2
    rw [sameMiddle] at rooted
    have sameAfter : afterRoots = lastRoots := (Prod.mk.inj (Except.ok.inj (rooted.symm.trans rootedTail))).2
    subst afterRoots
    simpa [interpretationSame, childInterpretation, RootInterpretation.enterScope, childInitialized, finalInitialized, GlobalEffectsAvailable] using tailAvailable
  exact replay.registerCall_withArguments_tail_checked accepted blockFrame child final scope fuel target origin statements context callee arguments ty
    position nesting childTyping childFuel childCounter childSource childCursor form contextAt calleeAt results scalar requests finalAvailable

#print axioms ScalarLocalReplay.registerCall_withArguments_tail_checked_fromBlock
end Goose.Proofs.ConstructionAcceptedExecution
