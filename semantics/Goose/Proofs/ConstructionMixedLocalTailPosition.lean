import Goose.Proofs.ConstructionAcceptedBlockTailChecks
import Goose.Proofs.ConstructionMixedLocalReplayWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem SourcePosition.blockTail_afterReplay {config : EvalConfig} (accepted : AcceptedModule config)
    (frame next : ConstructionSourceFrame) (scope fuel : Nat) (statements : List Stmt) (expression : Expr)
    (position : SourcePosition accepted frame (.block ⟨scope, statements, some expression⟩))
    (nesting : frame.typingFuel = fuel + 1)
    (typing : typeStatements fuel { frame.typing with scope := scope } statements frame.typingCounter = .ok (next.typing, next.typingCounter))
    (rooting : rpStmts { frame.source with scopes := scope :: frame.source.scopes } statements frame.rootCursor = .ok ((), next.rootCursor))
    (source : next.source = { frame.source with scopes := scope :: frame.source.scopes })
    (interpretation : next.interpretation = frame.interpretation) (initialized : next.initialized = frame.initialized)
    (phase : next.phase = frame.phase) :
    SourcePosition accepted { next with typingFuel := fuel } (.expression expression) := by
  obtain ⟨typingEnv, typingMiddle, rootMiddle, typed, rooted, child⟩ :=
    position.blockTail accepted frame scope fuel statements expression nesting
  have sameTyping : (typingEnv, typingMiddle) = (next.typing, next.typingCounter) := Except.ok.inj (typed.symm.trans typing)
  have sameRoot : rootMiddle = next.rootCursor := (Prod.mk.inj (Except.ok.inj (rooted.symm.trans rooting))).2
  obtain ⟨sameEnv, sameCounter⟩ := Prod.mk.inj sameTyping
  subst typingEnv typingMiddle rootMiddle
  cases frame
  cases next
  simp_all only

theorem entryStatementsFrame_blockFrame (config : EvalConfig) (frame : ConstructionSourceFrame) (scopeInst : Nat) :
    blockStatementsFrame (implementationBodyFrame config (entryStatementsFrame config frame scopeInst))
      frame.source.impl.body.scope 4095 = entryStatementsFrame config frame scopeInst := by
  rfl

#print axioms SourcePosition.blockTail_afterReplay
end Goose.Proofs.ConstructionAcceptedExecution
