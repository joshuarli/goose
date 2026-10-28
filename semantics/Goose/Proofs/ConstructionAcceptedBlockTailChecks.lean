import Goose.Proofs.ConstructionAcceptedScalarEntryWitness

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem SourcePosition.blockTail_checks {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (scope fuel : Nat) (statements : List Stmt) (expression : Expr)
    (position : SourcePosition accepted frame (.block ⟨scope, statements, some expression⟩))
    (nesting : frame.typingFuel = fuel + 1) :
    ∃ next typingMiddle rootMiddle types typingAfter roots rootsAfter,
      typeBlock frame.typingFuel frame.typing ⟨scope, statements, some expression⟩ frame.typingCounter = .ok (types, typingAfter) ∧
      typeStatements fuel { frame.typing with scope := scope } statements frame.typingCounter = .ok (next, typingMiddle) ∧
      rpStmts { frame.source with scopes := scope :: frame.source.scopes } statements frame.rootCursor = .ok ((), rootMiddle) ∧
      typeExpr fuel next expression typingMiddle = .ok (types, typingAfter) ∧
      rpExpr { frame.source with scopes := scope :: frame.source.scopes } expression rootMiddle = .ok (roots, rootsAfter) := by
  obtain ⟨types, typingAfter, blockRoots, rootsAfter, typed, rooted⟩ := position.checked accepted frame _
  have blockTyped := typed
  rw [nesting] at typed
  simp only [typeBlock, bind, StateT.bind] at typed
  obtain ⟨_, rootMiddle, roots, rootedStatements, rootedTail, _⟩ := rpBlockValue_body rooted
  simp only [List.length_nil, Nat.add_zero] at rootedStatements
  cases statementsTyped : typeStatements fuel { frame.typing with scope := scope } statements frame.typingCounter with
  | error failure =>
    rw [statementsTyped] at typed
    cases typed
  | ok result =>
    obtain ⟨next, typingMiddle⟩ := result
    rw [statementsTyped] at typed
    change typeExpr fuel next expression typingMiddle = .ok (types, typingAfter) at typed
    exact ⟨next, typingMiddle, rootMiddle, types, typingAfter, roots, rootsAfter,
      blockTyped, rfl, rootedStatements, typed, rootedTail⟩

theorem SourcePosition.blockTail {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (scope fuel : Nat) (statements : List Stmt) (expression : Expr)
    (position : SourcePosition accepted frame (.block ⟨scope, statements, some expression⟩))
    (nesting : frame.typingFuel = fuel + 1) :
    ∃ next typingMiddle rootMiddle,
      typeStatements fuel { frame.typing with scope := scope } statements frame.typingCounter = .ok (next, typingMiddle) ∧
      rpStmts { frame.source with scopes := scope :: frame.source.scopes } statements frame.rootCursor = .ok ((), rootMiddle) ∧
      SourcePosition accepted
        { frame with typingFuel := fuel, typing := next, typingCounter := typingMiddle, source := { frame.source with scopes := scope :: frame.source.scopes }, rootCursor := rootMiddle }
        (.expression expression) := by
  obtain ⟨next, typingMiddle, rootMiddle, types, typingAfter, roots, rootsAfter,
    blockTyped, typedStatements, rootedStatements, typedTail, rootedTail⟩ :=
    position.blockTail_checks accepted frame scope fuel statements expression nesting
  exact ⟨next, typingMiddle, rootMiddle, typedStatements, rootedStatements,
    .child position (.blockTail frame scope fuel statements expression next typingMiddle rootMiddle nesting typedStatements rootedStatements)
      ⟨types, typingAfter, roots, rootsAfter, typedTail, rootedTail⟩⟩

theorem SourcePosition.blockTail_checkedScalar {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (scope fuel : Nat) (statements : List Stmt) (expression : Expr)
    (position : SourcePosition accepted frame (.block ⟨scope, statements, some expression⟩))
    (nesting : frame.typingFuel = fuel + 1) (form : AcceptedBinaryExpression expression)
    (available : ∀ rootMiddle roots rootsAfter,
      rpStmts { frame.source with scopes := scope :: frame.source.scopes } statements frame.rootCursor = .ok ((), rootMiddle) →
      rpExpr { frame.source with scopes := scope :: frame.source.scopes } expression rootMiddle = .ok (roots, rootsAfter) →
      GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff) :
    ∃ next typingMiddle rootMiddle ty typingAfter roots rootsAfter,
      typeStatements fuel { frame.typing with scope := scope } statements frame.typingCounter = .ok (next, typingMiddle) ∧
      rpStmts { frame.source with scopes := scope :: frame.source.scopes } statements frame.rootCursor = .ok ((), rootMiddle) ∧
      CheckedValue { frame with typingFuel := fuel, typing := next, typingCounter := typingMiddle, source := { frame.source with scopes := scope :: frame.source.scopes }, rootCursor := rootMiddle }
        expression ty roots typingAfter rootsAfter := by
  obtain ⟨next, typingMiddle, rootMiddle, types, typingAfter, roots, rootsAfter,
    blockTyped, typedStatements, rootedStatements, typedTail, rootedTail⟩ :=
    position.blockTail_checks accepted frame scope fuel statements expression nesting
  obtain ⟨ty, same⟩ := typeExpr_scalar_singleton form fuel next typingMiddle typingAfter types typedTail
  subst types
  exact ⟨next, typingMiddle, rootMiddle, ty, typingAfter, roots, rootsAfter, typedStatements, rootedStatements,
    ⟨typedTail, rootedTail, available rootMiddle roots rootsAfter rootedStatements rootedTail⟩⟩

theorem SourcePosition.blockTail_checkedUnit {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (scope fuel : Nat) (statements : List Stmt) (expression : Expr)
    (position : SourcePosition accepted frame (.block ⟨scope, statements, some expression⟩))
    (nesting : frame.typingFuel = fuel + 1) (finalCounter : Nat)
    (bodyUnit : typeBlock frame.typingFuel frame.typing ⟨scope, statements, some expression⟩ frame.typingCounter =
      .ok ([.unit], finalCounter))
    (available : ∀ rootMiddle roots rootsAfter,
      rpStmts { frame.source with scopes := scope :: frame.source.scopes } statements frame.rootCursor = .ok ((), rootMiddle) →
      rpExpr { frame.source with scopes := scope :: frame.source.scopes } expression rootMiddle = .ok (roots, rootsAfter) →
      GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff) :
    ∃ next typingMiddle rootMiddle roots rootsAfter,
      typeStatements fuel { frame.typing with scope := scope } statements frame.typingCounter = .ok (next, typingMiddle) ∧
      rpStmts { frame.source with scopes := scope :: frame.source.scopes } statements frame.rootCursor = .ok ((), rootMiddle) ∧
      CheckedValue { frame with typingFuel := fuel, typing := next, typingCounter := typingMiddle, source := { frame.source with scopes := scope :: frame.source.scopes }, rootCursor := rootMiddle }
        expression .unit roots finalCounter rootsAfter := by
  obtain ⟨next, typingMiddle, rootMiddle, types, typingAfter, roots, rootsAfter,
    blockTyped, typedStatements, rootedStatements, typedTail, rootedTail⟩ :=
    position.blockTail_checks accepted frame scope fuel statements expression nesting
  have same : (types, typingAfter) = ([.unit], finalCounter) := Except.ok.inj (blockTyped.symm.trans bodyUnit)
  cases same
  exact ⟨next, typingMiddle, rootMiddle, roots, rootsAfter, typedStatements, rootedStatements,
    ⟨typedTail, rootedTail, available rootMiddle roots rootsAfter rootedStatements rootedTail⟩⟩

#print axioms SourcePosition.blockTail_checkedUnit
#print axioms SourcePosition.blockTail
#print axioms SourcePosition.blockTail_checks
#print axioms SourcePosition.blockTail_checkedScalar
end Goose.Proofs.ConstructionAcceptedExecution
