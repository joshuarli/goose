import Goose.Proofs.ConstructionAcceptedBlockExpressionTyping

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem rpExpr_blockE_body (environment : PEnv) (scope : Nat) (statements : List Stmt)
    (tail : Option Expr) (origin : Nat) (before after : RState) (roots : List RootRef)
    (checked : rpExpr environment (.blockE ⟨scope, statements, tail⟩ origin) before = .ok (roots, after)) :
    ∃ start finish bodyAfter,
      rpBlockValue { environment with valueBlock := some scope } [] ⟨scope, statements, tail⟩
        { before with valueBreakRoots := [] } = .ok ((roots, (start, finish)), bodyAfter) ∧
      after = { bodyAfter with valueBreakRoots := before.valueBreakRoots } := by
  simp only [rpExpr, bind, StateT.bind, get, modify] at checked
  simp only [getThe, MonadStateOf.get, modifyGet, MonadState.modifyGet, StateT.get, StateT.modifyGet, MonadStateOf.modifyGet, Except.bind, Except.pure, pure, StateT.pure] at checked
  cases body : rpBlockValue { environment with valueBlock := some scope } [] ⟨scope, statements, tail⟩
      { before with valueBreakRoots := [] } with
  | error failure =>
    simp [body] at checked
  | ok result =>
    rcases result with ⟨⟨bodyRoots, start, finish⟩, bodyAfter⟩
    simp [body] at checked
    obtain ⟨rfl, rfl⟩ := checked
    exact ⟨start, finish, bodyAfter, rfl, rfl⟩

#print axioms rpExpr_blockE_body
end Goose.Proofs.ConstructionAcceptedExecution
