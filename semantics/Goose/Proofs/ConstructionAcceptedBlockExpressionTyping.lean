import Goose.Proofs.ConstructionAcceptedTwoArgumentTyping

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

theorem typeExpr_blockE_tail (fuel : Nat) (environment : TypingEnv) (scope : Nat)
    (statements : List Stmt) (tail : Expr) (origin before after : Nat) (result : List Ty)
    (checked : typeExpr (fuel + 1) environment (.blockE ⟨scope, statements, some tail⟩ origin) before = .ok (result, after)) :
    ∃ expected, blockResultTypes? fuel ⟨environment.module, environment.variables⟩ ⟨scope, statements, some tail⟩ = some expected ∧
      typeBlock fuel { environment with valueBreakTarget := some ⟨expected, environment.use, environment.request, environment.resultRequests⟩ }
        ⟨scope, statements, some tail⟩ before = .ok (result, after) ∧ result = expected := by
  simp only [typeExpr, bind, StateT.bind] at checked
  cases query : blockResultTypes? fuel ⟨environment.module, environment.variables⟩ ⟨scope, statements, some tail⟩ with
  | none =>
    simp only [query] at checked
    change Except.error _ = Except.ok _ at checked
    cases checked
  | some expected =>
    simp only [query, StateT.bind] at checked
    change (typeBlock fuel { environment with valueBreakTarget := some ⟨expected, environment.use, environment.request, environment.resultRequests⟩ }
      ⟨scope, statements, some tail⟩ before).bind _ = _ at checked
    cases body : typeBlock fuel { environment with valueBreakTarget := some ⟨expected, environment.use, environment.request, environment.resultRequests⟩ }
        ⟨scope, statements, some tail⟩ before with
    | error failure =>
      rw [body] at checked
      change Except.error _ = Except.ok _ at checked
      cases checked
    | ok answer =>
      rcases answer with ⟨actual, next⟩
      simp only [body, Except.bind] at checked
      unfold_scalar_typing_helpers
      cases same : actual == expected with
      | false =>
        simp only [same, Bool.false_eq_true, ↓reduceIte] at checked
        change Except.error _ = Except.ok _ at checked
        cases checked
      | true =>
        simp [same, pure, StateT.pure] at checked
        obtain ⟨rfl, rfl⟩ := checked
        exact ⟨expected, rfl, body, beq_iff_eq.mp same⟩

#print axioms typeExpr_blockE_tail
end Goose.Proofs.ConstructionAcceptedExecution
