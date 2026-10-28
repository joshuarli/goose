import Goose.Proofs.ConstructionAcceptedNestedChecker
import Goose.Proofs.ConstructionAcceptedGlobalAssignFlow

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

mutual
inductive NestedScalarExpression : Expr → Prop
  | scalar {expression : Expr} (form : AcceptedBinaryExpression expression) : NestedScalarExpression expression
  | conditional {condition : Expr} {yes no : Block} (origin : Nat)
      (conditionForm : NestedScalarExpression condition) (yesForm : NestedScalarBlock yes) (noForm : NestedScalarBlock no) :
      NestedScalarExpression (.ifE condition yes no origin)

inductive NestedScalarBlock : Block → Prop
  | block (scope : Nat) (statements : List Stmt) (tail : Expr)
      (statementsForm : NestedScalarStatements statements) (tailForm : NestedScalarExpression tail) :
      NestedScalarBlock ⟨scope, statements, some tail⟩

inductive NestedScalarStatements : List Stmt → Prop
  | nil : NestedScalarStatements []
  | expression (expression : Expr) (origin : Nat) (rest : List Stmt)
      (form : NestedScalarExpression expression) (tail : NestedScalarStatements rest) :
      NestedScalarStatements (.expr expression origin :: rest)
  | assign (id : Nat) (expression : Expr) (origin : Nat) (rest : List Stmt)
      (form : NestedScalarExpression expression) (tail : NestedScalarStatements rest) :
      NestedScalarStatements (.assign (.global id) expression origin :: rest)
end

mutual
theorem nestedScalarExpressionFlow_next {expression : Expr} (form : NestedScalarExpression expression)
    (fuel : Nat) : nextFlowPrivate ∈ expressionFlowPrivate fuel expression := by
  cases form with
  | scalar form => exact recursiveScalarFlow_next form fuel
  | conditional origin conditionForm yesForm noForm =>
    cases fuel with
    | zero => flow_simp
    | succ fuel =>
      flow_simp
      refine ⟨nextFlowPrivate, nestedScalarExpressionFlow_next conditionForm fuel, ?_⟩
      simp only [↓reduceIte, List.mem_append]
      exact Or.inl (nestedScalarBlockFlow_next yesForm fuel)
termination_by fuel

theorem nestedScalarBlockFlow_next {block : Block} (form : NestedScalarBlock block)
    (fuel : Nat) : nextFlowPrivate ∈ blockFlowPrivate fuel block := by
  cases form with
  | block scope statements tail statementsForm tailForm =>
    cases fuel with
    | zero => flow_simp
    | succ fuel =>
      flow_simp
      exact ⟨nextFlowPrivate, nestedScalarStatementsFlow_next statementsForm fuel,
        nestedScalarExpressionFlow_next tailForm fuel⟩
termination_by fuel

theorem nestedScalarStatementsFlow_next {statements : List Stmt} (form : NestedScalarStatements statements)
    (fuel : Nat) : nextFlowPrivate ∈ statementsFlowPrivate fuel statements := by
  cases form with
  | nil => cases fuel <;> assign_flow_simp
  | expression expression origin rest expressionForm tailForm =>
    cases fuel with
    | zero => assign_flow_simp
    | succ fuel =>
      cases fuel with
      | zero => assign_flow_simp
      | succ fuel =>
        assign_flow_simp
        exact ⟨nextFlowPrivate, nestedScalarExpressionFlow_next expressionForm fuel,
          nestedScalarStatementsFlow_next tailForm (fuel + 1)⟩
  | assign id expression origin rest expressionForm tailForm =>
    cases fuel with
    | zero => assign_flow_simp
    | succ fuel =>
      cases fuel with
      | zero => assign_flow_simp
      | succ fuel =>
        assign_flow_simp
        cases fuel with
        | zero => flow_simp; exact nestedScalarStatementsFlow_next tailForm 1
        | succ fuel =>
          flow_simp
          exact ⟨nextFlowPrivate, nestedScalarExpressionFlow_next expressionForm (fuel + 1),
            nestedScalarStatementsFlow_next tailForm (fuel + 2)⟩
termination_by fuel
end

theorem nestedScalarBlock_notEscapes {block : Block} (form : NestedScalarBlock block) (fuel : Nat) :
    blockEscapes fuel block = false := by
  simp only [blockEscapes]
  simpa using nestedScalarBlockFlow_next form fuel

mutual
theorem nestedScalarExpression_singleton {expression : Expr} (form : NestedScalarExpression expression)
    (fuel : Nat) (environment : TypingEnv) (before after : Nat) (types : List Ty)
    (typed : typeExpr fuel environment expression before = .ok (types, after)) : ∃ ty, types = [ty] := by
  cases form with
  | scalar form => exact typeExpr_scalar_singleton form fuel environment before after types typed
  | conditional origin conditionForm yesForm noForm =>
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      obtain ⟨conditionAfter, yesTypes, yesAfter, noTypes, noAfter, conditionTyped, yesTyped, noTyped⟩ :=
        typeExpr_if_branches fuel environment _ _ _ origin before after types typed
      obtain ⟨ty, yesSingleton⟩ := nestedScalarBlock_singleton yesForm fuel environment conditionAfter yesAfter yesTypes yesTyped
      have same := typeExpr_if_nonEscaping_result fuel environment _ _ _ origin before after conditionAfter yesAfter noAfter
        types yesTypes noTypes typed conditionTyped yesTyped noTyped
        (nestedScalarBlock_notEscapes yesForm fuel) (nestedScalarBlock_notEscapes noForm fuel)
      exact ⟨ty, same.trans yesSingleton⟩
termination_by fuel

theorem nestedScalarBlock_singleton {block : Block} (form : NestedScalarBlock block)
    (fuel : Nat) (environment : TypingEnv) (before after : Nat) (types : List Ty)
    (typed : typeBlock fuel environment block before = .ok (types, after)) : ∃ ty, types = [ty] := by
  cases form with
  | block scope statements tail statementsForm tailForm =>
    cases fuel with
    | zero => change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      simp only [typeBlock, bind, StateT.bind] at typed
      cases statementsTyped : typeStatements fuel { environment with scope := scope } statements before with
      | error failure => rw [statementsTyped] at typed; cases typed
      | ok result =>
        obtain ⟨next, middle⟩ := result
        rw [statementsTyped] at typed
        change typeExpr fuel next tail middle = .ok (types, after) at typed
        exact nestedScalarExpression_singleton tailForm fuel next middle after types typed
termination_by fuel
end

#print axioms nestedScalarExpression_singleton
#print axioms nestedScalarBlock_singleton
#print axioms nestedScalarBlock_notEscapes
#print axioms nestedScalarExpressionFlow_next
#print axioms nestedScalarBlockFlow_next
#print axioms nestedScalarStatementsFlow_next

end Goose.Proofs.ConstructionAcceptedExecution
