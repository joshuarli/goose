import Goose.Proofs.ConstructionAcceptedGlobalAssignBlock

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

private def statementFlowName (name : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Declarations") 0) "Goose") "Construct") name

macro "assignStatementFlowPrivate" : term => pure (Lean.mkIdent (statementFlowName "statementFlow"))

macro "assign_flow_simp" : tactic => do
  let statement := Lean.mkIdent (statementFlowName "statementFlow")
  let statements := Lean.mkIdent (statementFlowName "statementsFlow")
  let block := Lean.mkIdent (statementFlowName "blockFlow")
  let cont := Lean.mkIdent (statementFlowName "continueFlow")
  `(tactic| simp [$statement:ident, $statements:ident, $block:ident, $cont:ident])

theorem globalAssignStatementsFlow_next {statements : List Stmt} (form : GlobalScalarStatements statements) :
    ∀ fuel, nextFlowPrivate ∈ statementsFlowPrivate fuel statements := by
  induction form with
  | nil => intro fuel; cases fuel <;> assign_flow_simp
  | expression expression origin rest expressionForm tail ih =>
    intro fuel
    cases fuel with
    | zero => assign_flow_simp
    | succ fuel =>
      cases fuel with
      | zero => assign_flow_simp
      | succ fuel =>
        assign_flow_simp
        exact ⟨nextFlowPrivate, recursiveScalarFlow_next expressionForm fuel, ih (fuel + 1)⟩
  | assign id expression origin rest expressionForm tail ih =>
    intro fuel
    cases fuel with
    | zero => assign_flow_simp
    | succ fuel =>
      cases fuel with
      | zero => assign_flow_simp
      | succ fuel =>
        assign_flow_simp
        cases fuel with
        | zero => flow_simp; exact ih 1
        | succ fuel =>
          flow_simp
          exact ⟨nextFlowPrivate, recursiveScalarFlow_next expressionForm (fuel + 1), ih (fuel + 2)⟩

theorem globalAssignStatementsBlock_notEscapes {statements : List Stmt} (form : GlobalScalarStatements statements)
    {tail : Expr} (tailForm : AcceptedBinaryExpression tail) (scope fuel : Nat) :
    blockEscapes fuel ⟨scope, statements, some tail⟩ = false := by
  cases fuel with
  | zero => simp only [blockEscapes]; assign_flow_simp
  | succ fuel =>
    simp only [blockEscapes]
    assign_flow_simp
    exact ⟨nextFlowPrivate, globalAssignStatementsFlow_next form fuel, recursiveScalarFlow_next tailForm fuel⟩

theorem typeExpr_if_globalAssignBranches (fuel : Nat) (environment : TypingEnv) (condition yes no : Expr) (yesStatements noStatements : List Stmt)
    (yesScope noScope origin before after conditionAfter yesAfter noAfter : Nat) (ty yesTy noTy : Ty)
    (checked : typeExpr (fuel + 1) environment (.ifE condition ⟨yesScope, yesStatements, some yes⟩ ⟨noScope, noStatements, some no⟩ origin) before = .ok ([ty], after))
    (conditionTyped : typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
      condition before = .ok ([.bool], conditionAfter))
    (yesTyped : typeBlock fuel environment ⟨yesScope, yesStatements, some yes⟩ conditionAfter = .ok ([yesTy], yesAfter))
    (noTyped : typeBlock fuel environment ⟨noScope, noStatements, some no⟩ yesAfter = .ok ([noTy], noAfter))
    (yesForm : AcceptedBinaryExpression yes) (noForm : AcceptedBinaryExpression no)
    (yesStatementsForm : GlobalScalarStatements yesStatements) (noStatementsForm : GlobalScalarStatements noStatements) :
    yesTy = ty ∧ noTy = ty := by
  have yesNoEscape := globalAssignStatementsBlock_notEscapes yesStatementsForm yesForm yesScope fuel
  have noNoEscape := globalAssignStatementsBlock_notEscapes noStatementsForm noForm noScope fuel
  simp only [typeExpr, bind, StateT.bind] at checked
  change (Except.bind (typeExpr fuel
    { environment with use := .ordinary, request := .value, resultRequests := [] } condition before) _) = _ at checked
  simp only [conditionTyped, Except.bind] at checked
  change (Except.bind (typeBlock fuel environment ⟨yesScope, yesStatements, some yes⟩ conditionAfter) _) = _ at checked
  simp only [yesTyped, Except.bind] at checked
  change (Except.bind (typeBlock fuel environment ⟨noScope, noStatements, some no⟩ yesAfter) _) = _ at checked
  simp only [noTyped, Except.bind, yesNoEscape, noNoEscape, Bool.false_and] at checked
  unfold_typing_require
  by_cases same : yesTy = noTy
  · subst noTy
    simp [bind, StateT.bind, pure, StateT.pure, Except.pure, Except.bind] at checked
    exact ⟨checked.1, checked.1⟩
  · simp [same, bind, StateT.bind, pure, StateT.pure, Except.pure, Except.bind] at checked
    change Except.error _ = Except.ok _ at checked
    cases checked

#print axioms typeExpr_if_globalAssignBranches
#print axioms globalAssignStatementsFlow_next
#print axioms globalAssignStatementsBlock_notEscapes
end Goose.Proofs.ConstructionAcceptedExecution
