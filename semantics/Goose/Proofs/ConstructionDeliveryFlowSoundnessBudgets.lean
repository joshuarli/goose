import Goose.Proofs.ConstructionDeliveryFlowSoundnessStatic

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

abbrev statementsQueryBudget (statements : List Stmt) : Nat :=
  (fun {budget : Nat}
    (_ : ∀ fuel other, budget ≤ fuel → budget ≤ other → statementsFlows fuel statements = statementsFlows other statements) => budget)
    (statementsFlow_budget statements)

abbrev statementQueryBudget (statement : Stmt) : Nat :=
  (fun {budget : Nat}
    (_ : ∀ fuel other, budget ≤ fuel → budget ≤ other → statementFlows fuel statement = statementFlows other statement) => budget)
    (statementFlow_budget statement)

abbrev expressionListQueryBudget (expressions : List Expr) : Nat :=
  (fun {budget : Nat}
    (_ : ∀ fuel other, budget ≤ fuel → budget ≤ other → expressionsFlows fuel expressions = expressionsFlows other expressions) => budget)
    (expressionsFlow_budget expressions)

abbrev placeQueryBudget (place : Place) : Nat :=
  (fun {budget : Nat}
    (_ : ∀ fuel other, budget ≤ fuel → budget ≤ other → placeFlows fuel place = placeFlows other place) => budget)
    (placeFlow_budget place)

abbrev viewQueryBudget (view : View) : Nat :=
  (fun {budget : Nat}
    (_ : ∀ fuel other, budget ≤ fuel → budget ≤ other → viewFlows fuel view = viewFlows other view) => budget)
    (viewFlow_budget view)

abbrev boundQueryBudget (bound : Bound) : Nat :=
  (fun {budget : Nat}
    (_ : ∀ fuel other, budget ≤ fuel → budget ≤ other → boundFlows fuel bound = boundFlows other bound) => budget)
    (boundFlow_budget bound)

abbrev argumentsQueryBudget (arguments : List Arg) : Nat :=
  (fun {budget : Nat}
    (_ : ∀ fuel other, budget ≤ fuel → budget ≤ other → argumentsFlows fuel arguments = argumentsFlows other arguments) => budget)
    (argumentsFlow_budget arguments)

abbrev argumentQueryBudget (argument : Arg) : Nat :=
  (fun {budget : Nat}
    (_ : ∀ fuel other, budget ≤ fuel → budget ≤ other → argumentFlows fuel argument = argumentFlows other argument) => budget)
    (argumentFlow_budget argument)

abbrev printArgumentsQueryBudget (arguments : List PrintArg) : Nat :=
  (fun {budget : Nat}
    (_ : ∀ fuel other, budget ≤ fuel → budget ≤ other → printArgumentsFlows fuel arguments = printArgumentsFlows other arguments) => budget)
    (printArgumentsFlow_budget arguments)

abbrev printArgumentQueryBudget (argument : PrintArg) : Nat :=
  (fun {budget : Nat}
    (_ : ∀ fuel other, budget ≤ fuel → budget ≤ other → printArgumentFlows fuel argument = printArgumentFlows other argument) => budget)
    (printArgumentFlow_budget argument)

theorem statementsFlows_stable (statements : List Stmt) (fuel : Nat) (enough : statementsQueryBudget statements ≤ fuel) :
    statementsFlows fuel statements = statementsFlows (statementsQueryBudget statements) statements :=
  statementsFlow_budget statements fuel (statementsQueryBudget statements) enough (Nat.le_refl _)

theorem statementFlows_stable (statement : Stmt) (fuel : Nat) (enough : statementQueryBudget statement ≤ fuel) :
    statementFlows fuel statement = statementFlows (statementQueryBudget statement) statement :=
  statementFlow_budget statement fuel (statementQueryBudget statement) enough (Nat.le_refl _)

theorem expressionsFlows_stable (expressions : List Expr) (fuel : Nat) (enough : expressionListQueryBudget expressions ≤ fuel) :
    expressionsFlows fuel expressions = expressionsFlows (expressionListQueryBudget expressions) expressions :=
  expressionsFlow_budget expressions fuel (expressionListQueryBudget expressions) enough (Nat.le_refl _)

theorem placeFlows_stable (place : Place) (fuel : Nat) (enough : placeQueryBudget place ≤ fuel) :
    placeFlows fuel place = placeFlows (placeQueryBudget place) place :=
  placeFlow_budget place fuel (placeQueryBudget place) enough (Nat.le_refl _)

theorem viewFlows_stable (view : View) (fuel : Nat) (enough : viewQueryBudget view ≤ fuel) :
    viewFlows fuel view = viewFlows (viewQueryBudget view) view :=
  viewFlow_budget view fuel (viewQueryBudget view) enough (Nat.le_refl _)

theorem boundFlows_stable (bound : Bound) (fuel : Nat) (enough : boundQueryBudget bound ≤ fuel) :
    boundFlows fuel bound = boundFlows (boundQueryBudget bound) bound :=
  boundFlow_budget bound fuel (boundQueryBudget bound) enough (Nat.le_refl _)

theorem argumentsFlows_stable (arguments : List Arg) (fuel : Nat) (enough : argumentsQueryBudget arguments ≤ fuel) :
    argumentsFlows fuel arguments = argumentsFlows (argumentsQueryBudget arguments) arguments :=
  argumentsFlow_budget arguments fuel (argumentsQueryBudget arguments) enough (Nat.le_refl _)

theorem argumentFlows_stable (argument : Arg) (fuel : Nat) (enough : argumentQueryBudget argument ≤ fuel) :
    argumentFlows fuel argument = argumentFlows (argumentQueryBudget argument) argument :=
  argumentFlow_budget argument fuel (argumentQueryBudget argument) enough (Nat.le_refl _)

theorem printArgumentsFlows_stable (arguments : List PrintArg) (fuel : Nat) (enough : printArgumentsQueryBudget arguments ≤ fuel) :
    printArgumentsFlows fuel arguments = printArgumentsFlows (printArgumentsQueryBudget arguments) arguments :=
  printArgumentsFlow_budget arguments fuel (printArgumentsQueryBudget arguments) enough (Nat.le_refl _)

theorem printArgumentFlows_stable (argument : PrintArg) (fuel : Nat) (enough : printArgumentQueryBudget argument ≤ fuel) :
    printArgumentFlows fuel argument = printArgumentFlows (printArgumentQueryBudget argument) argument :=
  printArgumentFlow_budget argument fuel (printArgumentQueryBudget argument) enough (Nat.le_refl _)

theorem expressionFlows_stable (expression : Expr) (fuel : Nat) (enough : expressionQueryBudget expression ≤ fuel) :
    expressionFlows fuel expression = expressionFlows (expressionQueryBudget expression) expression :=
  expressionFlow_budget expression fuel (expressionQueryBudget expression) enough (Nat.le_refl _)

theorem blockFlows_stable (block : Block) (fuel : Nat) (enough : blockQueryBudget block ≤ fuel) :
    blockFlows fuel block = blockFlows (blockQueryBudget block) block :=
  blockFlow_budget block fuel (blockQueryBudget block) enough (Nat.le_refl _)

theorem expressionQueryBudget_positive (expression : Expr) : 0 < expressionQueryBudget expression := by
  cases expression <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _

theorem blockQueryBudget_positive (block : Block) : 0 < blockQueryBudget block := by
  cases block with
  | mk scope statements tail =>
      cases tail <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _

theorem statementsQueryBudget_positive (statements : List Stmt) : 0 < statementsQueryBudget statements := by
  cases statements <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _

theorem statementQueryBudget_positive (statement : Stmt) : 0 < statementQueryBudget statement := by
  cases statement
  case ret expression origin =>
    cases expression <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _
  case ifS condition yes no origin =>
    cases no <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _
  case resize owner size fill origin =>
    cases fill <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _
  all_goals change 0 < _ + 1
  all_goals exact Nat.zero_lt_succ _

theorem expressionListQueryBudget_positive (expressions : List Expr) : 0 < expressionListQueryBudget expressions := by
  cases expressions <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _

theorem placeQueryBudget_positive (place : Place) : 0 < placeQueryBudget place := by
  cases place <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _

theorem viewQueryBudget_positive (view : View) : 0 < viewQueryBudget view := by
  cases view <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _

theorem boundQueryBudget_positive (bound : Bound) : 0 < boundQueryBudget bound := by
  cases bound <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _

theorem argumentsQueryBudget_positive (arguments : List Arg) : 0 < argumentsQueryBudget arguments := by
  cases arguments <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _

theorem argumentQueryBudget_positive (argument : Arg) : 0 < argumentQueryBudget argument := by
  cases argument <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _

theorem printArgumentsQueryBudget_positive (arguments : List PrintArg) : 0 < printArgumentsQueryBudget arguments := by
  cases arguments <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _

theorem printArgumentQueryBudget_positive (argument : PrintArg) : 0 < printArgumentQueryBudget argument := by
  cases argument <;> change 0 < _ + 1 <;> exact Nat.zero_lt_succ _

#print axioms statementsFlows_stable
#print axioms statementFlows_stable
#print axioms expressionsFlows_stable
#print axioms placeFlows_stable
#print axioms viewFlows_stable
#print axioms boundFlows_stable
#print axioms argumentsFlows_stable
#print axioms argumentFlows_stable
#print axioms printArgumentsFlows_stable
#print axioms printArgumentFlows_stable
#print axioms expressionFlows_stable
#print axioms blockFlows_stable

end Goose.Proofs.ConstructionDelivery
