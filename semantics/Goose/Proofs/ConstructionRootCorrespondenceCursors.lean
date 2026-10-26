import Goose.Construct.Roots

set_option Elab.async false

namespace Goose.Proofs.ConstructionRootCorrespondence
open Goose.Construct
open Goose.Core (VarId)

private theorem bind_success {action : P α} {next : α → P β} {before after : RState} {value : β}
    (checked : (action >>= next) before = .ok (value, after)) :
    ∃ result middle, action before = .ok (result, middle) ∧ next result middle = .ok (value, after) := by
  cases success : action before with
  | error error => simp [bind, StateT.bind, Except.bind, success] at checked
  | ok pair =>
    obtain ⟨result, middle⟩ := pair
    exact ⟨result, middle, rfl, by simpa [bind, StateT.bind, Except.bind, success] using checked⟩

private theorem get_state (state : RState) : (get : P RState) state = .ok (state, state) := rfl

private theorem modify_state (update : RState → RState) (state : RState) :
    (modify update : P PUnit) state = .ok (PUnit.unit, update state) := rfl

theorem rpStmts_cons {env : PEnv} {statement : Stmt} {rest : List Stmt} {before after : RState}
    (checked : rpStmts env (statement :: rest) before = .ok ((), after)) :
    ∃ middle, rpStmt env statement before = .ok ((), middle) ∧
      rpStmts env rest middle = .ok ((), after) := by
  obtain ⟨result, middle, first, remaining⟩ := bind_success checked
  cases result
  exact ⟨middle, first, remaining⟩

theorem rpBlockValue_body {env : PEnv} {scope : Nat} {statements : List Stmt}
    {value : Option Expr} {pre : List VarId} {before after : RState} {result : List RootRef × (Nat × Nat)}
    (checked : rpBlockValue env pre (.mk scope statements value) before = .ok (result, after)) :
    pre.all (fun id => before.nextVar ≤ id && id < before.nextVar + pre.length) = true ∧
    ∃ middle roots, rpStmts { env with scopes := scope :: env.scopes } statements
      { before with nextVar := before.nextVar + pre.length } = .ok ((), middle) ∧
      (match value with
        | none => (pure [] : P (List RootRef))
        | some expression => rpExpr { env with scopes := scope :: env.scopes } expression) middle =
          .ok (roots, after) ∧
      result = (if env.valueBlock == some scope then unionRoots roots after.valueBreakRoots else roots,
        (before.nextVar, after.nextVar)) := by
  unfold rpBlockValue at checked
  obtain ⟨initial, state0, initialChecked, checked⟩ := bind_success checked
  change Except.ok (before, before) = _ at initialChecked
  cases initialChecked
  split at checked
  next ordered =>
    obtain ⟨ignored, state1, guard, checked⟩ := bind_success checked
    change Except.ok ((), before) = _ at guard
    cases guard
    obtain ⟨ignored, state2, advanced, checked⟩ := bind_success checked
    change Except.ok ((), { before with nextVar := before.nextVar + pre.length }) = _ at advanced
    cases advanced
    obtain ⟨ignored, middle, statementsChecked, checked⟩ := bind_success checked
    obtain ⟨roots, state3, valueChecked, checked⟩ := bind_success checked
    obtain ⟨final, state4, finalChecked, checked⟩ := bind_success checked
    change Except.ok (state3, state3) = _ at finalChecked
    cases finalChecked
    obtain ⟨ignored, state5, blockChecked, checked⟩ := bind_success checked
    unfold liftV at blockChecked
    split at blockChecked
    next allowed success =>
      cases blockChecked
      change Except.ok (_, state3) = _ at checked
      cases checked
      exact ⟨ordered, middle, roots, statementsChecked, valueChecked, rfl⟩
    next denied error => cases blockChecked
  next unordered =>
    obtain ⟨ignored, state1, rejected, _⟩ := bind_success checked
    cases rejected

theorem rpStmt_letS_initializer {env : PEnv} {id : VarId} {expression : Expr} {origin : Nat}
    {before after : RState}
    (checked : rpStmt env (.letS id expression origin) before = .ok ((), after)) :
    id = before.nextVar ∧ ∃ roots middle,
      rpExpr { env with initializing := id :: env.initializing } expression
        { before with nextVar := before.nextVar + 1 } = .ok (roots, middle) ∧
      middle.eff.calls ⊆ after.eff.calls := by
  have ordered : id = before.nextVar := by
    by_cases ordered : id = before.nextVar
    · exact ordered
    · simp only [rpStmt, bind, StateT.bind, get_state, Except.bind, ite_eq_right ordered] at checked
      change Except.error _ = Except.ok ((), after) at checked
      cases checked
  refine ⟨ordered, ?_⟩
  cases expressionChecked : rpExpr { env with initializing := id :: env.initializing } expression
      { before with nextVar := before.nextVar + 1 } with
  | ok pair => exact ⟨pair.1, pair.2, rfl, rpStmt_letS_callsIncluded checked ordered expressionChecked⟩
  | error error =>
    simp only [rpStmt, bind, StateT.bind, get_state, Except.bind, ite_eq_left ordered, modify_state, expressionChecked, reduceCtorEq] at checked

theorem rpStmt_print_arguments {env : PEnv} {arguments : List PrintArg} {origin : Nat}
    {before after : RState}
    (checked : rpStmt env (.print arguments origin) before = .ok ((), after)) :
    ∃ middle, rpPrintArgs env arguments before = .ok ((), middle) := by
  obtain ⟨result, middle, argumentsChecked, _⟩ := bind_success checked
  cases result
  exact ⟨middle, argumentsChecked⟩

theorem rpPrintArgs_expression {env : PEnv} {expression : Expr} {rest : List PrintArg}
    {before after : RState}
    (checked : rpPrintArgs env (.expr expression :: rest) before = .ok ((), after)) :
    ∃ roots middle, rpExpr env expression before = .ok (roots, middle) ∧
      rpPrintArgs env rest middle = .ok ((), after) := by
  exact bind_success checked

theorem rpStmt_expression {env : PEnv} {expression : Expr} {origin : Nat}
    {before after : RState}
    (checked : rpStmt env (.expr expression origin) before = .ok ((), after)) :
    ∃ roots, rpExpr env expression before = .ok (roots, after) := by
  obtain ⟨roots, middle, expressionChecked, returned⟩ := bind_success checked
  change Except.ok ((), middle) = Except.ok ((), after) at returned
  cases returned
  exact ⟨roots, expressionChecked⟩

theorem rpExpr_call_argumentChecks {env : PEnv} {target : Goose.Core.ContextId} {arguments : List Arg}
    {origin : Goose.Core.OriginId} {before after : RState} {roots : List RootRef}
    (checked : rpExpr env (.call target arguments origin) before = .ok (roots, after)) :
    ∃ selected callee argumentRoots argumentAfter,
      env.mod.contexts[target]? = some selected ∧ env.mod.impls[selected.impl]? = some callee ∧
      rpArgs env arguments before = .ok (argumentRoots, argumentAfter) ∧
      checkContents env target arguments argumentRoots = .ok () := by
  unfold rpExpr at checked
  obtain ⟨argumentRoots, argumentAfter, argumentsChecked, checked⟩ := bind_success checked
  cases contextAt : env.mod.contexts[target]? with
  | none =>
    simp only [contextAt] at checked
    change Except.error _ = Except.ok (roots, after) at checked
    cases checked
  | some selected =>
    simp only [contextAt] at checked
    cases implementationAt : env.mod.impls[selected.impl]? with
    | none =>
      simp only [implementationAt] at checked
      change Except.error _ = Except.ok (roots, after) at checked
      cases checked
    | some callee =>
      simp only [implementationAt] at checked
      obtain ⟨ignored, state2, _, checked⟩ := bind_success checked
      obtain ⟨ignored, state3, contentsChecked, _⟩ := bind_success checked
      cases contents : checkContents env target arguments argumentRoots with
      | error error => simp [liftV, contents] at contentsChecked
      | ok value =>
        cases value
        refine ⟨selected, callee, argumentRoots, argumentAfter, ?_, ?_, argumentsChecked, ?_⟩
        · first | exact contextAt | rfl
        · first | exact implementationAt | rfl
        · first | exact contents | rfl

private theorem contents_forAll_at {α : Type} (inputs : List α) (action : α → Goose.Core.V Unit)
    (checked : Goose.Core.forAll inputs action = .ok ()) :
    ∀ input ∈ inputs, action input = .ok () := by
  induction inputs with
  | nil => intro input absent; cases absent
  | cons head rest ih =>
    cases first : action head with
    | error error => simp [Goose.Core.forAll, first, bind, Except.bind] at checked
    | ok value =>
      cases value
      have remaining : Goose.Core.forAll rest action = .ok () := by
        simpa only [Goose.Core.forAll, first, bind, Except.bind] using checked
      intro input member
      rcases List.mem_cons.mp member with equal | member
      · subst input
        exact first
      · exact ih remaining input member

theorem checkContents_at {env : PEnv} {target : Goose.Core.ContextId} {context : Context}
    {arguments : List Arg} {argumentRoots : List (List RootRef)}
    (selected : env.mod.contexts[target]? = some context)
    (checked : checkContents env target arguments argumentRoots = .ok ())
    (index : Nat) (bound : index < arguments.length) :
    checkContent env context arguments argumentRoots index = .ok () := by
  simp only [checkContents, selected] at checked
  exact contents_forAll_at _ _ checked index (List.mem_range.mpr bound)

end Goose.Proofs.ConstructionRootCorrespondence
