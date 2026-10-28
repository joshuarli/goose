import Goose.Proofs.ConstructionAcceptedConditionalBranches
import Lean.Elab.Tactic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct

elab "unfold_local_declare" : tactic => do
  let name := Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Typing") 0) "Goose") "Construct") "declare"
  let declaration := Lean.mkIdent name
  let checked := Lean.mkIdent `declared
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $declaration:ident at $checked:ident))

macro "declarePrivate" : term => do
  let name := Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Typing") 0) "Goose") "Construct") "declare"
  pure (Lean.mkIdent name)

theorem typeStatement_emptyVariables_noLet (fuel : Nat) (environment : TypingEnv) (id : Nat) (expression : Expr)
    (origin before after : Nat) (next : TypingEnv) (empty : environment.variables = #[]) :
    typeStatement fuel environment (.letS id expression origin) before ≠ .ok (next, after) := by
  intro checked
  cases fuel with
  | zero => change Except.error _ = Except.ok _ at checked; cases checked
  | succ fuel =>
    simp only [typeStatement, bind, StateT.bind] at checked
    change (Except.bind (declarePrivate environment id before) _) = _ at checked
    cases declared : declarePrivate environment id before with
    | error failure => simp only [declared, Except.bind] at checked; cases checked
    | ok result =>
      unfold_local_declare
      simp only [bind, StateT.bind] at declared
      change (Except.bind (Except.ok (before, before)) _) = Except.ok result at declared
      simp only [Except.bind] at declared
      split at declared
      · change Except.error _ = Except.ok _ at declared
        cases declared
      · simp only [empty, Array.getElem?_empty] at declared
        change Except.error _ = Except.ok _ at declared
        cases declared

theorem typeBlock_emptyVariables_noLeadingLet (fuel : Nat) (environment : TypingEnv) (scope id : Nat)
    (expression : Expr) (origin : Nat) (statements : List Stmt) (tail : Option Expr)
    (before after : Nat) (types : List Ty) (empty : environment.variables = #[]) :
    typeBlock (fuel + 2) environment ⟨scope, .letS id expression origin :: statements, tail⟩ before ≠ .ok (types, after) := by
  intro checked
  simp only [typeBlock, typeStatements, bind, StateT.bind] at checked
  cases first : typeStatement fuel { environment with scope := scope } (.letS id expression origin) before with
  | error failure => simp only [first, Except.bind] at checked; cases checked
  | ok result =>
    exact typeStatement_emptyVariables_noLet fuel { environment with scope := scope } id expression origin before
      result.2 result.1 empty first

theorem validated_globalConditional_noLeadingLet (config : EvalConfig) (accepted : AcceptedModule config)
    (id : Nat) (descriptor : Global) (present : config.module.globals[id]? = some descriptor)
    (condition : Expr) (yes no : Block) (origin : Nat)
    (shape : descriptor.init = .ifE condition yes no origin) :
    (∀ scope localId expression letOrigin statements tail,
      yes ≠ ⟨scope, .letS localId expression letOrigin :: statements, tail⟩) ∧
    (∀ scope localId expression letOrigin statements tail,
      no ≠ ⟨scope, .letS localId expression letOrigin :: statements, tail⟩) := by
  obtain ⟨ty, after, typed, adapts⟩ := validated_global_initializer_typing config.module id descriptor accepted.accepted present
  rw [shape] at typed
  let env := (scalarGlobalInitializerFrame config id 0 #[]).typing
  obtain ⟨_, yesTypes, yesAfter, noTypes, noAfter, _, yesTyped, noTyped⟩ :=
    typeExpr_if_branches 4095 env condition yes no origin 0 after [ty] typed
  constructor
  · intro scope localId expression letOrigin statements tail same
    subst yes
    exact typeBlock_emptyVariables_noLeadingLet 4093 env scope localId expression letOrigin statements tail _ _ yesTypes rfl yesTyped
  · intro scope localId expression letOrigin statements tail same
    subst no
    exact typeBlock_emptyVariables_noLeadingLet 4093 env scope localId expression letOrigin statements tail _ _ noTypes rfl noTyped

#print axioms validated_globalConditional_noLeadingLet
#print axioms typeBlock_emptyVariables_noLeadingLet
#print axioms typeStatement_emptyVariables_noLet
end Goose.Proofs.ConstructionAcceptedExecution
