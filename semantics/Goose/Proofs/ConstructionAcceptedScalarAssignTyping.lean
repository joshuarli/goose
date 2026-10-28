import Goose.Proofs.ConstructionAcceptedScalarWriteRuntime
import Lean.Elab.Tactic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def assignTypingHelperName (name : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Typing") 0) "Goose") "Construct") name

elab "unfold_assign_typing_helpers" : tactic => do
  let one := Lean.mkIdent (assignTypingHelperName "one")
  let require := Lean.mkIdent (assignTypingHelperName "require")
  let fail := Lean.mkIdent (assignTypingHelperName "fail")
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $one $require $fail at *))

elab "unfold_place_typing_helpers" : tactic => do
  let lookup := Lean.mkIdent (assignTypingHelperName "lookupVariable")
  let fail := Lean.mkIdent (assignTypingHelperName "fail")
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $lookup $fail at *))

private theorem assignTyping_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem typeStatement_scalarAssign (fuel : Nat) (environment next : TypingEnv) (place : Place)
    (expression : Expr) (origin before after : Nat) (form : AcceptedBinaryExpression expression)
    (typed : typeStatement (fuel + 1) environment (.assign place expression origin) before = .ok (next, after)) :
    ∃ ty writable binding middle expressionAfter,
      typePlace fuel environment place before = .ok ((ty, writable, binding), middle) ∧
      typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
        expression middle = .ok ([ty], expressionAfter) ∧
      ty.flat = true ∧ writable = true ∧ next = environment ∧ after = expressionAfter := by
  simp only [typeStatement, bind, StateT.bind] at typed
  change Except.bind (typePlace fuel environment place before) _ = _ at typed
  obtain ⟨placeResult, placeTyped, remaining⟩ := assignTyping_bind_success _ _ _ typed
  obtain ⟨⟨ty, writable, binding⟩, middle⟩ := placeResult
  change Except.bind (typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
    expression middle) _ = _ at remaining
  obtain ⟨expressionResult, expressionTyped, remaining⟩ := assignTyping_bind_success _ _ _ remaining
  obtain ⟨expressionTypes, expressionAfter⟩ := expressionResult
  obtain ⟨expressionTy, sameTypes⟩ := typeExpr_scalar_singleton form fuel
    { environment with use := .ordinary, request := .value, resultRequests := [] } middle expressionAfter expressionTypes expressionTyped
  subst expressionTypes
  unfold_assign_typing_helpers
  simp only [pure, StateT.pure, Except.pure, Except.bind] at remaining
  cases condition : (ty.flat && (ty == expressionTy) && writable) with
  | false =>
    simp only [condition, Bool.false_eq_true, ↓reduceIte] at remaining
    change Except.error _ = Except.ok _ at remaining
    cases remaining
  | true =>
    have facts : (ty.flat = true ∧ ty = expressionTy) ∧ writable = true := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using condition
    obtain ⟨⟨flat, same⟩, write⟩ := facts
    subst expressionTy
    simp only [condition, ↓reduceIte, pure, StateT.pure, Except.pure] at remaining
    cases remaining
    exact ⟨ty, writable, binding, middle, after, placeTyped, expressionTyped, flat, write, rfl, rfl⟩

theorem typePlace_local_scalarFacts (fuel : Nat) (environment : TypingEnv) (id before after : Nat)
    (ty : Ty) (writable binding : Bool)
    (checked : typePlace fuel environment (.var id) before = .ok ((ty, writable, binding), after)) :
    ∃ descriptor, id ∈ environment.visible ∧ environment.variables[id]? = some descriptor ∧
      ty = descriptor.ty ∧ writable = (descriptor.kind == .mutable) ∧ after = before := by
  cases fuel with
  | zero =>
    simp only [typePlace] at checked
    change Except.error _ = Except.ok _ at checked
    cases checked
  | succ fuel =>
    simp only [typePlace, bind, StateT.bind] at checked
    unfold_place_typing_helpers
    cases visible : environment.visible.contains id with
    | false =>
      simp only [visible, Bool.not_false, ↓reduceIte] at checked
      change Except.error _ = Except.ok _ at checked
      cases checked
    | true =>
      cases declared : environment.variables[id]? with
      | none =>
        simp only [visible, Bool.not_true, ↓reduceIte, declared] at checked
        change Except.error _ = Except.ok _ at checked
        cases checked
      | some descriptor =>
        simp only [visible, Bool.not_true, ↓reduceIte, declared, bind, StateT.bind, pure, StateT.pure,
          Except.pure, Except.bind] at checked
        cases checked
        exact ⟨descriptor, by simpa using visible, rfl, rfl, rfl, rfl⟩

theorem typePlace_global_scalarFacts (fuel : Nat) (environment : TypingEnv) (id before after : Nat)
    (ty : Ty) (writable binding : Bool)
    (checked : typePlace fuel environment (.global id) before = .ok ((ty, writable, binding), after)) :
    ∃ descriptor, id < environment.globalLimit ∧ environment.module.globals[id]? = some descriptor ∧
      ty = descriptor.ty ∧ writable = (descriptor.kind == .mutable) ∧ after = before := by
  cases fuel with
  | zero =>
    simp only [typePlace] at checked
    change Except.error _ = Except.ok _ at checked
    cases checked
  | succ fuel =>
    simp only [typePlace, bind, StateT.bind] at checked
    by_cases inside : id < environment.globalLimit
    · have outside : ¬ id ≥ environment.globalLimit := by omega
      cases declared : environment.module.globals[id]? with
      | none =>
        simp only [outside, ↓reduceIte, declared] at checked
        change Except.error _ = Except.ok _ at checked
        cases checked
      | some descriptor =>
        simp only [outside, ↓reduceIte, declared, bind, StateT.bind, pure, StateT.pure,
          Except.pure, Except.bind] at checked
        cases checked
        exact ⟨descriptor, inside, rfl, rfl, rfl, rfl⟩
    · have outside : id ≥ environment.globalLimit := by omega
      simp only [outside, ↓reduceIte] at checked
      change Except.error _ = Except.ok _ at checked
      cases checked

#print axioms typePlace_global_scalarFacts
#print axioms typePlace_local_scalarFacts
#print axioms typeStatement_scalarAssign
end Goose.Proofs.ConstructionAcceptedExecution
