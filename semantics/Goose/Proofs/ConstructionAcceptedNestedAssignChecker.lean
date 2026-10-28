import Goose.Proofs.ConstructionAcceptedNestedSyntax
import Goose.Proofs.ConstructionAcceptedGlobalAssignChecker

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private theorem nestedAssign_bind_success {ε α β : Type} (first : Except ε α) (next : α → Except ε β)
    (result : β) (checked : first.bind next = .ok result) :
    ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first with
  | error failure => cases checked
  | ok value => exact ⟨value, rfl, checked⟩

theorem typeStatement_nestedScalarAssign (fuel : Nat) (environment next : TypingEnv) (place : Place)
    (expression : Expr) (origin before after : Nat) (form : NestedScalarExpression expression)
    (typed : typeStatement (fuel + 1) environment (.assign place expression origin) before = .ok (next, after)) :
    ∃ ty writable binding middle expressionAfter,
      typePlace fuel environment place before = .ok ((ty, writable, binding), middle) ∧
      typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
        expression middle = .ok ([ty], expressionAfter) ∧
      ty.flat = true ∧ writable = true ∧ next = environment ∧ after = expressionAfter := by
  simp only [typeStatement, bind, StateT.bind] at typed
  change Except.bind (typePlace fuel environment place before) _ = _ at typed
  obtain ⟨placeResult, placeTyped, remaining⟩ := nestedAssign_bind_success _ _ _ typed
  obtain ⟨⟨ty, writable, binding⟩, middle⟩ := placeResult
  change Except.bind (typeExpr fuel { environment with use := .ordinary, request := .value, resultRequests := [] }
    expression middle) _ = _ at remaining
  obtain ⟨expressionResult, expressionTyped, remaining⟩ := nestedAssign_bind_success _ _ _ remaining
  obtain ⟨expressionTypes, expressionAfter⟩ := expressionResult
  obtain ⟨expressionTy, sameTypes⟩ := nestedScalarExpression_singleton form fuel
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

private theorem nestedAssign_addTargets_members (before added : List Target) (target : Target) :
    target ∈ addTargets before added ↔ target ∈ before ∨ target ∈ added := by
  induction added generalizing before with
  | nil => simp [addTargets]
  | cons selected rest ih =>
    simp only [addTargets, List.foldl_cons]
    split
    · rename_i retained
      change target ∈ addTargets before rest ↔ _
      rw [ih]
      have present : selected ∈ before := by simpa using retained
      simp only [List.mem_cons]
      constructor
      · intro member
        rcases member with member | member
        · exact Or.inl member
        · exact Or.inr (Or.inr member)
      · intro member
        rcases member with member | equal | member
        · exact Or.inl member
        · exact Or.inl (equal ▸ present)
        · exact Or.inr member
    · change target ∈ addTargets (before ++ [selected]) rest ↔ _
      rw [ih]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc]

theorem nestedAssign_operandEffects_included (environment : PEnv) (id : Nat) (expression : Expr) (origin : Nat)
    (before after middle : RState) (roots : List RootRef)
    (operand : rpExpr environment expression { before with eff := {} } = .ok (roots, middle))
    (checked : rpStmt environment (.assign (.global id) expression origin) before = .ok ((), after)) :
    EffectTargetsIncluded middle.eff after.eff := by
  have access := rpStmt_directAssign_accessTargets environment (.global id) expression origin before after middle roots
    (Or.inr ⟨id, rfl⟩) operand checked
  intro target member
  rw [access]
  simp only [Eff.accessTargets, List.mem_append] at member ⊢
  rcases member with ((reads | writes) | grows) | shrinks
  · exact Or.inl (Or.inl (Or.inl ((nestedAssign_addTargets_members _ _ _).2 (Or.inr reads))))
  · exact Or.inl (Or.inl (Or.inr ((nestedAssign_addTargets_members _ _ _).2 (Or.inl ((nestedAssign_addTargets_members _ _ _).2 (Or.inr writes))))))
  · exact Or.inl (Or.inr ((nestedAssign_addTargets_members _ _ _).2 (Or.inr grows)))
  · exact Or.inr ((nestedAssign_addTargets_members _ _ _).2 (Or.inr shrinks))

theorem checkedValue_nestedGlobalAssign_operand (fuel : Nat) (frame : ConstructionSourceFrame)
    (id : Nat) (expression : Expr) (origin : Nat) (form : NestedScalarExpression expression)
    (next : TypingEnv) (typingAfter : Nat) (rootsAfter : RState)
    (typed : typeStatement (fuel + 1) frame.typing (.assign (.global id) expression origin) frame.typingCounter = .ok (next, typingAfter))
    (rooted : rpStmt frame.source (.assign (.global id) expression origin) frame.rootCursor = .ok ((), rootsAfter))
    (available : GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff) :
    ∃ descriptor roots expressionTypingAfter expressionRootsAfter,
      frame.typing.module.globals[id]? = some descriptor ∧ id < frame.typing.globalLimit ∧ descriptor.kind = .mutable ∧
      descriptor.ty.flat = true ∧ next = frame.typing ∧ typingAfter = expressionTypingAfter ∧
      CheckedValue (scalarAssignmentOperandFrame frame fuel) expression descriptor.ty roots expressionTypingAfter expressionRootsAfter := by
  obtain ⟨ty, writable, binding, middle, expressionAfter, placeTyped, expressionTyped, flat, mutable, sameNext, sameAfter⟩ :=
    typeStatement_nestedScalarAssign fuel frame.typing next (.global id) expression origin frame.typingCounter typingAfter form typed
  obtain ⟨descriptor, inside, declared, sameTy, sameMutable, sameMiddle⟩ :=
    typePlace_global_scalarFacts fuel frame.typing id frame.typingCounter middle ty writable binding placeTyped
  subst middle ty
  have mutableDescriptor : descriptor.kind = .mutable := by
    rw [sameMutable] at mutable
    simpa using mutable
  obtain ⟨roots, expressionRootsAfter, expressionRooted⟩ := rpStmt_directAssign_operand frame.source (.global id) expression origin
    frame.rootCursor rootsAfter (Or.inr ⟨id, rfl⟩) rooted
  have included := nestedAssign_operandEffects_included frame.source id expression origin frame.rootCursor rootsAfter
    expressionRootsAfter roots expressionRooted rooted
  have operandAvailable : GlobalEffectsAvailable frame.interpretation frame.initialized expressionRootsAfter.eff := by
    intro target member global instantiates
    exact available target (included member) global instantiates
  exact ⟨descriptor, roots, expressionAfter, expressionRootsAfter, declared, inside, mutableDescriptor, flat, sameNext, sameAfter,
    ⟨expressionTyped, expressionRooted, operandAvailable⟩⟩

#print axioms checkedValue_nestedGlobalAssign_operand
#print axioms nestedAssign_operandEffects_included
#print axioms typeStatement_nestedScalarAssign
end Goose.Proofs.ConstructionAcceptedExecution
