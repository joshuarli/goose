import Goose.Construct.Declarations

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

abbrev blockFlows (fuel : Nat) (block : Block) :=
  (fun {α : Type} {left right : α} (_ : left = right) => left)
    (blockFlow_transition fuel block)

abbrev statementFlows (fuel : Nat) (statement : Stmt) :=
  (fun {α : Type} {left right : α} (_ : left = right) => left)
    (statementFlow_transition fuel statement)

abbrev expressionFlows (fuel : Nat) (input : Expr) :=
  (fun {α : Type} {left right : α} (_ : left = right) => left)
    (expressionFlow_transition fuel input)

abbrev statementsFlows (fuel : Nat) (input : List Stmt) :=
  (fun {α : Type} {left right : α} (_ : left = right) => left)
    (statementsFlow_transition fuel input)

abbrev expressionsFlows (fuel : Nat) (input : List Expr) :=
  (fun {α : Type} {left right : α} (_ : left = right) => left)
    (expressionsFlow_transition fuel input)

abbrev placeFlows (fuel : Nat) (input : Place) :=
  (fun {α : Type} {left right : α} (_ : left = right) => left)
    (placeFlow_transition fuel input)

abbrev viewFlows (fuel : Nat) (input : View) :=
  (fun {α : Type} {left right : α} (_ : left = right) => left)
    (viewFlow_transition fuel input)

abbrev boundFlows (fuel : Nat) (input : Bound) :=
  (fun {α : Type} {left right : α} (_ : left = right) => left)
    (boundFlow_transition fuel input)

abbrev argumentsFlows (fuel : Nat) (input : List Arg) :=
  (fun {α : Type} {left right : α} (_ : left = right) => left)
    (argumentsFlow_transition fuel input)

abbrev argumentFlows (fuel : Nat) (input : Arg) :=
  (fun {α : Type} {left right : α} (_ : left = right) => left)
    (argumentFlow_transition fuel input)

abbrev printArgumentsFlows (fuel : Nat) (input : List PrintArg) :=
  (fun {α : Type} {left right : α} (_ : left = right) => left)
    (printArgumentsFlow_transition fuel input)

abbrev printArgumentFlows (fuel : Nat) (input : PrintArg) :=
  (fun {α : Type} {left right : α} (_ : left = right) => left)
    (printArgumentFlow_transition fuel input)

abbrev StaticFlow :=
  (fun {α : Type} (_ : List α) => α) (blockFlows 0 (.mk 0 [] none))

abbrev normalFlow : StaticFlow :=
  (blockFlows 0 (.mk 0 [] none)).head (by decide)

abbrev valueBreakFlow : StaticFlow :=
  (statementFlows 1 (.breakValue (.bool true) 0)).head (by decide)

abbrev loopBreakFlow : StaticFlow :=
  (statementFlows 1 (.brk 0)).head (by decide)

abbrev continueLoopFlow : StaticFlow :=
  (statementFlows 1 (.cont 0)).head (by decide)

abbrev escapingFlow : StaticFlow :=
  (statementFlows 1 (.abort "" 0)).head (by decide)

abbrev continueFlows (first second : List StaticFlow) :=
  (fun {α : Type} {left right : α} (_ : left = right) => left)
    (continueFlow_transition first second)

theorem normalFlow_mem_continue (first second : List StaticFlow) :
    normalFlow ∈ continueFlows first second ↔ normalFlow ∈ first ∧ normalFlow ∈ second := by
  simp only [continueFlows, continueFlow_transition, List.mem_flatMap]
  constructor
  · rintro ⟨flow, present, reached⟩
    cases flow <;> simp_all [normalFlow, blockFlows, blockFlow_transition]
  · rintro ⟨present, reached⟩
    exact ⟨normalFlow, present, by simpa [normalFlow, blockFlows, blockFlow_transition] using reached⟩

theorem no_normal_iff_escapes (fuel : Nat) (block : Block) :
    blockEscapes fuel block = true ↔ normalFlow ∉ blockFlows fuel block := by
  simp only [blockEscapes, blockFlows, List.all_eq_true]
  constructor
  · intro every present
    have rejected := every _ present
    simp [normalFlow, blockFlows, blockFlow_transition] at rejected
  · intro absent flow present
    have different : flow ≠ normalFlow := by
      intro equal
      subst flow
      exact absent present
    simpa [normalFlow, blockFlows, blockFlow_transition] using different

theorem mem_continueFlows_first (first second : List StaticFlow) (flow : StaticFlow)
    (abrupt : flow ≠ normalFlow) (present : flow ∈ first) :
    flow ∈ continueFlows first second := by
  simp only [continueFlows, continueFlow_transition, List.mem_flatMap]
  refine ⟨flow, present, ?_⟩
  simpa [normalFlow, blockFlows, blockFlow_transition] using
    (show flow ∈ (if flow == normalFlow then second else [flow]) by
      simp [show ¬flow = normalFlow from abrupt])

theorem mem_continueFlows_second (first second : List StaticFlow) (flow : StaticFlow)
    (normal : normalFlow ∈ first) (present : flow ∈ second) :
    flow ∈ continueFlows first second := by
  simp only [continueFlows, continueFlow_transition, List.mem_flatMap]
  exact ⟨normalFlow, normal, by simpa [normalFlow, blockFlows, blockFlow_transition] using present⟩

theorem normalFlow_mem_statements_cons (fuel : Nat) (statement : Stmt) (rest : List Stmt) :
    normalFlow ∈ statementsFlows (fuel + 1) (statement :: rest) ↔
      normalFlow ∈ statementFlows fuel statement ∧ normalFlow ∈ statementsFlows fuel rest := by
  exact normalFlow_mem_continue _ _

theorem normalFlow_mem_block (fuel : Nat) (scope : Nat) (statements : List Stmt) (tail : Option Expr) :
    normalFlow ∈ blockFlows (fuel + 1) (.mk scope statements tail) ↔
      normalFlow ∈ statementsFlows fuel statements ∧
        (match tail with | none => True | some expression => normalFlow ∈ expressionFlows fuel expression) := by
  cases tail with
  | none =>
      change (normalFlow ∈ continueFlows (statementsFlows fuel statements) [normalFlow]) ↔
        normalFlow ∈ statementsFlows fuel statements ∧ True
      rw [normalFlow_mem_continue]
      simp
  | some expression => exact normalFlow_mem_continue _ _

theorem normalFlow_not_escaping (fuel : Nat) (block : Block)
    (present : normalFlow ∈ blockFlows fuel block) : blockEscapes fuel block = false := by
  cases classified : blockEscapes fuel block with
  | false => rfl
  | true => exact False.elim ((no_normal_iff_escapes fuel block).mp classified present)

#print axioms normalFlow_mem_continue
#print axioms no_normal_iff_escapes
#print axioms mem_continueFlows_first
#print axioms mem_continueFlows_second
#print axioms normalFlow_mem_statements_cons
#print axioms normalFlow_mem_block
#print axioms normalFlow_not_escaping

end Goose.Proofs.ConstructionDelivery
