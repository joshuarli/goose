import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluation
import Goose.Proofs.Exit

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem execBlock_normal_not_escaping (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (channels : List Channel) (body : Block) (before after : ExecutionState) (value : Value)
    (bounded : BreakTargetsBelowCounter before)
    (evaluated : execBlock fuel config environment pre channels body before = .ok (.normal value) after) :
    blockEscapes (blockQueryBudget body) body = false := by
  have checked := ((evaluationControlFlows fuel config).block environment pre channels body
    (blockQueryBudget body) (Nat.le_refl _)).outcome before bounded
  simp only [evaluated, ControlFlowOutcome, resultControlFlow] at checked
  exact normalFlow_not_escaping _ _ checked

theorem execResultBlock_normal_not_escaping (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (body : Block)
    (before after : ExecutionState) (value : Value) (carriers : List Carrier)
    (bounded : BreakTargetsBelowCounter before)
    (evaluated : execResultBlock fuel config environment channels body before = .ok (.normal value, carriers) after) :
    blockEscapes (blockQueryBudget body) body = false := by
  have checked := ((evaluationControlFlows fuel config).resultBlock environment channels body
    (blockQueryBudget body) (Nat.le_refl _)).outcome before bounded
  simp only [evaluated, ControlFlowOutcome, resultControlFlow] at checked
  exact normalFlow_not_escaping _ _ checked

theorem evalValue_jump_static (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (expression : Expr) (before after : ExecutionState)
    (id : Nat) (kind : JumpKind) (bounded : BreakTargetsBelowCounter before)
    (evaluated : evalValue fuel config environment expression before = .jump id kind after) :
    ∃ target ∈ before.breaks,
      before.breaks.find? (fun entry => entry.act == environment.act && some target.scope == some entry.scope) = some target ∧
      JumpScopeMatches target.scope kind ∧ target.id = id ∧
      jumpControlFlow target.scope kind ∈ expressionFlows (expressionQueryBudget expression) expression := by
  have checked := ((evaluationControlFlows fuel config).value environment expression
    (expressionQueryBudget expression) (Nat.le_refl _)).outcome before bounded
  simpa only [evaluated, ControlFlowOutcome] using checked

theorem runModule_break_stack_initial (fuel : Nat) (config : EvalConfig) :
    let after := Goose.Proofs.Exit.stepState (runModule fuel config .initial)
    after.breaks = [] ∧ BreakTargetsBelowCounter after := by
  have initialBounded : BreakTargetsBelowCounter .initial := by
    intro target present
    cases present
  have checked := runModule_breakFrame fuel config .initial initialBounded
  cases evaluated : runModule fuel config .initial <;> rw [evaluated] at checked
  all_goals change BreakStackFrame .initial _ at checked
  all_goals exact ⟨checked.stack, checked.bounded initialBounded⟩

#print axioms execBlock_normal_not_escaping
#print axioms execResultBlock_normal_not_escaping
#print axioms evalValue_jump_static
#print axioms runModule_break_stack_initial

end Goose.Proofs.ConstructionDelivery
