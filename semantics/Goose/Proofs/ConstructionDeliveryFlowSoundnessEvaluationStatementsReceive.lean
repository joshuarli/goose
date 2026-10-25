import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationStatementsWhole

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem controlFlow_mapMLoop_normal (items : List α) (action : α → EvalM β)
    (body : ∀ item, ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (action item))
    (accumulator : List β) :
    ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (List.mapM.loop action items accumulator) := by
  induction items generalizing accumulator with
  | nil => exact controlFlow_pure _ _ _ (List.mem_singleton_self _)
  | cons item rest ih =>
    change ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (do
      let value ← action item
      List.mapM.loop action rest (value :: accumulator))
    apply controlFlow_prefix
    · exact body item
    · intro value; exact ih (value :: accumulator)

theorem controlFlow_listMapM_normal (items : List α) (action : α → EvalM β)
    (body : ∀ item, ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (action item)) :
    ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (items.mapM action) :=
  controlFlow_mapMLoop_normal items action body []

local macro "receive_normal" : tactic => `(tactic|
  repeat' first
    | (solve | evaluation_values_leaf)
    | exact controlFlow_normal _ (breakFrame_materializedDestination _ _ _ _ _ _ _) (neverJumps_materializedDestination _ _ _ _ _ _ _)
    | (with_reducible apply controlFlow_listMapM_normal)
    | (with_reducible apply controlFlow_prefix)
    | exact controlFlow_pure _ _ _ (List.mem_singleton_self _)
    | exact controlFlow_stop _ _ _
    | evaluation_values_zeta
    | evaluation_values_intro
    | split)

theorem evaluationControl_statement_receive_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (localVars : List Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.receive localVars expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.receive localVars expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.receive localVars expression origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (expressionFlows staticFuel expression) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_prefix
    · receive_normal
    · intro channels
      apply controlFlow_suffix
      · exact previous.produce environment channels expression staticFuel (by omega)
      · intro carriers
        split
        · exact controlFlow_stop _ _ _
        · apply controlFlow_prefix
          · receive_normal
          · intro converted
            apply controlFlow_prefix
            · evaluation_values_normal
            · intro ignored
              apply controlFlow_prefix
              · apply controlFlow_normal
                · apply breakFrame_listForIn
                  intro pair ignored
                  rcases pair with ⟨localVar, carrier⟩
                  repeat' first
                    | (solve | evaluation_values_frame)
                    | apply breakFrame_bind
                    | evaluation_values_intro
                · apply neverJumps_forIn
                  intro pair ignored
                  rcases pair with ⟨localVar, carrier⟩
                  repeat' first
                    | (solve | evaluation_values_noJump)
                    | apply neverJumps_bind
                    | evaluation_values_intro
              · intro ignored
                exact controlFlow_pure _ _ _ (List.mem_singleton_self _)

#print axioms controlFlow_listMapM_normal
#print axioms evaluationControl_statement_receive_succ

end Goose.Proofs.ConstructionDelivery
