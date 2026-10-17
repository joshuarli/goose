import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationContext
import Goose.Proofs.ConstructionDeliveryFlowSoundnessDispatch
import Goose.Proofs.ConstructionDeliveryFlowSoundnessNoJumps

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem evaluationControl_statements_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (statements : List Stmt) (staticFuel : Nat) (enough : statementsQueryBudget statements ≤ staticFuel) :
    ControlFlowAction environment.act (statementsFlows staticFuel statements) resultControlFlow
      (execStmts (fuel + 1) config environment statements) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementsQueryBudget_positive statements) enough)
  | succ staticFuel =>
    cases statements with
    | nil =>
      simp only [execStmts]
      exact controlFlow_pure _ _ _ (List.mem_singleton_self _)
    | cons statement rest =>
      have budgets : statementQueryBudget statement + statementsQueryBudget rest + 1 ≤ staticFuel + 1 := enough
      have firstEnough : statementQueryBudget statement ≤ staticFuel := by omega
      have restEnough : statementsQueryBudget rest ≤ staticFuel := by omega
      simp only [execStmts]
      change ControlFlowAction environment.act
        (continueFlows (statementFlows staticFuel statement) (statementsFlows staticFuel rest)) resultControlFlow _
      apply controlFlow_dispatch (statementFlows staticFuel statement)
      · exact previous.statement environment statement staticFuel firstEnough
      · intro scope kind present
        exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal scope kind) present
      · intro flow present
        cases flow with
        | normal value =>
          apply controlFlow_mono _ _ _ _ ?_ (previous.statements environment rest staticFuel restEnough)
          intro nextFlow admitted
          exact mem_continueFlows_second _ _ _ present admitted
        | breaking value =>
          apply controlFlow_pure
          exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal .loop (.breakValue [])) present
        | continuing =>
          apply controlFlow_pure
          exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal .loop .continueLoop) present

theorem evaluationControl_block_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (block : Block)
    (staticFuel : Nat) (enough : blockQueryBudget block ≤ staticFuel) :
    ControlFlowAction environment.act (blockFlows staticFuel block) resultControlFlow
      (execBlock (fuel + 1) config environment pre channels block) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (blockQueryBudget_positive block) enough)
  | succ staticFuel =>
    cases block with
    | mk scope statements tail =>
      have statementsEnough : statementsQueryBudget statements ≤ staticFuel := by
        cases tail
        case none => change statementsQueryBudget statements + 1 + 1 ≤ staticFuel + 1 at enough; omega
        case some expression => change statementsQueryBudget statements + expressionQueryBudget expression + 1 ≤ staticFuel + 1 at enough; omega
      simp only [execBlock]
      apply controlFlow_prefix
      · exact controlFlow_normal _ breakFrame_freshScope neverJumps_freshScope
      · intro scopeInst
        try dsimp only
        apply controlFlow_withScope
        apply controlFlow_prefix
        · exact controlFlow_normal _ (breakFrame_bindAll _ _ _) (neverJumps_bindAll _ _ _)
        · intro ignored
          apply controlFlow_dispatch (statementsFlows staticFuel statements) _ resultControlFlow resultControlFlow
          · exact previous.statements { environment with scopes := (scope, scopeInst) :: environment.scopes } statements staticFuel statementsEnough
          · intro breakScope kind present
            cases tail with
            | none => exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal breakScope kind) present
            | some expression => exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal breakScope kind) present
          · intro flow present
            cases flow with
            | normal value =>
              cases tail with
              | none =>
                simp only
                apply controlFlow_pure
                exact mem_continueFlows_second _ _ _ present (List.mem_singleton_self _)
              | some expression =>
                simp only
                have expressionEnough : expressionQueryBudget expression ≤ staticFuel := by
                  change statementsQueryBudget statements + expressionQueryBudget expression + 1 ≤ staticFuel + 1 at enough
                  omega
                apply controlFlow_mono (expressionFlows staticFuel expression)
                · intro nextFlow admitted
                  exact mem_continueFlows_second _ _ _ present admitted
                · by_cases ready : channels.isEmpty = true
                  · simp only [ready]
                    apply controlFlow_map
                    exact previous.value { environment with scopes := (scope, scopeInst) :: environment.scopes } expression staticFuel expressionEnough
                  · simp only [ready]
                    apply controlFlow_dispatch (expressionFlows staticFuel expression) _ (fun _ => normalFlow) resultControlFlow
                    · exact previous.produce { environment with scopes := (scope, scopeInst) :: environment.scopes } channels expression staticFuel expressionEnough
                    · intro breakScope kind admitted
                      exact admitted
                    · intro carriers admitted
                      apply controlFlow_prefix
                      · exact controlFlow_normal _ (breakFrame_singleCarrier _) (neverJumps_singleCarrier _)
                      · intro carrier
                        apply controlFlow_prefix
                        · exact controlFlow_normal _ (breakFrame_carrierValue _) (neverJumps_carrierValue _)
                        · intro result
                          exact controlFlow_pure _ resultControlFlow (Flow.normal result) admitted
            | breaking value =>
              apply controlFlow_pure
              cases tail with
              | none => exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal .loop (.breakValue [])) present
              | some expression => exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal .loop (.breakValue [])) present
            | continuing =>
              apply controlFlow_pure
              cases tail with
              | none => exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal .loop .continueLoop) present
              | some expression => exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal .loop .continueLoop) present

#print axioms evaluationControl_statements_succ
#print axioms evaluationControl_block_succ

end Goose.Proofs.ConstructionDelivery
