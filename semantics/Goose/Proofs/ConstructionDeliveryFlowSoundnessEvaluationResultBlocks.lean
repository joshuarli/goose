import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationContext
import Goose.Proofs.ConstructionDeliveryFlowSoundnessDispatch
import Goose.Proofs.ConstructionDeliveryFlowSoundnessNoJumps

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem controlFlow_mapActivations (change : RuntimeActivation → RuntimeActivation)
    (allowed : List StaticFlow) (resultFlow : α → StaticFlow) (action : EvalM α)
    (body : ControlFlowAction activation allowed resultFlow action) :
    ControlFlowAction activation allowed resultFlow (do
      let state ← EvalM.get
      EvalM.set { state with activations := state.activations.map change }
      action) := by
  constructor
  · intro before bounded
    let prepared := { before with activations := before.activations.map change }
    have checked := body.frame prepared bounded
    cases result : action prepared <;> simp only [result] at checked
    all_goals change BreakStackFrame prepared _ at checked
    all_goals dsimp only [prepared] at result
    all_goals simp only [bind, Bind.bind, EvalM.get, EvalM.set, result]
    all_goals change BreakStackFrame before _
    all_goals exact ⟨checked.counter, checked.stack⟩
  · intro before bounded
    let prepared := { before with activations := before.activations.map change }
    have checked := body.outcome prepared bounded
    cases result : action prepared
    all_goals simp only [result, ControlFlowOutcome] at checked
    all_goals dsimp only [prepared] at result
    all_goals simpa only [bind, Bind.bind, EvalM.get, EvalM.set, result, ControlFlowOutcome] using checked

theorem evaluationControl_resultBlock_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (body : Block) (staticFuel : Nat)
    (enough : blockQueryBudget body ≤ staticFuel) :
    ControlFlowAction environment.act (blockFlows staticFuel body) (fun result : Flow × List Carrier => resultControlFlow result.1)
      (execResultBlock (fuel + 1) config environment channels body) := by
  simp only [execResultBlock]
  exact previous.resultBlockWith environment [] channels body staticFuel enough

theorem evaluationControl_resultBlockWith_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (block : Block)
    (staticFuel : Nat) (enough : blockQueryBudget block ≤ staticFuel) :
    ControlFlowAction environment.act (blockFlows staticFuel block) (fun result : Flow × List Carrier => resultControlFlow result.1)
      (execResultBlockWith (fuel + 1) config environment pre channels block) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (blockQueryBudget_positive block) enough)
  | succ staticFuel =>
    cases block with
    | mk scope statements tail =>
      have statementsEnough : statementsQueryBudget statements ≤ staticFuel := by
        cases tail
        case none => change statementsQueryBudget statements + 1 + 1 ≤ staticFuel + 1 at enough; omega
        case some expression => change statementsQueryBudget statements + expressionQueryBudget expression + 1 ≤ staticFuel + 1 at enough; omega
      simp only [execResultBlockWith, execResultScope]
      apply controlFlow_prefix
      · exact controlFlow_normal _ breakFrame_freshScope neverJumps_freshScope
      · intro scopeInst
        try dsimp only
        apply controlFlow_mapActivations
        apply controlFlow_withScope
        apply controlFlow_prefix
        · exact controlFlow_normal _ (breakFrame_bindAll _ _ _) (neverJumps_bindAll _ _ _)
        · intro ignored
          apply controlFlow_dispatch (statementsFlows staticFuel statements) _ resultControlFlow (fun result : Flow × List Carrier => resultControlFlow result.1)
          · exact previous.statements { environment with scopes := (scope, scopeInst) :: environment.scopes } statements staticFuel statementsEnough
          · intro breakScope kind admitted
            cases tail with
            | none => exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal breakScope kind) admitted
            | some expression => exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal breakScope kind) admitted
          · intro flow admitted
            cases flow with
            | normal value =>
              cases tail with
              | none =>
                simp only
                repeat' first
                  | exact controlFlow_stop _ _ _
                  | (apply controlFlow_pure; exact mem_continueFlows_second _ _ _ admitted (List.mem_singleton_self _))
                  | apply controlFlow_conditional
                  | split
              | some expression =>
                simp only
                have expressionEnough : expressionQueryBudget expression ≤ staticFuel := by
                  change statementsQueryBudget statements + expressionQueryBudget expression + 1 ≤ staticFuel + 1 at enough
                  omega
                apply controlFlow_mono (expressionFlows staticFuel expression)
                · intro nextFlow present
                  exact mem_continueFlows_second _ _ _ admitted present
                · apply controlFlow_map
                  exact previous.produce { environment with scopes := (scope, scopeInst) :: environment.scopes } channels expression staticFuel expressionEnough
            | breaking value =>
              apply controlFlow_pure
              cases tail with
              | none => exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal .loop (.breakValue [])) admitted
              | some expression => exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal .loop (.breakValue [])) admitted
            | continuing =>
              apply controlFlow_pure
              cases tail with
              | none => exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal .loop .continueLoop) admitted
              | some expression => exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal .loop .continueLoop) admitted

#print axioms evaluationControl_resultBlock_succ
#print axioms evaluationControl_resultBlockWith_succ

end Goose.Proofs.ConstructionDelivery
