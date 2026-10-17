import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationStatementsReturns

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

theorem controlFlow_breakValue (allowed : List StaticFlow)
    (action : BreakTarget → EvalM (List Carrier))
    (body : ∀ target, ControlFlowAction activation allowed (fun _ => normalFlow) (action target)) :
    ControlFlowAction activation (continueFlows allowed [valueBreakFlow]) resultControlFlow (do
      let target ← currentBreak activation (some .block)
      let carriers ← action target
      jump target.id (.breakValue carriers)) := by
  refine ⟨breakFrame_bind _ _ (breakFrame_currentBreak _ _) (fun target =>
    breakFrame_bind _ _ (body target).frame (fun carriers => breakFrame_jump _ _)), ?_⟩
  intro before bounded
  cases selected : before.breaks.find? (fun target => target.act == activation && some BreakScope.block == some target.scope) with
  | none =>
    simp only [bind, Bind.bind, currentBreak, EvalM.get, selected, Option.isNone_some, Bool.false_or, ControlFlowOutcome]
    trivial
  | some target =>
    have selectedScope := List.find?_some selected
    have scopeEqual : target.scope = .block := by
      simp only [Bool.and_eq_true, beq_iff_eq, Option.some.injEq] at selectedScope
      exact selectedScope.2.symm
    have reached := (body target).outcome before bounded
    cases evaluated : action target before with
    | ok carriers after =>
      simp only [evaluated, ControlFlowOutcome] at reached
      simp only [pure, bind, Bind.bind, currentBreak, EvalM.get, Option.isNone_some, Bool.false_or, selected, evaluated, jump, ControlFlowOutcome]
      refine ⟨target, List.mem_of_find?_eq_some selected, by simpa only [scopeEqual] using selected,
        True.intro, rfl, ?_⟩
      simp only [scopeEqual, jumpControlFlow]
      exact mem_continueFlows_second _ _ _ reached (List.mem_singleton_self _)
    | stop reason after =>
      simp only [pure, bind, Bind.bind, currentBreak, EvalM.get, Option.isNone_some, Bool.false_or, selected, evaluated, ControlFlowOutcome]
    | escape address carriers after =>
      simp only [pure, bind, Bind.bind, currentBreak, EvalM.get, Option.isNone_some, Bool.false_or, selected, evaluated, ControlFlowOutcome]
    | jump id kind after =>
      simp only [evaluated, ControlFlowOutcome] at reached
      rcases reached with ⟨outer, member, nearest, compatible, equal, permitted⟩
      simp only [pure, bind, Bind.bind, currentBreak, EvalM.get, Option.isNone_some, Bool.false_or, selected, evaluated, ControlFlowOutcome]
      exact ⟨outer, member, nearest, compatible, equal,
        mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal _ _) permitted⟩

theorem evaluationControl_statement_breakValue_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (expression : Expr) (origin : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : statementQueryBudget (.breakValue expression origin) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.breakValue expression origin)) resultControlFlow
      (execStmt (fuel + 1) config environment (.breakValue expression origin)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive _) enough)
  | succ staticFuel =>
    have budgets : expressionQueryBudget expression + 1 ≤ staticFuel + 1 := enough
    change ControlFlowAction environment.act (continueFlows (expressionFlows staticFuel expression) [valueBreakFlow]) resultControlFlow _
    simp only [execStmt]
    apply controlFlow_breakValue
    intro target
    apply controlFlow_withExitChannels
    intro channels
    exact previous.produce environment channels expression staticFuel (by omega)

#print axioms controlFlow_breakValue
#print axioms evaluationControl_statement_breakValue_succ

end Goose.Proofs.ConstructionDelivery
