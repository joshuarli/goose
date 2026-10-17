import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationContext
import Goose.Proofs.ConstructionDeliveryFlowSoundnessTargets
import Goose.Proofs.ConstructionDeliveryFlowSoundnessDispatch
import Goose.Proofs.ConstructionDeliveryFlowSoundnessNoJumps

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem whileFlows_nonliteral (staticFuel : Nat) (condition : Expr) (body : Block)
    (notTrue : condition ≠ .bool true) :
    statementFlows (staticFuel + 1) (.while condition body 0) =
      continueFlows (expressionFlows staticFuel condition) (loopControlFlows staticFuel body) := by
  cases condition <;> try rfl
  case bool value =>
    cases value with
    | false => rfl
    | true => exact False.elim (notTrue rfl)

private theorem whileFlows_true (staticFuel : Nat) (body : Block) :
    statementFlows (staticFuel + 1) (.while (.bool true) body 0) =
      if !(blockFlows staticFuel body).contains loopBreakFlow then
        (blockFlows staticFuel body).filter escapingControlFlow else loopControlFlows staticFuel body := by
  have literal : expressionFlows staticFuel (.bool true) = [normalFlow] := by cases staticFuel <;> rfl
  change continueFlows (expressionFlows staticFuel (.bool true)) _ = _
  rw [literal, continueFlows_normal_left]
  rfl

private theorem execWhile_true (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation) (body : Block) :
    execWhile (fuel + 2) config environment (.bool true) body = (do
      match (← loopBody (fuel + 1) config environment [] body) with
      | .normal _ | .continuing => execWhile (fuel + 1) config environment (.bool true) body
      | .breaking value => pure (.normal (value.getD .unit))) := by
  funext before
  simp only [execWhile, evalValue, expectBool, pure, bind, Bind.bind, ↓reduceIte]
  cases result : loopBody (fuel + 1) config environment [] body before with
  | ok flow middle => cases flow <;> rfl
  | stop reason middle => rfl
  | escape address carriers middle => rfl
  | jump target kind middle => rfl

theorem evaluationControl_loop_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) (staticFuel : Nat)
    (enough : blockQueryBudget body ≤ staticFuel) :
    ControlFlowAction environment.act (blockFlows staticFuel body) resultControlFlow
      (loopBody (fuel + 1) config environment pre body) := by
  simp only [loopBody]
  apply controlFlow_withBreakTarget
  · exact previous.block environment pre [] body staticFuel enough
  · intro value admitted
    exact admitted
  · intro scope kind different admitted
    exact admitted
  · intro kind
    cases kind with
    | continueLoop => exact breakFrame_pure _
    | breakValue carriers =>
      cases carriers with
      | nil => exact breakFrame_pure _
      | cons carrier rest =>
        apply breakFrame_bind
        · exact breakFrame_singleCarrier _
        · intro selected
          apply breakFrame_bind
          · exact breakFrame_carrierValue _
          · intro value
            exact breakFrame_pure _
  · intro kind admitted
    cases kind with
    | continueLoop => exact controlFlow_pure _ resultControlFlow .continuing admitted
    | breakValue carriers =>
      cases carriers with
      | nil => exact controlFlow_pure _ resultControlFlow (.breaking none) admitted
      | cons carrier rest =>
        apply controlFlow_prefix
        · exact controlFlow_normal _ (breakFrame_singleCarrier _) (neverJumps_singleCarrier _)
        · intro selected
          apply controlFlow_prefix
          · exact controlFlow_normal _ (breakFrame_carrierValue _) (neverJumps_carrierValue _)
          · intro value
            exact controlFlow_pure _ resultControlFlow (.breaking (some value)) admitted

theorem evaluationControl_loopIteration_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) (staticFuel : Nat)
    (enough : blockQueryBudget body ≤ staticFuel) :
    ControlFlowAction environment.act (loopControlFlows staticFuel body) (fun _ => normalFlow)
      (loopBody (fuel + 1) config environment pre body) := by
  refine ⟨(evaluationControl_loop_succ fuel config previous environment pre body staticFuel enough).frame, ?_⟩
  intro before bounded
  cases run : loopBody (fuel + 1) config environment pre body before with
  | ok value after => exact List.mem_cons_self
  | stop reason after => trivial
  | escape address carriers after => trivial
  | jump id kind after =>
    simp only [loopBody] at run
    rcases controlFlow_withBreakTarget_jump_outer environment.act .loop [] (blockFlows staticFuel body)
      resultControlFlow (execBlock fuel config environment pre [] body) _
      (previous.block environment pre [] body staticFuel enough) (by
        intro kind
        cases kind with
        | continueLoop => exact neverJumps_pure _
        | breakValue carriers =>
          cases carriers with
          | nil => exact neverJumps_pure _
          | cons carrier rest =>
            apply neverJumps_bind
            · exact neverJumps_singleCarrier _
            · intro selected
              apply neverJumps_bind
              · exact neverJumps_carrierValue _
              · intro value
                exact neverJumps_pure _) before bounded id kind after run with
      ⟨target, member, selection, equal, different, compatible, admitted⟩
    refine ⟨target, member, selection, compatible, equal, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨admitted, ?_⟩)⟩
    cases kind with
    | continueLoop => exact False.elim (different compatible)
    | breakValue carriers =>
      cases targetScope : target.scope with
      | block => rfl
      | loop => exact False.elim (different targetScope)

theorem evaluationControl_range_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (ty : Goose.Core.IntTy) (first last : Int) (body : Block) (staticFuel : Nat)
    (enough : blockQueryBudget body ≤ staticFuel) :
    ControlFlowAction environment.act (loopControlFlows staticFuel body) resultControlFlow
      (execRange (fuel + 1) config environment localVar ty first last body) := by
  simp only [execRange]
  split
  · apply controlFlow_dispatch (loopControlFlows staticFuel body) _ (fun _ => normalFlow) resultControlFlow
    · exact previous.loopIteration environment [(localVar, .int ty first)] body staticFuel enough
    · intro scope kind admitted
      exact admitted
    · intro flow admitted
      cases flow with
      | normal value => exact previous.rangeLoop environment localVar ty (first + 1) last body staticFuel enough
      | continuing => exact previous.rangeLoop environment localVar ty (first + 1) last body staticFuel enough
      | breaking value => exact controlFlow_pure _ resultControlFlow (.normal (value.getD .unit)) List.mem_cons_self
  · exact controlFlow_pure _ resultControlFlow (.normal .unit) List.mem_cons_self

theorem evaluationControl_each_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool)
    (body : Block) (view : RuntimeView) (current staticFuel : Nat)
    (enough : blockQueryBudget body ≤ staticFuel) :
    ControlFlowAction environment.act (loopControlFlows staticFuel body) resultControlFlow
      (execEach (fuel + 1) config environment localVar index byRef body view current) := by
  have iteration (value : Value) :
      ControlFlowAction environment.act (loopControlFlows staticFuel body) resultControlFlow (do
        match (← loopBody fuel config environment
          ((localVar, value) :: (index.toList.map fun index => (index, Value.int .i64 current))) body) with
        | .normal _ | .continuing => execEach fuel config environment localVar index byRef body view (current + 1)
        | .breaking value => pure (.normal (value.getD .unit))) := by
    apply controlFlow_dispatch (loopControlFlows staticFuel body) _ (fun _ => normalFlow) resultControlFlow
    · exact previous.loopIteration environment _ body staticFuel enough
    · intro scope kind admitted
      exact admitted
    · intro flow admitted
      cases flow with
      | normal value => exact previous.eachLoop environment localVar index byRef body view (current + 1) staticFuel enough
      | continuing => exact previous.eachLoop environment localVar index byRef body view (current + 1) staticFuel enough
      | breaking value => exact controlFlow_pure _ resultControlFlow (.normal (value.getD .unit)) List.mem_cons_self
  simp only [execEach]
  repeat' first
    | exact iteration _
    | exact controlFlow_normal _ (breakFrame_readLoc _ _ _) (neverJumps_readLoc _ _ _)
    | exact controlFlow_normal _ (breakFrame_arrayLength _) (neverJumps_arrayLength _)
    | exact controlFlow_pure _ _ _ List.mem_cons_self
    | apply controlFlow_conditional
    | apply controlFlow_prefix
    | (intro)
    | dsimp only

theorem evaluationControl_while_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (condition : Expr) (body : Block) (staticFuel : Nat)
    (enough : statementQueryBudget (.while condition body 0) ≤ staticFuel) :
    ControlFlowAction environment.act (statementFlows staticFuel (.while condition body 0)) resultControlFlow
      (execWhile (fuel + 1) config environment condition body) := by
  cases fuel with
  | zero =>
    simp only [execWhile, evalValue, timeout, bind, Bind.bind, EvalM.stop]
    exact controlFlow_stop _ _ _
  | succ fuel =>
    cases staticFuel with
    | zero => exact False.elim (Nat.not_le_of_gt (statementQueryBudget_positive (.while condition body 0)) enough)
    | succ staticFuel =>
      have budgets : expressionQueryBudget condition + blockQueryBudget body + 1 ≤ staticFuel + 1 := enough
      have conditionEnough : expressionQueryBudget condition ≤ staticFuel := by omega
      have bodyEnough : blockQueryBudget body ≤ staticFuel := by omega
      by_cases isTrue : condition = .bool true
      · subst condition
        rw [whileFlows_true, execWhile_true]
        cases breaks : (blockFlows staticFuel body).contains loopBreakFlow with
        | false =>
          simp only [Bool.not_false, ↓reduceIte]
          apply controlFlow_loopDispatch (blockFlows staticFuel body) (loopControlFlows staticFuel body)
          · exact previous.loop environment [] body staticFuel bodyEnough
          · exact previous.loopIteration environment [] body staticFuel bodyEnough
          · intro scope kind admitted
            rcases List.mem_cons.mp admitted with same | outer
            · exact False.elim ((jumpControlFlow_ne_normal scope kind) same)
            · exact outer
          · intro flow admitted
            cases flow with
            | normal value =>
              simpa only [whileFlows_true, breaks, Bool.not_false, ↓reduceIte] using
                previous.whileLoop environment (.bool true) body (staticFuel + 1) enough
            | continuing =>
              simpa only [whileFlows_true, breaks, Bool.not_false, ↓reduceIte] using
                previous.whileLoop environment (.bool true) body (staticFuel + 1) enough
            | breaking value =>
              have impossible : (blockFlows staticFuel body).contains loopBreakFlow = true := List.contains_iff_mem.mpr admitted
              exact False.elim (Bool.noConfusion (breaks.symm.trans impossible))
        | true =>
          simp only [Bool.not_true]
          apply controlFlow_dispatch (loopControlFlows staticFuel body) _ (fun _ => normalFlow) resultControlFlow
          · exact previous.loopIteration environment [] body staticFuel bodyEnough
          · intro scope kind admitted
            exact admitted
          · intro flow admitted
            cases flow with
            | normal value =>
              simpa only [whileFlows_true, breaks, Bool.not_true, ↓reduceIte] using
                previous.whileLoop environment (.bool true) body (staticFuel + 1) enough
            | continuing =>
              simpa only [whileFlows_true, breaks, Bool.not_true, ↓reduceIte] using
                previous.whileLoop environment (.bool true) body (staticFuel + 1) enough
            | breaking value => exact controlFlow_pure _ resultControlFlow (.normal (value.getD .unit)) List.mem_cons_self
      · rw [whileFlows_nonliteral staticFuel condition body isTrue]
        simp only [execWhile]
        apply controlFlow_dispatch (expressionFlows staticFuel condition) _ (fun _ => normalFlow) resultControlFlow
        · exact previous.value environment condition staticFuel conditionEnough
        · intro scope kind admitted
          exact mem_continueFlows_first _ _ _ (jumpControlFlow_ne_normal scope kind) admitted
        · intro value normalCondition
          apply controlFlow_prefix
          · exact controlFlow_normal _ (breakFrame_expectBool _) (neverJumps_expectBool _)
          · intro truth
            apply controlFlow_conditional
            · apply controlFlow_dispatch (loopControlFlows staticFuel body) _ (fun _ => normalFlow) resultControlFlow
              · exact previous.loopIteration environment [] body staticFuel bodyEnough
              · intro scope kind admitted
                exact mem_continueFlows_second _ _ _ normalCondition admitted
              · intro flow admitted
                cases flow with
                | normal value =>
                  simpa only [whileFlows_nonliteral staticFuel condition body isTrue, execWhile] using
                    previous.whileLoop environment condition body (staticFuel + 1) enough
                | continuing =>
                  simpa only [whileFlows_nonliteral staticFuel condition body isTrue, execWhile] using
                    previous.whileLoop environment condition body (staticFuel + 1) enough
                | breaking value =>
                  exact controlFlow_pure _ resultControlFlow (.normal (value.getD .unit))
                    (mem_continueFlows_second _ _ _ normalCondition List.mem_cons_self)
            · exact controlFlow_pure _ resultControlFlow (.normal .unit)
                (mem_continueFlows_second _ _ _ normalCondition List.mem_cons_self)

#print axioms evaluationControl_loop_succ
#print axioms evaluationControl_loopIteration_succ
#print axioms evaluationControl_range_succ
#print axioms evaluationControl_each_succ
#print axioms evaluationControl_while_succ

end Goose.Proofs.ConstructionDelivery
