import Goose.Proofs.ExitExecution

namespace Goose.Proofs.ConstructionActivationCounter
open Goose.Construct Goose.Proofs.ExitExecution

def PreservesActivationCounter (action : EvalM α) : Prop :=
  ∀ state, state.nextAct ≤ (Goose.Proofs.Exit.stepState (action state)).nextAct

theorem counter_pure (value : α) : PreservesActivationCounter (pure value) := by
  intro state
  exact Nat.le_refl _

theorem counter_stop (reason : Goose.Core.Stop) : PreservesActivationCounter (EvalM.stop (α := α) reason) := by
  intro state
  exact Nat.le_refl _

theorem counter_bind (action : EvalM α) (next : α → EvalM β)
    (first : PreservesActivationCounter action) (remaining : ∀ value, PreservesActivationCounter (next value)) :
    PreservesActivationCounter (action >>= next) := by
  intro state
  have prior := first state
  cases result : action state with
  | ok value middle =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    have after := remaining value middle
    simp only [bind, result]
    exact Nat.le_trans prior after
  | stop reason after | escape address carriers after | jump target kind after =>
    simpa only [bind, result, Goose.Proofs.Exit.stepState] using prior

theorem counter_stateQuery (action : EvalM α) (query : StateQuery action) : PreservesActivationCounter action := by
  intro state
  rw [query state]
  exact Nat.le_refl _

theorem counter_freshAct : PreservesActivationCounter freshAct := by
  intro state
  simp [freshAct, EvalM.get, EvalM.set, bind, pure, Goose.Proofs.Exit.stepState]

theorem counter_freshScope : PreservesActivationCounter freshScope := by
  intro state
  simp [freshScope, EvalM.get, EvalM.set, bind, pure, Goose.Proofs.Exit.stepState]

theorem counter_lift (origin : Goose.Core.OriginId) (action : ConstructionM α) :
    PreservesActivationCounter (liftConstruction origin action) := by
  intro state
  cases result : action state.construction <;> simp [liftConstruction, result, Goose.Proofs.Exit.stepState]

theorem counter_withScope (environment : RuntimeActivation) (scope scopeInst : Nat) (action : EvalM α)
    (preserved : PreservesActivationCounter action) : PreservesActivationCounter (withScope environment scope scopeInst action) := by
  intro state
  have after := preserved state
  cases result : action state with
  | ok value final =>
    simpa [withScope, result, releaseScope, releaseScopeState, EvalM.get, EvalM.set, bind,
      Goose.Proofs.Exit.stepState] using after
  | stop reason final => simpa [withScope, result, Goose.Proofs.Exit.stepState] using after
  | escape target carriers final =>
    simpa [withScope, result, releaseScope, releaseScopeState, EvalM.get, EvalM.set, bind,
      Goose.Proofs.Exit.stepState] using after
  | jump target kind final =>
    simpa [withScope, result, releaseScope, releaseScopeState, EvalM.get, EvalM.set, bind,
      Goose.Proofs.Exit.stepState] using after

#print axioms counter_withScope
theorem counter_finishActivation (layout : LayoutEnv) (activation : RuntimeActivation) (types : List Ty)
    (origin : Goose.Core.OriginId) (action : EvalM (List Carrier))
    (preserved : PreservesActivationCounter action)
    (finishPreserved : ∀ carriers, PreservesActivationCounter (finishChannels layout activation.channels types carriers origin)) :
    PreservesActivationCounter (finishActivation layout activation types origin action) := by
  intro state
  have prior := preserved state
  cases result : action state with
  | ok carriers final =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    let trimmed : ExecutionState := { final with activations := final.activations.filter (fun current => current.act != activation.act) }
    have after := finishPreserved carriers trimmed
    cases finished : finishChannels layout activation.channels types carriers origin trimmed <;>
      simp only [finished, Goose.Proofs.Exit.stepState] at after <;>
      simpa [finishActivation, result, trimmed, finished, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after
  | stop reason final => simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using prior
  | jump target kind final => simpa [finishActivation, result, Goose.Proofs.Exit.stepState] using prior
  | escape target carriers final =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    by_cases caught : target.activation = activation.act
    · let trimmed : ExecutionState := { final with activations := final.activations.filter (fun current => current.act != activation.act) }
      have after := finishPreserved carriers trimmed
      cases finished : finishChannels layout activation.channels types carriers origin trimmed <;>
        simp only [finished, Goose.Proofs.Exit.stepState] at after <;>
        simpa [finishActivation, result, caught, trimmed, finished, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after
    · simpa [finishActivation, result, caught, Goose.Proofs.Exit.stepState] using prior

#print axioms counter_finishActivation
theorem counter_protectDestination (origin : Goose.Core.OriginId) (destination : Goose.Core.DestinationId)
    (action : EvalM α) (preserved : PreservesActivationCounter action)
    (cleanup : ∀ carriers, PreservesActivationCounter (cleanupReceivingDestination origin destination carriers)) :
    PreservesActivationCounter (protectDestination origin destination action) := by
  intro state
  have prior := preserved state
  cases result : action state with
  | ok value final => simpa [protectDestination, result, Goose.Proofs.Exit.stepState] using prior
  | stop reason final => simpa [protectDestination, result, Goose.Proofs.Exit.stepState] using prior
  | escape target carriers final =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    have after := cleanup carriers final
    cases cleaned : cleanupReceivingDestination origin destination carriers final <;>
      simp only [cleaned, Goose.Proofs.Exit.stepState] at after <;>
      simpa [protectDestination, result, cleaned, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after
  | jump target kind final =>
    simp only [result, Goose.Proofs.Exit.stepState] at prior
    cases kind with
    | breakValue carriers =>
      have after := cleanup carriers final
      cases cleaned : cleanupReceivingDestination origin destination carriers final <;>
        simp only [cleaned, Goose.Proofs.Exit.stepState] at after <;>
        simpa [protectDestination, result, cleaned, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after
    | continueLoop =>
      have after := cleanup [] final
      cases cleaned : cleanupReceivingDestination origin destination [] final <;>
        simp only [cleaned, Goose.Proofs.Exit.stepState] at after <;>
        simpa [protectDestination, result, cleaned, Goose.Proofs.Exit.stepState] using Nat.le_trans prior after

#print axioms counter_protectDestination
structure EvaluationPreservesActivationCounter (fuel : Nat) (config : EvalConfig) : Prop where
  value : ∀ environment expression, PreservesActivationCounter (evalValue fuel config environment expression)
  bound : ∀ environment count defaultValue operand, PreservesActivationCounter (evalBound fuel config environment count defaultValue operand)
  place : ∀ environment operand, PreservesActivationCounter (evalPlace fuel config environment operand)
  view : ∀ environment operand, PreservesActivationCounter (evalView fuel config environment operand)
  produce : ∀ environment channels operand, PreservesActivationCounter (evalProduce fuel config environment channels operand)
  operands : ∀ environment channels expressions, PreservesActivationCounter (evalOperands fuel config environment channels expressions)
  build : ∀ environment destination expression, PreservesActivationCounter (buildExpr fuel config environment destination expression)
  element : ∀ environment destination element expression, PreservesActivationCounter (buildElement fuel config environment destination element expression)
  arguments : ∀ environment vars params args, PreservesActivationCounter (evalArguments fuel config environment vars params args)
  call : ∀ environment context args channels origin, PreservesActivationCounter (invokeCall fuel config environment context args channels origin)
  activation : ∀ environment pre body origin, PreservesActivationCounter (enterActivation fuel config environment pre body origin)
  activationBody : ∀ environment pre body, PreservesActivationCounter (execActivationBody fuel config environment pre body)
  resultBlock : ∀ environment channels body, PreservesActivationCounter (execResultBlock fuel config environment channels body)
  resultBlockWith : ∀ environment pre channels body, PreservesActivationCounter (execResultBlockWith fuel config environment pre channels body)
  block : ∀ environment pre channels body, PreservesActivationCounter (execBlock fuel config environment pre channels body)
  statements : ∀ environment statements, PreservesActivationCounter (execStmts fuel config environment statements)
  statement : ∀ environment statement, PreservesActivationCounter (execStmt fuel config environment statement)
  printArgument : ∀ environment argument, PreservesActivationCounter (evalPrintArg fuel config environment argument)
  whileLoop : ∀ environment condition body, PreservesActivationCounter (execWhile fuel config environment condition body)
  rangeLoop : ∀ environment var ty first last body, PreservesActivationCounter (execRange fuel config environment var ty first last body)
  eachLoop : ∀ environment var index byRef body view current, PreservesActivationCounter (execEach fuel config environment var index byRef body view current)
  loop : ∀ environment pre body, PreservesActivationCounter (loopBody fuel config environment pre body)
  push : ∀ environment owner expression origin, PreservesActivationCounter (pushValue fuel config environment owner expression origin)


theorem evaluationCounter_zero (config : EvalConfig) : EvaluationPreservesActivationCounter 0 config := by
  constructor <;> intros <;>
    simp only [evalValue, evalBound, evalPlace, evalView, evalProduce, evalOperands, buildExpr, buildElement,
      evalArguments, invokeCall, enterActivation, execActivationBody, execResultBlock, execResultBlockWith,
      execBlock, execStmts, execStmt, evalPrintArg, execWhile, execRange, execEach, loopBody, pushValue,
      timeout, counter_stop]

theorem evalValue_not_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation) (expression : Expr) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.not expression)) := by
  simp only [evalValue]
  apply counter_bind
  · exact previous.value environment expression
  · intro value
    apply counter_bind
    · exact counter_stateQuery _ (stateQuery_expectBool value)
    · intro result
      exact counter_pure _

theorem evalValue_cmp_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.CmpOp) (first second : Expr) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.cmp operation first second)) := by
  simp only [evalValue]
  apply counter_bind
  · exact previous.value environment first
  · intro firstValue
    apply counter_bind
    · exact previous.value environment second
    · intro secondValue
      apply counter_bind
      · exact counter_stateQuery _ (stateQuery_comparable firstValue secondValue)
      · intro result
        exact counter_pure _

#print axioms evalValue_not_counter
#print axioms evalValue_cmp_counter
theorem counter_fault (reason : Goose.Core.FaultKind) : PreservesActivationCounter (fault (α := α) reason) :=
  counter_stop _

theorem counter_abortAt (reason : Goose.Core.AbortKind) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (abortAt (α := α) reason origin) := counter_stop _

theorem evalValue_un_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.UnOp) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.un operation expression origin)) := by
  simp only [evalValue]
  apply counter_bind
  · exact previous.value environment expression
  · intro value
    apply counter_bind
    · exact counter_stateQuery _ (stateQuery_expectInt value)
    · intro result
      cases result with
      | mk ty number =>
        cases Goose.Core.evalUn config.profile operation ty number with
        | ok value => exact counter_pure _
        | error reason => exact counter_abortAt (Goose.Core.AbortKind.ofNum reason) origin

theorem evalValue_bin_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (operation : Goose.Core.BinOp) (first second : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.bin operation first second origin)) := by
  simp only [evalValue]
  apply counter_bind
  · exact previous.value environment first
  · intro firstValue
    apply counter_bind
    · exact counter_stateQuery _ (stateQuery_expectInt firstValue)
    · intro firstResult
      cases firstResult with
      | mk ty firstNumber =>
        apply counter_bind
        · exact previous.value environment second
        · intro secondValue
          apply counter_bind
          · exact counter_stateQuery _ (stateQuery_expectInt secondValue)
          · intro secondResult
            cases secondResult with
            | mk otherTy secondNumber =>
              apply counter_bind
              · exact counter_stateQuery _ (stateQuery_sameIntType ty otherTy)
              · intro ignored
                cases Goose.Core.evalBin config.profile operation ty firstNumber secondNumber with
                | ok value => exact counter_pure _
                | error reason => exact counter_abortAt (Goose.Core.AbortKind.ofNum reason) origin

theorem evalValue_conv_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (kind : Goose.Core.ConvKind) (target : Ty) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.conv kind target expression origin)) := by
  simp only [evalValue]
  apply counter_bind
  · exact previous.value environment expression
  · intro value
    apply counter_bind
    · exact counter_stateQuery _ (stateQuery_expectInt value)
    · intro result
      cases result with
      | mk source number =>
        cases target with
        | int target =>
          simp only
          cases Goose.Core.evalConv config.profile kind source target number with
          | ok value => exact counter_pure _
          | error reason => exact counter_abortAt (Goose.Core.AbortKind.ofNum reason) origin
        | _ => exact counter_fault _

#print axioms evalValue_conv_counter
theorem evalValue_and_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation) (first second : Expr) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.and first second)) := by
  simp only [evalValue]
  apply counter_bind
  · exact previous.value environment first
  · intro value
    apply counter_bind
    · exact counter_stateQuery _ (stateQuery_expectBool value)
    · intro condition
      cases condition with
      | false => exact counter_pure _
      | true =>
        apply counter_bind
        · exact previous.value environment second
        · intro value
          apply counter_bind
          · exact counter_stateQuery _ (stateQuery_expectBool value)
          · intro value
            exact counter_pure _

theorem evalValue_or_counter (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation) (first second : Expr) :
    PreservesActivationCounter (evalValue (fuel + 1) config environment (.or first second)) := by
  simp only [evalValue]
  apply counter_bind
  · exact previous.value environment first
  · intro value
    apply counter_bind
    · exact counter_stateQuery _ (stateQuery_expectBool value)
    · intro condition
      cases condition with
      | true => exact counter_pure _
      | false =>
        apply counter_bind
        · exact previous.value environment second
        · intro value
          apply counter_bind
          · exact counter_stateQuery _ (stateQuery_expectBool value)
          · intro value
            exact counter_pure _

#print axioms evalValue_bin_counter
#print axioms evalValue_and_counter
theorem freshActs_distinct_across (action : EvalM α) (preserved : PreservesActivationCounter action)
    (before afterFirst afterAction afterSecond : ExecutionState) (first second : Goose.Core.ActId) (value : α)
    (firstStep : freshAct before = .ok first afterFirst)
    (actionStep : action afterFirst = .ok value afterAction)
    (secondStep : freshAct afterAction = .ok second afterSecond) : first < second := by
  have firstExact : freshAct before = .ok before.nextAct { before with nextAct := before.nextAct + 1 } := by rfl
  have secondExact : freshAct afterAction = .ok afterAction.nextAct { afterAction with nextAct := afterAction.nextAct + 1 } := by rfl
  have firstId : first = before.nextAct := (ExecutionStep.ok.inj (firstStep.symm.trans firstExact)).1
  have firstState : afterFirst = { before with nextAct := before.nextAct + 1 } :=
    (ExecutionStep.ok.inj (firstStep.symm.trans firstExact)).2
  have secondId : second = afterAction.nextAct := (ExecutionStep.ok.inj (secondStep.symm.trans secondExact)).1
  have monotone := preserved afterFirst
  simp only [actionStep, Goose.Proofs.Exit.stepState] at monotone
  rw [firstId, secondId]
  rw [firstState] at monotone
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) monotone

private def allocationWitness : EvalM (Goose.Core.ActId × Goose.Core.ActId) := do
  let first ← freshAct
  emitStdout ⟨#[65]⟩
  let second ← freshAct
  pure (first, second)

private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem allocationWitness_execution :
    ∃ state, allocationWitness .initial = .ok (0, 1) state ∧
      state.construction.stdout.data.toList = [65] := by
  refine ⟨witnessState (allocationWitness .initial), ?_, ?_⟩ <;>
    unfold allocationWitness witnessState <;> cbv

#print axioms allocationWitness_execution
#print axioms freshActs_distinct_across
#print axioms evaluationCounter_zero
#print axioms counter_bind
#print axioms counter_freshAct
#print axioms counter_lift
end Goose.Proofs.ConstructionActivationCounter
