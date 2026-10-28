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
