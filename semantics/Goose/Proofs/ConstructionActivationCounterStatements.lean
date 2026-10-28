import Goose.Proofs.ConstructionActivationCounterExit

namespace Goose.Proofs.ConstructionActivationCounterStatements
open Goose.Construct Goose.Proofs.ConstructionActivationCounter Goose.Proofs.ConstructionActivationCounterOwner
open Goose.Proofs.ConstructionActivationCounterExit Goose.Proofs.ExitExecution

theorem counter_returned (activation : Goose.Core.ActId) (carriers : List Carrier) :
    PreservesActivationCounter (returned (α := α) activation carriers) := by
  intro state
  exact Nat.le_refl _

theorem counter_escaped (address : ExitAddress) (carriers : List Carrier) :
    PreservesActivationCounter (escaped (α := α) address carriers) := by
  intro state
  exact Nat.le_refl _

theorem counter_jump (target : Nat) (kind : JumpKind) :
    PreservesActivationCounter (jump (α := α) target kind) := by
  intro state
  exact Nat.le_refl _

theorem counter_emitStdout (bytes : ByteArray) : PreservesActivationCounter (emitStdout bytes) :=
  counter_lift _ _

theorem counter_landCarrier (origin : Goose.Core.OriginId) (carrier : Carrier) :
    PreservesActivationCounter (landCarrier origin carrier) := by
  unfold landCarrier
  cases carrier with
  | register value => exact counter_pure _
  | pendingNamed token => exact counter_fault _
  | completed id =>
    apply counter_bind
    · exact counter_stateQuery _ (stateQuery_getDestination id)
    · intro destination
      cases destination.use with
      | replacement old => exact counter_lift _ _
      | receiver | child parent => exact counter_pure _

theorem counter_landCarriers (origin : Goose.Core.OriginId) (carriers : List Carrier) :
    PreservesActivationCounter (landCarriers origin carriers) := by
  unfold landCarriers
  apply counter_bind
  · apply counter_listForIn
    intro carrier ignored
    apply counter_bind
    · exact counter_landCarrier origin carrier
    · intro ignored; exact counter_pure _
  · intro ignored; exact counter_pure _

local macro "counter_stmt" previous:ident : tactic => `(tactic|
  repeat' first
    | with_reducible assumption
    | counter_conditional_step
    | with_reducible exact counter_pure _
    | with_reducible exact counter_stop _
    | with_reducible exact counter_fault _
    | with_reducible exact counter_abortAt _ _
    | with_reducible exact counter_get
    | with_reducible exact counter_lift _ _
    | with_reducible exact counter_freshScope
    | with_reducible exact counter_bindRoot _ _
    | with_reducible exact counter_bindStaticRoot _ _
    | with_reducible exact counter_setObjectOrdinal _ _
    | with_reducible exact counter_writeLoc _ _ _ _
    | with_reducible exact counter_copyValue _ _ _ _ _ _
    | with_reducible exact counter_receivingDestination _
    | with_reducible exact counter_completedReceivingDestination _
    | with_reducible exact counter_receivingAction _ _ _
    | with_reducible exact counter_newDestination _ _ _ _ _ _ _
    | with_reducible exact counter_materializedDestination _ _ _ _ _ _ _
    | with_reducible exact counter_publishCarriers _ _
    | with_reducible exact counter_ownerDestination _ _ _ _ _
    | with_reducible exact counter_publishOwner _ _ _ _ _ _
    | with_reducible exact counter_openElementReceiving _ _ _ _ _ _ _
    | with_reducible exact counter_publishElementReceiving _ _ _ _ _ _
    | with_reducible exact counter_truncateOwner _ _ _ _ _
    | with_reducible exact counter_appendFixedValues _ _ _ _ _
    | with_reducible exact counter_appendRun _ _ _ _ _
    | with_reducible exact counter_landCarriersInto _ _ _
    | with_reducible exact counter_landCarriers _ _
    | with_reducible exact counter_returned _ _
    | with_reducible exact counter_escaped _ _
    | with_reducible exact counter_jump _ _
    | with_reducible exact counter_emitStdout _
    | with_reducible exact counter_stateQuery _ (stateQuery_rootOf _ _)
    | with_reducible exact counter_stateQuery _ (stateQuery_readLoc _ _ _)
    | with_reducible exact counter_stateQuery _ (stateQuery_sampledStored _)
    | with_reducible exact counter_stateQuery _ (stateQuery_arrayLength _)
    | with_reducible exact counter_stateQuery _ (stateQuery_getDestination _)
    | with_reducible exact counter_stateQuery _ (stateQuery_storedDestination _)
    | with_reducible exact counter_stateQuery _ (stateQuery_carrierValue _)
    | with_reducible exact counter_stateQuery _ (stateQuery_singleCarrier _)
    | with_reducible exact counter_stateQuery _ (stateQuery_expectInt _)
    | with_reducible exact counter_stateQuery _ (stateQuery_expectBool _)
    | with_reducible exact counter_stateQuery _ (stateQuery_sameIntType _ _)
    | with_reducible exact counter_stateQuery _ (stateQuery_liftExcept _)
    | with_reducible exact counter_stateQuery _ (stateQuery_enclosingActivation _)
    | with_reducible exact counter_stateQuery _ (stateQuery_targetActivation _ _)
    | with_reducible exact counter_stateQuery _ (stateQuery_currentBreak _ _)
    | with_reducible exact ($previous).value _ _
    | with_reducible exact ($previous).bound _ _ _ _
    | with_reducible exact ($previous).place _ _
    | with_reducible exact ($previous).view _ _
    | with_reducible exact ($previous).produce _ _ _
    | with_reducible exact ($previous).operands _ _ _
    | with_reducible exact ($previous).build _ _ _
    | with_reducible exact ($previous).element _ _ _ _
    | with_reducible exact ($previous).block _ _ _ _
    | with_reducible exact ($previous).statements _ _
    | with_reducible exact ($previous).printArgument _ _
    | with_reducible exact ($previous).whileLoop _ _ _
    | with_reducible exact ($previous).rangeLoop _ _ _ _ _ _
    | with_reducible exact ($previous).eachLoop _ _ _ _ _ _ _
    | with_reducible exact ($previous).loop _ _ _
    | with_reducible exact ($previous).push _ _ _ _
    | with_reducible apply counter_withExitChannels
    | with_reducible apply counter_withOwnerExtension
    | with_reducible apply counter_withBreakTarget
    | with_reducible apply counter_protectDestination
    | with_reducible apply counter_materializeProducer
    | with_reducible apply counter_constructLocal
    | with_reducible apply counter_listForIn
    | with_reducible apply counter_arrayForIn
    | with_reducible apply counter_rangeForIn
    | with_reducible apply counter_listMapM
    | with_reducible apply counter_bind
    | with_reducible split
    | with_reducible rfl
    | with_reducible intro)

private theorem counterLetPure_bind (value : α) (next : α → EvalM β) :
    ((pure value : EvalM α) >>= next) = next value := rfl

local elab "counter_let_step" previous:ident environment:ident expression:ident : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  if target.isForall then
    Lean.Elab.Tactic.evalTactic (← `(tactic| intro))
    return
  let args := target.getAppArgs
  let some action := args[args.size - 1]? | throwError "expected action"
  if action.isLet then
    Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only))
    return
  let name := action.getAppFn.constName?
  if name == some ``Bind.bind then
    let args := action.getAppArgs
    let some head := args[args.size - 2]? | throwError "expected head"
    let headName := head.getAppFn.constName?
    if headName == some ``Pure.pure then
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [counterLetPure_bind]))
    else if headName == some ``fault || headName == some ``EvalM.stop then
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact counter_stop _))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply counter_bind))
  else if name == some ``ite then
    Lean.Elab.Tactic.evalTactic (← `(tactic| counter_conditional_step))
  else if name == some ``evalValue then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($previous).value $environment $expression))
  else if name == some ``buildExpr then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($previous).build $environment _ $expression))
  else if name == some ``materializeProducer then
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply counter_materializeProducer; exact ($previous).value $environment $expression))
  else if name == some ``Pure.pure then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact counter_pure _))
  else if name == some ``fault || name == some ``EvalM.stop then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact counter_stop _))
  else if name == some ``EvalM.get || (name.map (·.getPrefix) == some `Goose.Construct) then
    let some (.str _ suffix) := name | throwError "expected primitive name"
    let suffix := if suffix == "liftConstruction" then "lift" else suffix
    let freshName := `Goose.Proofs.ConstructionActivationCounter ++ .str .anonymous ("counter_" ++ suffix)
    if (← Lean.getEnv).contains freshName then
      let fresh := Lean.mkIdent freshName
      Lean.Elab.Tactic.evalTactic (← `(tactic| apply $fresh))
    else
      let query := Lean.mkIdent (`Goose.Proofs.ExitExecution ++ .str .anonymous ("stateQuery_" ++ suffix))
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact counter_stateQuery _ (by apply $query)))
  else
    Lean.Elab.Tactic.evalTactic (← `(tactic| split))

set_option maxHeartbeats 2000000 in
theorem execStmt_letS_counter_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesActivationCounter fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationCounter (execStmt (fuel + 1) config environment (.letS localVar expression origin)) := by
  simp only [execStmt]
  repeat' first
    | contradiction
    | counter_let_step previous environment expression

#print axioms execStmt_letS_counter_succ
end Goose.Proofs.ConstructionActivationCounterStatements
