import Goose.Construct.Eval
import Goose.Proofs.ConstructionDeliveryFlowSoundnessRuntimeFramesCopy

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem breakFrame_conditional (condition : Prop) [Decidable condition]
    (yes no : EvalM α) (left : BreakFrameAction yes) (right : BreakFrameAction no) :
    BreakFrameAction (if condition then yes else no) := by
  split <;> assumption

elab "evaluation_frame_conditional" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``BreakFrameAction do throwError "expected break frame"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.getAppFn.isConstOf ``ite do throwError "expected conditional action"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply breakFrame_conditional))

elab "evaluation_frame_intro" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.isForall do throwError "expected callback"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro))

elab "evaluation_frame_zeta" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``BreakFrameAction do throwError "expected break frame"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.isLet do throwError "expected local action binding"
  Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only))

macro "evaluation_frame_basic" : tactic => `(tactic|
  repeat' first
    | assumption
    | exact breakFrame_pure _
    | exact breakFrame_stop _
    | exact breakFrame_get
    | exact breakFrame_freshScope
    | exact breakFrame_freshAct
    | exact breakFrame_getDestination _
    | exact breakFrame_getStorage _
    | exact breakFrame_receivingDestination _
    | exact breakFrame_completedDestination _
    | exact breakFrame_completedReceivingDestination _
    | exact breakFrame_rootOf _ _
    | exact breakFrame_currentBreak _ _
    | exact breakFrame_sampledStored _
    | exact breakFrame_arrayLength _
    | exact breakFrame_liftExcept _
    | exact breakFrame_liftLayout _
    | (with_reducible apply breakFrame_liftConstruction)
    | (with_reducible apply breakFrame_bind)
    | (with_reducible apply breakFrame_listForIn)
    | (with_reducible apply breakFrame_listMapM)
    | evaluation_frame_conditional
    | evaluation_frame_zeta
    | evaluation_frame_intro
    | split)

theorem breakFrame_returned (activation : Goose.Core.ActId) (carriers : List Carrier) :
    BreakFrameAction (returned (α := α) activation carriers) := by
  intro state _
  exact BreakStackFrame.refl state

theorem breakFrame_escaped (address : ExitAddress) (carriers : List Carrier) :
    BreakFrameAction (escaped (α := α) address carriers) := by
  intro state _
  exact BreakStackFrame.refl state

theorem breakFrame_fault_bind (kind : Goose.Core.FaultKind) (next : α → EvalM β) :
    BreakFrameAction (fault kind >>= next) := by
  intro state _
  exact BreakStackFrame.refl state

theorem breakFrame_timeout_bind (next : α → EvalM β) :
    BreakFrameAction (timeout >>= next) := by
  intro state _
  exact BreakStackFrame.refl state

theorem breakFrame_abortAt_bind (kind : Goose.Core.AbortKind) (origin : Goose.Core.OriginId)
    (next : α → EvalM β) : BreakFrameAction (abortAt kind origin >>= next) := by
  intro state _
  exact BreakStackFrame.refl state

theorem breakFrame_mapActivations (change : RuntimeActivation → RuntimeActivation)
    (action : EvalM α) (body : BreakFrameAction action) :
    BreakFrameAction (do
      let state ← EvalM.get
      EvalM.set { state with activations := state.activations.map change }
      action) := by
  intro state bounded
  let changed := { state with activations := state.activations.map change }
  have checked := body changed bounded
  change (match action changed with
    | .ok _ after | .stop _ after | .escape _ _ after | .jump _ _ after => BreakStackFrame state after)
  cases result : action changed <;>
    rw [result] at checked <;>
    change BreakStackFrame state _ <;>
    exact ⟨checked.counter, checked.stack⟩

theorem breakFrame_allocateActivation (activation : RuntimeActivation)
    (action : EvalM α) (body : BreakFrameAction action) :
    BreakFrameAction (do
      let state ← EvalM.get
      EvalM.set { state with activations := activation :: state.activations }
      action) := by
  intro state bounded
  let changed := { state with activations := activation :: state.activations }
  have checked := body changed bounded
  change (match action changed with
    | .ok _ after | .stop _ after | .escape _ _ after | .jump _ _ after => BreakStackFrame state after)
  cases result : action changed <;>
    rw [result] at checked <;>
    change BreakStackFrame state _ <;>
    exact ⟨checked.counter, checked.stack⟩

theorem breakFrame_getImplementation (config : EvalConfig) (context : Goose.Core.ContextId) :
    BreakFrameAction (getImplementation config context) := by
  unfold getImplementation
  evaluation_frame_basic

theorem breakFrame_enclosingActivation (environment : RuntimeActivation) :
    BreakFrameAction (enclosingActivation environment) := by
  unfold enclosingActivation
  evaluation_frame_basic

theorem breakFrame_targetActivation (config : EvalConfig) (target : Nat) :
    BreakFrameAction (targetActivation config target) := by
  unfold targetActivation
  evaluation_frame_basic

theorem breakFrame_materializeProducer (fuel : Nat) (declarations : DeclarationEnv)
    (expression : Expr) (evaluate : EvalM Value) (body : BreakFrameAction evaluate) :
    BreakFrameAction (materializeProducer fuel declarations expression evaluate) := by
  unfold materializeProducer
  evaluation_frame_basic

theorem breakFrame_exitSource (source : RuntimeActivation) (incoming : Goose.Core.DestinationId)
    (operand : Expr) : BreakFrameAction (exitSource source incoming operand) := by
  unfold exitSource
  evaluation_frame_basic

theorem breakFrame_selectCompletionChannel (source : RuntimeActivation) (operand : Expr)
    (channel : Channel) : BreakFrameAction (selectCompletionChannel source operand channel) := by
  cases channel <;> unfold selectCompletionChannel <;> evaluation_frame_basic
  exact breakFrame_exitSource _ _ _

theorem breakFrame_exitChannels (source activation : RuntimeActivation) (operands : List Expr)
    (origin : Goose.Core.OriginId) : BreakFrameAction (exitChannels source activation operands origin) := by
  unfold exitChannels
  evaluation_frame_basic
  all_goals exact breakFrame_exitSource _ _ _

theorem breakFrame_materializeOwnedCarriers (origin : Goose.Core.OriginId)
    (tokens : List ExitReservationId) (carriers : List Carrier) :
    BreakFrameAction (materializeOwnedCarriers origin tokens carriers) := by
  unfold materializeOwnedCarriers
  evaluation_frame_basic

private theorem breakFrame_cleanupResult (cleanup : EvalM Unit) (resume : ExecutionState → ExecutionStep α)
    (unchanged : ∀ state, match resume state with
      | .ok _ after | .stop _ after | .escape _ _ after | .jump _ _ after => after = state)
    (preserved : BreakFrameAction cleanup) (before middle : ExecutionState)
    (bounded : BreakTargetsBelowCounter before) (frame : BreakStackFrame before middle) :
    (match (match cleanup middle with
      | .ok () after => resume after
      | .stop reason after => .stop reason after
      | .escape target carriers after => .escape target carriers after
      | .jump target kind after => .jump target kind after) with
    | .ok _ after | .stop _ after | .escape _ _ after | .jump _ _ after => BreakStackFrame before after) := by
  have checked := preserved middle (frame.bounded bounded)
  cases result : cleanup middle with
  | ok value final =>
    cases value
    rw [result] at checked
    have same := unchanged final
    cases resumed : resume final <;>
      rw [resumed] at same <;>
      simp only [result, resumed] <;>
      subst_vars <;> exact frame.trans checked
  | stop reason final | escape target carriers final | jump target kind final =>
    rw [result] at checked
    simp only [result]
    exact frame.trans checked

theorem breakFrame_withExitChannels (source activation : RuntimeActivation)
    (operands : List Expr) (origin : Goose.Core.OriginId) (action : List Channel → EvalM (List Carrier))
    (body : ∀ channels, BreakFrameAction (action channels)) :
    BreakFrameAction (withExitChannels source activation operands origin action) := by
  intro state bounded
  have preparedFrame := breakFrame_exitChannels source activation operands origin state bounded
  cases prepared : exitChannels source activation operands origin state with
  | stop reason after | escape target carriers after | jump target kind after =>
    rw [prepared] at preparedFrame
    change BreakStackFrame state after at preparedFrame
    simp only [withExitChannels, prepared]
    change BreakStackFrame state after
    exact preparedFrame
  | ok channels after =>
    rw [prepared] at preparedFrame
    let tokens := (List.range (after.construction.exitReservations.size - state.construction.exitReservations.size)).map
      (state.construction.exitReservations.size + ·)
    let evaluatedAction := do materializeOwnedCarriers origin tokens (← action channels)
    have actionFrame : BreakFrameAction evaluatedAction :=
      breakFrame_bind (action channels) _ (body channels) (breakFrame_materializeOwnedCarriers origin tokens)
    have evaluatedFrame := actionFrame after (preparedFrame.bounded bounded)
    cases evaluated : evaluatedAction after
    all_goals rw [evaluated] at evaluatedFrame
    all_goals have evaluatedResult := evaluated
    all_goals dsimp only [evaluatedAction, tokens] at evaluatedResult
    all_goals simp only [withExitChannels, prepared, evaluatedResult]
    all_goals
      apply breakFrame_cleanupResult
      · exact fun _ => rfl
      · simp only [Bool.false_eq_true, ↓reduceIte]
        evaluation_frame_basic
      · exact bounded
      · exact preparedFrame.trans evaluatedFrame

theorem breakFrame_withCompletionChannels (channels : List Channel) (origin : Goose.Core.OriginId)
    (action : List Channel → EvalM (List Carrier))
    (body : ∀ planned, BreakFrameAction (action planned)) :
    BreakFrameAction (withCompletionChannels channels origin action) := by
  let setup : EvalM (List Channel × List ExitReservationId) := do
    let planned ← channels.mapM fun channel => match channel with
      | .construct incoming => do
          let token ← liftConstruction origin (waitExitDestination incoming)
          pure (Channel.completion token, some token)
      | .register ty => pure (Channel.register ty, none)
      | .completion _ => fault .flow
    pure (planned.map Prod.fst, planned.filterMap Prod.snd)
  have setupFrame : BreakFrameAction setup := by
    unfold setup
    evaluation_frame_basic
  intro state bounded
  unfold withCompletionChannels
  dsimp only
  split
  next planned tokens after prepared =>
    have preparedRun : setup state = .ok (planned, tokens) after := prepared
    have preparedFrame := setupFrame state bounded
    rw [preparedRun] at preparedFrame
    let evaluatedAction := do materializeOwnedCarriers origin tokens (← action planned)
    have actionFrame : BreakFrameAction evaluatedAction :=
      breakFrame_bind (action planned) _ (body planned) (breakFrame_materializeOwnedCarriers origin tokens)
    have evaluatedFrame := actionFrame after (preparedFrame.bounded bounded)
    cases evaluated : evaluatedAction after
    all_goals rw [evaluated] at evaluatedFrame
    all_goals have evaluatedResult := evaluated
    all_goals dsimp only [evaluatedAction] at evaluatedResult
    all_goals simp only [evaluatedResult]
    all_goals
      apply breakFrame_cleanupResult
      · exact fun _ => rfl
      · simp only [Bool.false_eq_true, ↓reduceIte]
        evaluation_frame_basic
      · exact bounded
      · exact preparedFrame.trans evaluatedFrame
  next reason after prepared =>
    have preparedRun : setup state = .stop reason after := prepared
    have checked := setupFrame state bounded
    rw [preparedRun] at checked
    change BreakStackFrame state after at checked ⊢
    exact checked
  next target carriers after prepared =>
    have preparedRun : setup state = .escape target carriers after := prepared
    have checked := setupFrame state bounded
    rw [preparedRun] at checked
    change BreakStackFrame state after at checked ⊢
    exact checked
  next target kind after prepared =>
    have preparedRun : setup state = .jump target kind after := prepared
    have checked := setupFrame state bounded
    rw [preparedRun] at checked
    change BreakStackFrame state after at checked ⊢
    exact checked

theorem breakFrame_execResultScope (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (channels : List Channel) (block : Block)
    (statementsAction : RuntimeActivation → List Stmt → EvalM Flow)
    (tailAction : RuntimeActivation → Expr → EvalM (List Carrier))
    (statements : ∀ environment items, BreakFrameAction (statementsAction environment items))
    (tail : ∀ environment expression, BreakFrameAction (tailAction environment expression)) :
    BreakFrameAction (execResultScope environment pre channels block statementsAction tailAction) := by
  cases block with
  | mk scope items value =>
    unfold execResultScope
    apply breakFrame_bind
    · exact breakFrame_freshScope
    · intro scopeInst
      apply breakFrame_mapActivations
      apply breakFrame_withScope
      apply breakFrame_bind
      · exact breakFrame_bindAll _ _ _
      · intro _
        apply breakFrame_bind
        · exact statements _ _
        · intro flow
          cases flow <;> cases value <;> evaluation_frame_basic
          all_goals exact tail _ _

end Goose.Proofs.ConstructionDelivery
