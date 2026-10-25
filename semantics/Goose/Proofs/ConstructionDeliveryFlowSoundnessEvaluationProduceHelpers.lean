import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationValuesConstruct
import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationGuards

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem produce_forIn_normal (items : List α) (initial : β)
    (action : α → β → EvalM (ForInStep β))
    (body : ∀ item value, ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (action item value)) :
    ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (forIn items initial action) := by
  induction items generalizing initial with
  | nil => exact controlFlow_pure _ _ _ (List.mem_singleton_self _)
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply controlFlow_prefix
    · exact body item initial
    · intro step
      cases step with
      | done value => exact controlFlow_pure _ _ _ (List.mem_singleton_self _)
      | yield value => exact ih value

private theorem produce_arrayForIn_normal (items : Array α) (initial : β)
    (action : α → β → EvalM (ForInStep β))
    (body : ∀ item value, ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (action item value)) :
    ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (forIn items initial action) := by
  rw [← Array.forIn_toList]
  exact produce_forIn_normal _ initial action body

private theorem produce_rangeForIn_normal (range : Std.Legacy.Range) (initial : β)
    (action : Nat → β → EvalM (ForInStep β))
    (body : ∀ item value, ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (action item value)) :
    ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (forIn range initial action) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact produce_forIn_normal _ initial action body

private theorem produce_mapMLoop_normal (items : List α) (action : α → EvalM β)
    (body : ∀ item, ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (action item))
    (accumulator : List β) :
    ControlFlowAction activation [normalFlow] (fun _ => normalFlow)
      (List.mapM.loop action items accumulator) := by
  induction items generalizing accumulator with
  | nil => exact controlFlow_pure _ _ _ (List.mem_singleton_self _)
  | cons item rest ih =>
    change ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (do
      let value ← action item
      List.mapM.loop action rest (value :: accumulator))
    apply controlFlow_prefix
    · exact body item
    · intro value; exact ih (value :: accumulator)

private theorem produce_mapM_normal (items : List α) (action : α → EvalM β)
    (body : ∀ item, ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (action item)) :
    ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (items.mapM action) :=
  produce_mapMLoop_normal items action body []

elab "evaluation_produce_normal_head" : tactic => do
  let target := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  if target.isForall then
    Lean.Elab.Tactic.evalTactic (← `(tactic| intro))
    return
  unless target.getAppFn.isConstOf ``ControlFlowAction do throwError "expected control flow"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  let action := action.consumeMData
  if action.isLet then
    Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only))
    return
  let some name := action.getAppFn.constName? | throwError "expected named action"
  let key := (name.toString.splitOn ".").getLast!
  match key with
  | "pure" => Lean.Elab.Tactic.evalTactic (← `(tactic|
      exact controlFlow_pure [normalFlow] (fun _ => normalFlow) _ (List.mem_singleton_self _)))
  | "stop" | "fault" | "timeout" | "abortAt" => Lean.Elab.Tactic.evalTactic (← `(tactic|
      exact controlFlow_stop [normalFlow] (fun _ => normalFlow) _))
  | "mapM" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply produce_mapM_normal))
  | "forIn" => Lean.Elab.Tactic.evalTactic (← `(tactic|
      first | apply produce_forIn_normal | apply produce_arrayForIn_normal | apply produce_rangeForIn_normal))
  | "bind" => Lean.Elab.Tactic.evalTactic (← `(tactic| apply controlFlow_prefix))
  | "ite" | "dite" => Lean.Elab.Tactic.evalTactic (← `(tactic| split))
  | _ =>
      let frameName := Lean.Name.str `Goose.Proofs.ConstructionDelivery ("breakFrame_" ++ key)
      let jumpName := Lean.Name.str `Goose.Proofs.ConstructionDelivery
        (if key == "liftConstruction" then "neverJumps_lift" else "neverJumps_" ++ key)
      let environment ← Lean.getEnv
      unless environment.contains frameName && environment.contains jumpName do
        throwError "unrecognized administrative action {name}"
      let frame := Lean.mkIdent frameName
      let noJump := Lean.mkIdent jumpName
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        solve | (apply controlFlow_normal <;> first | apply $frame:ident | apply $noJump:ident)))

macro "evaluation_produce_normal" : tactic => `(tactic|
  repeat' first
    | assumption
    | evaluation_produce_normal_head
    | split)

theorem controlFlow_renewProducerChannels (channels : List Channel) (expression : Expr) :
    ControlFlowAction activation [normalFlow] (fun _ => normalFlow)
      (channels.mapM fun channel => match channel with
        | .register ty => pure (Channel.register ty)
        | .construct id => do
          pure (Channel.construct (← liftConstruction (expressionOrigin expression) (renewReceivingDestination id)))
        | .completion token => pure (.completion token)) := by
  apply produce_mapM_normal
  intro channel
  cases channel <;> evaluation_produce_normal

theorem controlFlow_selectProducerChannels (environment : RuntimeActivation)
    (expression : Expr) (channels : List Channel) :
    ControlFlowAction environment.act [normalFlow] (fun _ => normalFlow)
      (channels.mapM (selectCompletionChannel environment expression)) := by
  apply produce_mapM_normal
  intro channel
  exact controlFlow_normal _ (breakFrame_selectCompletionChannel _ _ _) (neverJumps_selectCompletionChannel _ _ _)

theorem controlFlow_producerDefault (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (expression : Expr) (channels : List Channel) (allowed : List StaticFlow)
    (value : ControlFlowAction environment.act allowed (fun _ => normalFlow) (evalValue fuel config environment expression))
    (build : ∀ destination, ControlFlowAction environment.act allowed (fun _ => normalFlow) (buildExpr fuel config environment destination expression)) :
    ControlFlowAction environment.act allowed (fun _ => normalFlow)
      (match channels with
        | [] => do let _ ← evalValue fuel config environment expression; pure []
        | [.register _] => do pure [Carrier.register (← evalValue fuel config environment expression)]
        | [.construct destination] => do
          buildExpr fuel config environment destination expression
          pure [Carrier.completed (← completedReceivingDestination destination)]
        | _ => fault .arity) := by
  split
  · apply controlFlow_map
    exact value
  · apply controlFlow_map
    exact value
  · apply controlFlow_suffix
    · exact build _
    · intro ignored
      evaluation_produce_normal
  · exact controlFlow_stop _ _ _

theorem controlFlow_landCarriersInto (origin : Goose.Core.OriginId) (channels : List Channel) (carriers : List Carrier) :
    ControlFlowAction activation [normalFlow] (fun _ => normalFlow) (landCarriersInto origin channels carriers) := by
  unfold landCarriersInto
  evaluation_produce_normal

end Goose.Proofs.ConstructionDelivery
