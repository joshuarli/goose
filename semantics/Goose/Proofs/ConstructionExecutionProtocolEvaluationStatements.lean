import Goose.Proofs.ConstructionExecutionProtocolEvaluationContext

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct
open Goose.Core (VarId OriginId)

variable {predicate : ConstructionState → Prop} [primitives : ConstructionProtocolPrimitives predicate]
  [reservations : ConstructionReservationPrimitives predicate]
include primitives reservations

private theorem bindingConditional (condition : Prop) [Decidable condition] (yes no : EvalM α)
    (left : PreservesConstructionInvariant predicate yes)
    (right : PreservesConstructionInvariant predicate no) :
    PreservesConstructionInvariant predicate (if condition then yes else no) := by
  split <;> assumption

local elab "binding_conditional" : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless target.getAppFn.isConstOf ``PreservesConstructionInvariant do
    throwError "expected construction invariant"
  let arguments := target.getAppArgs
  let some action := arguments[arguments.size - 1]? | throwError "expected action"
  unless action.getAppFn.isConstOf ``ite do
    throwError "expected conditional action"
  Lean.Elab.Tactic.evalTactic (← `(tactic| apply bindingConditional))

private def bindLetValue (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : VarId) (expression : Expr) (origin : OriginId) (descriptor : LocalVar) (root : Goose.Core.RootInst) : EvalM Flow := do
  let value ←
    if descriptor.ty.nonfixed then
      let some implementation := config.module.impls[environment.implementation]? | fault .unbound
      let namedCandidate := implementation.results.toList.zipIdx |>.find? (fun (result, _) => result.namedLocal == some localVar)
      let named ← match namedCandidate with
        | some (result, index) =>
            match environment.channels[index]? with
            | some (.construct incoming) => do
                let destination ← liftConstruction origin (renewReceivingDestination incoming)
                let destination ← getDestination destination
                pure (if destination.capability.request == .value then some (result, index) else none)
            | _ => fault .flow
        | none => pure none
      let materialized ← if named.isNone then
          materializeProducer fuel ⟨config.module, environment.vars⟩ expression (evalValue fuel config environment expression)
        else pure none
      let destination ← match named with
        | some (_, index) =>
            match environment.channels[index]? with
            | some (.construct destination) => liftConstruction origin (renewReceivingDestination destination)
            | _ => fault .flow
        | none =>
            newDestination config.layout environment.act descriptor.ty .value origin none
              (materialized.map Array.size <|> producerCount? ⟨config.module, environment.vars⟩ expression)
      if named.isSome then liftConstruction origin (prepareNamedBinding destination descriptor.ty)
      match materialized with
      | some values => copyValue fuel config.layout destination (.fixed values) origin none
      | none => buildExpr fuel config environment destination expression
      let destination ← completedReceivingDestination destination
      if named.isNone then publishCarriers origin [.completed destination]
      let stored ← storedDestination destination
      let object ← if named.isSome then do pure (some (← liftConstruction origin reserveStorage)) else pure none
      pure (.stored { stored with ty := descriptor.ty, object := object })
    else evalValue fuel config environment expression
  bindRoot root value
  pure (.normal .unit)

set_option maxHeartbeats 2000000 in
private theorem bindLetValue_contract (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationPreservesConstructionInvariant (predicate := predicate) fuel config) (environment : RuntimeActivation)
    (localVar : VarId) (expression : Expr) (origin : OriginId) (descriptor : LocalVar) (root : Goose.Core.RootInst) :
    PreservesConstructionInvariant predicate (bindLetValue fuel config environment localVar expression origin descriptor root) := by
  cases nonfixed : descriptor.ty.nonfixed <;> simp only [bindLetValue, nonfixed, Bool.false_eq_true, ↓reduceIte]
  all_goals repeat' first
    | with_reducible exact preservesConstructionInvariant_pure _
    | with_reducible exact preservesConstructionInvariant_fault _
    | with_reducible exact preservesConstructionInvariant_fault_bind _ _
    | with_reducible exact previous.build _ _ _
    | with_reducible exact previous.value _ _
    | with_reducible exact preservesConstructionInvariant_newDestination _ _ _ _ _ _ _
    | with_reducible exact preservesConstructionInvariant_publishCarriers _ _
    | with_reducible exact preservesConstructionInvariant_copyValue _ _ _ _ _ _
    | protocol_materialize
    | with_reducible exact preservesConstructionInvariant_bindRoot _ _
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_getDestination _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_completedReceivingDestination _)
    | with_reducible exact stateQuery_preservesConstructionInvariant _ (stateQuery_storedDestination _)
    | kernel_protocol
    | reservation_protocol
    | binding_conditional
    | with_reducible apply preservesConstructionInvariant_bind
    | with_reducible split
    | with_reducible intro

set_option maxHeartbeats 2000000 in
theorem execStmt_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation) (statement : Stmt) :
    (PreservesConstructionInvariant predicate) (execStmt (fuel + 1) config environment statement) := by
  cases statement <;> try simp only [execStmt]
  case letS x e org =>
    split
    · apply preservesConstructionInvariant_bind
      · exact stateQuery_preservesConstructionInvariant _ (stateQuery_rootOf _ _)
      · intro root
        exact bindLetValue_contract fuel config previous environment x e org _ root
    · protocol_eval previous
  all_goals protocol_eval previous
  case ifS condition yes no origin =>
    cases no <;> simp only [execStmt]
    all_goals protocol_eval previous


end Goose.Proofs.ConstructionExecutionProtocol
