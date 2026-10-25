import Goose.Proofs.ExitExecutionInvocationStatementsNative
import Goose.Proofs.ExitExecutionInvocationStatementsDefinitions

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem statementNeverEscapes_receivePrefix (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (localVars : List Goose.Core.VarId) (producer : Expr)
    (origin : Goose.Core.OriginId) :
    ProducerNeverEscapes (statementInvocation_statementReceivePrefix fuel config environment localVars producer origin) := by
  unfold statementInvocation_statementReceivePrefix
  apply producerNeverEscapes_listMapM
  intro item
  rcases item with ⟨localVar, index⟩
  dsimp only
  cases lookup : environment.vars[localVar]? with
  | none => simpa only [lookup] using producerNeverEscapes_fault (α := Channel) .unbound
  | some descriptor =>
      dsimp only
      split
      · exact producerNeverEscapes_pure _
      · split
        · exact producerNeverEscapes_bind _ _ (producerNeverEscapes_newDestination _ _ _ _ _ _ _) (fun _ => producerNeverEscapes_pure _)
        · exact producerNeverEscapes_pure _

theorem statementNeverEscapes_receiveMaterialize (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (origin : Goose.Core.OriginId)
    (items : List (Goose.Core.VarId × Carrier)) :
    ProducerNeverEscapes (items.mapM fun (localVar, carrier) => do
      let some descriptor := environment.vars[localVar]? | fault .unbound
      match carrier with
      | .register (.fixed values) =>
          if descriptor.ty.nonfixed then
            pure (.completed (← materializedDestination fuel config.layout environment.act descriptor.ty origin values.size (.fixed values)))
          else pure carrier
      | _ => pure carrier) := by
  apply producerNeverEscapes_listMapM
  intro item
  rcases item with ⟨localVar, carrier⟩
  dsimp only
  cases lookup : environment.vars[localVar]? with
  | none => simpa only [lookup] using producerNeverEscapes_fault (α := Carrier) .unbound
  | some descriptor =>
      dsimp only
      split
      · split
        · exact producerNeverEscapes_bind _ _ (statementNeverEscapes_materializedDestination _ _ _ _ _ _ _) (fun _ => producerNeverEscapes_pure _)
        · exact producerNeverEscapes_pure _
      · exact producerNeverEscapes_pure _

theorem statementNeverEscapes_receiveBind (environment : RuntimeActivation)
    (items : List (Goose.Core.VarId × Carrier)) :
    ProducerNeverEscapes (items.forIn' (() : Unit) fun (localVar, carrier) _ _ => do
      bindRoot (← rootOf environment localVar) (← carrierValue carrier)
      pure (ForInStep.yield (() : Unit))) := by
  have same := forIn'_eq_forIn (m := EvalM) items (() : Unit)
    (fun (localVar, carrier) _ _ => do
      bindRoot (← rootOf environment localVar) (← carrierValue carrier)
      pure (ForInStep.yield (() : Unit)))
    (fun item _ => do
      bindRoot (← rootOf environment item.1) (← carrierValue item.2)
      pure (ForInStep.yield (() : Unit)))
    (by intro item member current; cases item; rfl)
  simp only [List.forIn'_eq_forIn']
  rw [same]
  apply producerNeverEscapes_listForIn
  intro item previous
  exact producerNeverEscapes_bind _ _ (producerNeverEscapes_rootOf _ _) (fun root =>
    producerNeverEscapes_bind _ _ (producerNeverEscapes_carrierValue _) (fun value =>
      producerNeverEscapes_bind _ _ (valueNeverEscapes_bindRoot _ _) (fun _ =>
        producerNeverEscapes_pure _)))

end Goose.Proofs.ExitExecution
