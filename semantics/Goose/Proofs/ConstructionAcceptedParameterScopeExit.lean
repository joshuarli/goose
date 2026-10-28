import Goose.Proofs.ConstructionByteEntryStopped
import Goose.Proofs.ConstructionByteEntryScopeWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execActivationBody_bound_stopped (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (pre : List (Nat × Value)) (body : Block) (before boundState after : ExecutionState) (stop : Goose.Core.Stop)
    (bound : bindAll activation.act before.nextScope pre (ownershipResultScopeState activation body.scope before) = .ok () boundState)
    (stopped : execStmts fuel config
      { activation with scopes := (body.scope, before.nextScope) :: activation.scopes } body.stmts boundState = .stop stop after) :
    execActivationBody (fuel + 1) config activation pre body before = .stop stop after := by
  cases body with
  | mk scope statements value =>
    simp only [Block.scope, Block.stmts] at bound stopped
    simp only [ownershipResultScopeState, beq_iff_eq] at bound
    simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bound, stopped]

theorem execActivationBody_bound_normal (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (pre : List (Nat × Value)) (body : Block) (before boundState after : ExecutionState)
    (channels : activation.channels = []) (tail : body.value = none)
    (bound : bindAll activation.act before.nextScope pre (ownershipResultScopeState activation body.scope before) = .ok () boundState)
    (normal : execStmts fuel config
      { activation with scopes := (body.scope, before.nextScope) :: activation.scopes } body.stmts boundState = .ok (.normal .unit) after) :
    execActivationBody (fuel + 1) config activation pre body before =
      .ok [] (releaseScopeState activation body.scope before.nextScope after) := by
  cases body with
  | mk scope statements value =>
    simp only [Block.scope, Block.stmts, Block.value] at bound normal tail ⊢
    subst value
    simp only [ownershipResultScopeState, beq_iff_eq] at bound
    simp only [channels] at normal
    simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope,
      bound, channels, normal, releaseScope]

#print axioms execActivationBody_bound_stopped
#print axioms execActivationBody_bound_normal
end Goose.Proofs.ConstructionAcceptedExecution
