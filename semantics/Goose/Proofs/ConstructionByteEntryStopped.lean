import Goose.Proofs.ConstructionByteGlobalEntryBody

namespace Goose.Proofs.ConstructionAcceptedExecution

open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership

theorem execActivationBody_statements_stopped (fuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (body : Block) (before after : ExecutionState) (stop : Goose.Core.Stop)
    (stopped : execStmts fuel config
      { activation with scopes := (body.scope, before.nextScope) :: activation.scopes } body.stmts
      (ownershipResultScopeState activation body.scope before) = .stop stop after) :
    execActivationBody (fuel + 1) config activation [] body before = .stop stop after := by
  cases body with
  | mk scope statements value =>
    simp only [Block.scope, Block.stmts] at stopped
    simp only [ownershipResultScopeState, beq_iff_eq] at stopped
    simp [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set, bind, pure, withScope,
      bindAll, stopped]

theorem byteEntry_statements_stopped_module (fuel : Nat) (config : EvalConfig) (initialized : ExecutionState)
    (frame : ConstructionSourceFrame) (activation : RuntimeActivation) (after : ExecutionState) (stop : Goose.Core.Stop)
    (environmentEq : frame.interpretation.environment = activation)
    (moduleStep : runModule (fuel + 3) config .initial =
      (invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 >>= fun carriers => publishCarriers 0 carriers) initialized)
    (callStep :
      let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
      invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 initialized =
        (finishActivation config.layout activation [] 0 (execActivationBody (fuel + 1) config activation [] frame.source.impl.body) >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated)
    (stopped :
      let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
      let before := ownershipResultScopeState activation frame.source.impl.body.scope activated
      let entryFrame := entryStatementsFrame config frame activated.nextScope
      execStmts fuel config entryFrame.interpretation.environment frame.source.impl.body.stmts before = .stop stop after) :
    runModule (fuel + 3) config .initial = .stop stop after := by
  let activated := { initialized with nextAct := initialized.nextAct + 1, activations := activation :: initialized.activations }
  have stopped' : execStmts fuel config
      { activation with scopes := (frame.source.impl.body.scope, activated.nextScope) :: activation.scopes }
      frame.source.impl.body.stmts (ownershipResultScopeState activation frame.source.impl.body.scope activated) = .stop stop after := by
    simpa only [entryStatementsFrame, blockStatementsFrame, RootInterpretation.enterScope, environmentEq] using stopped
  have bodyStop := execActivationBody_statements_stopped fuel config activation frame.source.impl.body activated after stop stopped'
  dsimp only [activated] at bodyStop
  rw [moduleStep]
  simp only [bind, callStep, finishActivation, bodyStop]

#print axioms execActivationBody_statements_stopped
#print axioms byteEntry_statements_stopped_module

end Goose.Proofs.ConstructionAcceptedExecution
