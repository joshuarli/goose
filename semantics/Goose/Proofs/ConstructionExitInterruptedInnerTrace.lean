import Goose.Proofs.ConstructionExitInterruptedEntryTrace

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution.InterruptedTrace
open Goose.Construct
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks
open Goose.Proofs.ConstructionAcceptedExecution

def interruptElseBound : ExecutionState := { interruptBuilderBound with nextScope := interruptBuilderBound.nextScope + 1 }

def interruptElseScope : RuntimeActivation := { interruptBuilderScope with scopes := (2, interruptBuilderBound.nextScope) :: interruptBuilderScope.scopes }

def interruptElseAllocated : ExecutionState := Goose.Proofs.Exit.stepState (runModule 14 interruptConfig .initial)

theorem interrupt_outer_activation_reached :
    ExitReached 44 interruptConfig
      (.activation 28 recursiveOuterActivation [(0, .int .i64 0)] interruptedReturnBuilderBody 0) recursiveOuterEntered := by
  have condition : ((do expectBool (← evalValue 33 interruptConfig interruptBuilderScope recursiveBranchCondition)) : EvalM Bool)
      interruptBuilderBound = .ok false interruptBuilderBound := by cbv
  have block : ExitReached 44 interruptConfig
      (.block 33 interruptBuilderScope [] [] recursiveOuterElse) interruptBuilderBound :=
    .call interrupt_entry_builder_branch_reached (.statements (.ifNo 33 interruptBuilderScope recursiveBranchCondition recursiveBranchBlock
      recursiveOuterElse 0 interruptBuilderBound interruptBuilderBound condition))
  have binding : bindAll interruptBuilderScope.act interruptBuilderBound.nextScope []
      { interruptBuilderBound with nextScope := interruptBuilderBound.nextScope + 1 } = .ok () interruptElseBound := by cbv
  have statements : ExitReached 44 interruptConfig
      (.statements 32 interruptElseScope
        [.letS 1 (.call 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] 0) 0,
          .print [.view (.of (.var 1))] 0, .retValues [.bytes array [65] 0] 0]) interruptElseBound := by
    have edge := ExitCallSite.blockStatements (config := interruptConfig) 32 interruptBuilderScope [] [] 2
      [.letS 1 (.call 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] 0) 0,
        .print [.view (.of (.var 1))] 0, .retValues [.bytes array [65] 0] 0] none interruptBuilderBound interruptElseBound binding
    exact .call block (by simpa [recursiveOuterElse, interruptElseScope] using edge)
  let expression : Expr := .call 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] 0
  have statement : ExitReached 44 interruptConfig (.statement 31 interruptElseScope (.letS 1 expression 0)) interruptElseBound :=
    .call statements (.statementsHead 31 interruptElseScope _ _ interruptElseBound)
  let descriptor : LocalVar := ⟨"inner", array, .immutable, 2, 0⟩
  have named : StatementLetNamedPrefix interruptConfig interruptElseScope 1 0 interruptElseBound
      descriptor (.local 1 2 1) none interruptElseBound := by
    apply StatementLetNamedPrefix.absent interruptElseBound interruptElseBound descriptor (.local 1 2 1) interruptBuilderImpl
    all_goals cbv
  have materialized : materializeProducer 30 ⟨interruptConfig.module, interruptElseScope.vars⟩ expression
      (evalValue 30 interruptConfig interruptElseScope expression) interruptElseBound = .ok none interruptElseBound := by cbv
  have allocation : newDestination interruptConfig.layout interruptElseScope.act descriptor.ty .value 0 none
      (producerCount? ⟨interruptConfig.module, interruptElseScope.vars⟩ expression) interruptElseBound =
      .ok 1 interruptElseAllocated := by cbv
  have buildPrefix : StatementLetBuildPrefix 30 interruptConfig interruptElseScope 1 expression 0
      interruptElseBound 1 interruptElseAllocated := by
    exact .actual interruptElseBound interruptElseBound interruptElseBound interruptElseAllocated interruptElseAllocated
      descriptor (.local 1 2 1) none 1 named (by simpa using materialized) (by simpa using allocation) rfl
  have build : ExitReached 44 interruptConfig (.build 30 interruptElseScope 1 expression) interruptElseAllocated :=
    .call statement (.statements (.letBuild 30 interruptElseScope 1 expression 0 interruptElseBound interruptElseAllocated 1 buildPrefix))
  have renewed : liftConstruction 0 (renewReceivingDestination 1) interruptElseAllocated = .ok 1 interruptElseAllocated := by cbv
  have call : ExitReached 44 interruptConfig
      (.call 29 interruptElseScope 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] [.construct 1] 0) interruptElseAllocated :=
    .call build (.producer (.build renewed (.call 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] 0 interruptElseAllocated)))
  have lookup : getImplementation interruptConfig 1 interruptElseAllocated = .ok (1, interruptBuilderImpl) interruptElseAllocated := by cbv
  have renew : liftConstruction 0 (renewReceivingDestination 1) interruptElseAllocated = .ok 1 interruptElseAllocated := by cbv
  have adapt : liftConstruction 0 (adaptDestinationType 1 array) interruptElseAllocated = .ok () interruptElseAllocated := by cbv
  have receivingAction : ((([Channel.construct 1].zip interruptBuilderImpl.results.toList).mapM fun pair => do
        match pair.2.request, pair.1 with
        | .register, _ => pure (Channel.register pair.2.ty)
        | .value, .construct incoming | .elementRun, .construct incoming =>
            let destination ← liftConstruction 0 (renewReceivingDestination incoming)
            liftConstruction 0 (adaptDestinationType destination pair.2.ty)
            pure (.construct destination)
        | .value, .register _ | .elementRun, .register _ => fault .shape
        | _, .completion _ => fault .flow) : EvalM (List Channel)) interruptElseAllocated =
      .ok [.construct 1] interruptElseAllocated := by
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mapM_cons, List.mapM_nil, bind, pure, renew, adapt, interruptBuilderImpl]
  have receiving : CallArgumentPrefix interruptConfig 1 [.construct 1] 0 interruptElseAllocated
      1 interruptBuilderImpl [.construct 1] interruptElseAllocated :=
    .actual interruptElseAllocated interruptElseAllocated interruptElseAllocated 1 interruptBuilderImpl [.construct 1] lookup (by cbv) receivingAction
  have arguments : evalArguments 28 interruptConfig interruptElseScope interruptBuilderImpl.vars
      interruptBuilderImpl.params.toList [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] interruptElseAllocated =
      .ok [.int .i64 0] interruptElseAllocated := by cbv
  have renewal : (([Channel.construct 1].mapM fun channel => match channel with
      | .register ty => pure (Channel.register ty)
      | .construct destination => do pure (.construct (← liftConstruction 0 (renewReceivingDestination destination)))
      | .completion _ => fault .flow) : EvalM (List Channel)) interruptElseAllocated = .ok [.construct 1] interruptElseAllocated := by cbv
  have depth : interruptElseAllocated.activations.length < Goose.Core.maxCallDepth := by cbv
  have callPrefix := CallActivationPrefix.actual interruptElseAllocated interruptElseAllocated interruptElseAllocated
    interruptElseAllocated 1 interruptBuilderImpl [.construct 1] [.construct 1] [.int .i64 0] receiving arguments renewal depth
  have entered : { interruptElseAllocated with
      nextAct := interruptElseAllocated.nextAct + 1
      activations := ⟨1, interruptElseAllocated.nextAct, interruptBuilderImpl.vars, [], [.construct 1]⟩ :: interruptElseAllocated.activations } =
      recursiveOuterEntered := by cbv
  rw [entered] at callPrefix
  have nextAct : interruptElseAllocated.nextAct = 2 := by cbv
  rw [nextAct] at callPrefix
  exact .call call (.callActivation 28 interruptElseScope 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] [.construct 1] 0
    interruptElseAllocated recursiveOuterEntered recursiveOuterActivation [(0, .int .i64 0)] interruptedReturnBuilderBody
    (by simpa [recursiveOuterActivation, recursiveCheckpointTarget, interruptBuilderImpl, array] using callPrefix))


#print axioms interrupt_outer_activation_reached

end Goose.Proofs.ConstructionAcceptedExecution.InterruptedTrace
