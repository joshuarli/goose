import Goose.Proofs.ConstructionExitCheckpointTrace
import Goose.Proofs.ConstructionExitInterruptedReturnWitness

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution.InterruptedTrace
open Goose.Construct
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks
open Goose.Proofs.ConstructionAcceptedExecution

def interruptConfig : EvalConfig := ⟨.release, interruptedByteReturn⟩

def interruptEntryImpl : Impl :=
  ⟨"entry", #[], #[], #[⟨"result", array, .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.call 1 [.byVal (.lit .i64 1)] 0) 0,
      .print [.view (.of (.var 0))] 0] none,
    .known ⟨[], [], [], [], [], [], [], [], true, true⟩⟩

def interruptEntryActivation : RuntimeActivation := ⟨0, 0, interruptEntryImpl.vars, [], []⟩

def interruptEntryEntered : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 2 interruptConfig .initial)

def interruptEntryBound : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 3 interruptConfig .initial)

def interruptEntryScope : RuntimeActivation :=
  { interruptEntryActivation with scopes := [(0, 0)] }

theorem interrupt_entry_reached :
    ExitReached 44 interruptConfig
      (.statement 40 interruptEntryScope (.letS 0 (.call 1 [.byVal (.lit .i64 1)] 0) 0)) interruptEntryBound := by
  have globals : initGlobals 44 interruptConfig (List.range interruptConfig.module.globals.size) .initial = .ok () .initial := by cbv
  have lookup : getImplementation interruptConfig interruptConfig.module.entry .initial = .ok (0, interruptEntryImpl) .initial := by cbv
  have channels : channelsFor interruptConfig.layout 0 interruptEntryImpl.results.toList 0 .initial = .ok [] .initial := by cbv
  have call : ExitReached 44 interruptConfig (.call 44 ⟨0, 0, #[], [], []⟩ 0 [] [] 0) .initial := by
    exact .call .initial (.moduleEntry 44 .initial .initial .initial .initial 0 interruptEntryImpl [] globals lookup channels)
  have receiving : CallArgumentPrefix interruptConfig 0 [] 0 .initial 0 interruptEntryImpl [] .initial := by
    exact .actual .initial .initial .initial 0 interruptEntryImpl [] lookup rfl rfl
  have arguments : evalArguments 43 interruptConfig ⟨0, 0, #[], [], []⟩ interruptEntryImpl.vars
      interruptEntryImpl.params.toList [] .initial = .ok [] .initial := by cbv
  have depth : ExecutionState.initial.activations.length < Goose.Core.maxCallDepth := by cbv
  have callPrefix := CallActivationPrefix.actual .initial .initial .initial .initial 0 interruptEntryImpl [] [] [] receiving arguments rfl depth
  let initialState := ExecutionState.initial
  have entered : { initialState with
      nextAct := initialState.nextAct + 1
      activations := ⟨0, initialState.nextAct, interruptEntryImpl.vars, [], []⟩ :: initialState.activations } = interruptEntryEntered := by cbv
  rw [entered] at callPrefix
  have activation : ExitReached 44 interruptConfig
      (.activation 43 interruptEntryActivation [] interruptEntryImpl.body 0) interruptEntryEntered := by
    exact .call call (.callActivation 43 ⟨0, 0, #[], [], []⟩ 0 [] [] 0 .initial interruptEntryEntered
      interruptEntryActivation [] interruptEntryImpl.body (by simpa [interruptEntryActivation, ExecutionState.initial] using callPrefix))
  have implementation : interruptConfig.module.impls[interruptEntryActivation.implementation]? = some interruptEntryImpl := by cbv
  have body : ExitReached 44 interruptConfig
      (.activationBody 42 interruptEntryActivation [] interruptEntryImpl.body) interruptEntryEntered :=
    .call activation (.activationBody 42 interruptEntryActivation [] interruptEntryImpl.body 0 interruptEntryEntered interruptEntryImpl implementation)
  have scope : ExitReached 44 interruptConfig
      (.activationScope 41 interruptEntryActivation [] interruptEntryImpl.body) interruptEntryEntered :=
    .call body (.activationScope 41 interruptEntryActivation [] interruptEntryImpl.body interruptEntryEntered)
  have binding : bindAll interruptEntryActivation.act interruptEntryEntered.nextScope [] { interruptEntryEntered with
      nextScope := interruptEntryEntered.nextScope + 1
      activations := interruptEntryEntered.activations.map (fun current => if current.act == interruptEntryActivation.act then
        { current with scopes := (0, interruptEntryEntered.nextScope) :: interruptEntryActivation.scopes } else current) } =
      .ok () interruptEntryBound := by cbv
  have environment : { interruptEntryActivation with scopes :=
      (0, interruptEntryEntered.nextScope) :: interruptEntryActivation.scopes } = interruptEntryScope := by cbv
  have statements : ExitReached 44 interruptConfig
      (.statements 41 interruptEntryScope [.letS 0 (.call 1 [.byVal (.lit .i64 1)] 0) 0,
        .print [.view (.of (.var 0))] 0]) interruptEntryBound := by
    have edge := ExitCallSite.activationStatements (config := interruptConfig) 41 interruptEntryActivation [] 0
      [.letS 0 (.call 1 [.byVal (.lit .i64 1)] 0) 0, .print [.view (.of (.var 0))] 0] none
      interruptEntryEntered interruptEntryBound binding
    rw [environment] at edge
    exact .call scope (by simpa [interruptEntryImpl] using edge)
  exact .call statements (.statementsHead 40 interruptEntryScope _ _ interruptEntryBound)

def interruptEntryAllocated : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 5 interruptConfig .initial)

theorem interrupt_entry_builder_call_reached :
    ExitReached 44 interruptConfig
      (.call 38 interruptEntryScope 1 [.byVal (.lit .i64 1)] [.construct 0] 0) interruptEntryAllocated := by
  let descriptor : LocalVar := ⟨"result", array, .immutable, 0, 0⟩
  let expression : Expr := .call 1 [.byVal (.lit .i64 1)] 0
  have named : StatementLetNamedPrefix interruptConfig interruptEntryScope 0 0 interruptEntryBound
      descriptor (.local 0 0 0) none interruptEntryBound := by
    apply StatementLetNamedPrefix.absent interruptEntryBound interruptEntryBound descriptor (.local 0 0 0) interruptEntryImpl
    all_goals cbv
  have materialized : materializeProducer 39 ⟨interruptConfig.module, interruptEntryScope.vars⟩ expression
      (evalValue 39 interruptConfig interruptEntryScope expression) interruptEntryBound = .ok none interruptEntryBound := by cbv
  have allocation : newDestination interruptConfig.layout interruptEntryScope.act descriptor.ty .value 0 none
      (producerCount? ⟨interruptConfig.module, interruptEntryScope.vars⟩ expression) interruptEntryBound =
      .ok 0 interruptEntryAllocated := by cbv
  have buildPrefix : StatementLetBuildPrefix 39 interruptConfig interruptEntryScope 0 expression 0
      interruptEntryBound 0 interruptEntryAllocated := by
    exact .actual interruptEntryBound interruptEntryBound interruptEntryBound interruptEntryAllocated interruptEntryAllocated
      descriptor (.local 0 0 0) none 0 named (by simpa using materialized) (by simpa using allocation) rfl
  have build : ExitReached 44 interruptConfig
      (.build 39 interruptEntryScope 0 expression) interruptEntryAllocated :=
    .call interrupt_entry_reached (.statements (.letBuild 39 interruptEntryScope 0 expression 0 interruptEntryBound interruptEntryAllocated 0 buildPrefix))
  have renewed : liftConstruction 0 (renewReceivingDestination 0) interruptEntryAllocated = .ok 0 interruptEntryAllocated := by cbv
  have site : ProducerInvocationChild interruptConfig (.build 39 interruptEntryScope 0 expression) interruptEntryAllocated
      (.call 38 interruptEntryScope 1 [.byVal (.lit .i64 1)] [.construct 0] 0) interruptEntryAllocated :=
    .build renewed (.call 1 [.byVal (.lit .i64 1)] 0 interruptEntryAllocated)
  exact .call build (.producer site)

def interruptBuilderImpl : Impl :=
  ⟨"builder", #[⟨0, .byValue⟩], #[⟨array, .value, none⟩],
    #[⟨"depth", .int .i64, .immutable, 0, 0⟩, ⟨"inner", array, .immutable, 2, 0⟩],
    interruptedReturnBuilderBody, .known ⟨[], [], [], [], [], [0], [], [], true, true⟩⟩

def interruptBuilderActivation : RuntimeActivation := ⟨1, 1, interruptBuilderImpl.vars, [], [.construct 0]⟩

def interruptBuilderEntered : ExecutionState := { interruptEntryAllocated with
  nextAct := interruptEntryAllocated.nextAct + 1
  activations := interruptBuilderActivation :: interruptEntryAllocated.activations }

def interruptBuilderBound : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 10 interruptConfig .initial)

def interruptBuilderScope : RuntimeActivation := { interruptBuilderActivation with scopes := [(0, 1)] }

theorem interrupt_entry_builder_branch_reached :
    ExitReached 44 interruptConfig
      (.statement 34 interruptBuilderScope (.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0))
      interruptBuilderBound := by
  have lookup : getImplementation interruptConfig 1 interruptEntryAllocated = .ok (1, interruptBuilderImpl) interruptEntryAllocated := by cbv
  have renew : liftConstruction 0 (renewReceivingDestination 0) interruptEntryAllocated = .ok 0 interruptEntryAllocated := by cbv
  have adapt : liftConstruction 0 (adaptDestinationType 0 array) interruptEntryAllocated = .ok () interruptEntryAllocated := by cbv
  have receivingAction : ((([Channel.construct 0].zip interruptBuilderImpl.results.toList).mapM fun pair => do
        match pair.2.request, pair.1 with
        | .register, _ => pure (Channel.register pair.2.ty)
        | .value, .construct incoming | .elementRun, .construct incoming =>
            let destination ← liftConstruction 0 (renewReceivingDestination incoming)
            liftConstruction 0 (adaptDestinationType destination pair.2.ty)
            pure (.construct destination)
        | .value, .register _ | .elementRun, .register _ => fault .shape
        | _, .completion _ => fault .flow) : EvalM (List Channel)) interruptEntryAllocated =
      .ok [.construct 0] interruptEntryAllocated := by
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mapM_cons, List.mapM_nil, bind, pure, renew, adapt, interruptBuilderImpl]
  have receiving : CallArgumentPrefix interruptConfig 1 [.construct 0] 0 interruptEntryAllocated
      1 interruptBuilderImpl [.construct 0] interruptEntryAllocated :=
    .actual interruptEntryAllocated interruptEntryAllocated interruptEntryAllocated 1 interruptBuilderImpl [.construct 0] lookup (by cbv) receivingAction
  have arguments : evalArguments 37 interruptConfig interruptEntryScope interruptBuilderImpl.vars
      interruptBuilderImpl.params.toList [.byVal (.lit .i64 1)] interruptEntryAllocated = .ok [.int .i64 1] interruptEntryAllocated := by cbv
  have renewal : (([Channel.construct 0].mapM fun channel => match channel with
      | .register ty => pure (Channel.register ty)
      | .construct destination => do pure (.construct (← liftConstruction 0 (renewReceivingDestination destination)))
      | .completion _ => fault .flow) : EvalM (List Channel)) interruptEntryAllocated = .ok [.construct 0] interruptEntryAllocated := by cbv
  have depth : interruptEntryAllocated.activations.length < Goose.Core.maxCallDepth := by cbv
  have callPrefix := CallActivationPrefix.actual interruptEntryAllocated interruptEntryAllocated interruptEntryAllocated
    interruptEntryAllocated 1 interruptBuilderImpl [.construct 0] [.construct 0] [.int .i64 1] receiving arguments renewal depth
  have entered : { interruptEntryAllocated with
      nextAct := interruptEntryAllocated.nextAct + 1
      activations := ⟨1, interruptEntryAllocated.nextAct, interruptBuilderImpl.vars, [], [.construct 0]⟩ :: interruptEntryAllocated.activations } =
      interruptBuilderEntered := by cbv
  rw [entered] at callPrefix
  have nextAct : interruptEntryAllocated.nextAct = 1 := by cbv
  rw [nextAct] at callPrefix
  have activation : ExitReached 44 interruptConfig
      (.activation 37 interruptBuilderActivation [(0, .int .i64 1)] interruptBuilderImpl.body 0) interruptBuilderEntered := by
    exact .call interrupt_entry_builder_call_reached (.callActivation 37 interruptEntryScope 1 [.byVal (.lit .i64 1)] [.construct 0] 0
      interruptEntryAllocated interruptBuilderEntered interruptBuilderActivation [(0, .int .i64 1)] interruptBuilderImpl.body
      (by simpa [interruptBuilderActivation, interruptBuilderImpl] using callPrefix))
  have implementation : interruptConfig.module.impls[interruptBuilderActivation.implementation]? = some interruptBuilderImpl := by cbv
  have body : ExitReached 44 interruptConfig
      (.activationBody 36 interruptBuilderActivation [(0, .int .i64 1)] interruptBuilderImpl.body) interruptBuilderEntered :=
    .call activation (.activationBody 36 interruptBuilderActivation [(0, .int .i64 1)] interruptBuilderImpl.body 0 interruptBuilderEntered interruptBuilderImpl implementation)
  have scope : ExitReached 44 interruptConfig
      (.activationScope 35 interruptBuilderActivation [(0, .int .i64 1)] interruptBuilderImpl.body) interruptBuilderEntered :=
    .call body (.activationScope 35 interruptBuilderActivation [(0, .int .i64 1)] interruptBuilderImpl.body interruptBuilderEntered)
  have binding : bindAll interruptBuilderActivation.act interruptBuilderEntered.nextScope [(0, .int .i64 1)] { interruptBuilderEntered with
      nextScope := interruptBuilderEntered.nextScope + 1
      activations := interruptBuilderEntered.activations.map (fun current => if current.act == interruptBuilderActivation.act then
        { current with scopes := (0, interruptBuilderEntered.nextScope) :: interruptBuilderActivation.scopes } else current) } =
      .ok () interruptBuilderBound := by cbv
  have environment : { interruptBuilderActivation with scopes :=
      (0, interruptBuilderEntered.nextScope) :: interruptBuilderActivation.scopes } = interruptBuilderScope := by cbv
  have statements : ExitReached 44 interruptConfig
      (.statements 35 interruptBuilderScope [.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0, .retValues [.bytes array [68] 0] 0])
      interruptBuilderBound := by
    have edge := ExitCallSite.activationStatements (config := interruptConfig) 35 interruptBuilderActivation
      [(0, .int .i64 1)] 0 [.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0, .retValues [.bytes array [68] 0] 0] none
      interruptBuilderEntered interruptBuilderBound binding
    rw [environment] at edge
    exact .call scope (by simpa [interruptBuilderImpl, interruptedReturnBuilderBody, recursiveBranchCondition, recursiveBranchBlock, recursiveOuterElse] using edge)
  exact .call statements (.statementsHead 34 interruptBuilderScope _ [.retValues [.bytes array [68] 0] 0] interruptBuilderBound)


#print axioms interrupt_entry_reached
#print axioms interrupt_entry_builder_call_reached
#print axioms interrupt_entry_builder_branch_reached

end Goose.Proofs.ConstructionAcceptedExecution.InterruptedTrace
