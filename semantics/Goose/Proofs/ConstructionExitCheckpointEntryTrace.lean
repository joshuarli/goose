import Goose.Proofs.ConstructionExitCheckpointTrace

set_option Elab.async false
set_option maxRecDepth 2048
set_option maxHeartbeats 4000000

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ExitExecution
open Goose.Proofs.ExitExecutionChecks

def recursiveEntryImpl : Impl :=
  ⟨"entry", #[], #[], #[⟨"result", array, .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.call 1 [.byVal (.lit .i64 1)] 0) 0,
      .print [.view (.of (.var 0))] 0] none,
    .known ⟨[], [], [], [], [], [], [], [], true, true⟩⟩

def recursiveEntryActivation : RuntimeActivation := ⟨0, 0, recursiveEntryImpl.vars, [], []⟩

def recursiveEntryEntered : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 2 recursiveCheckpointConfig .initial)

def recursiveEntryBound : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 3 recursiveCheckpointConfig .initial)

def recursiveEntryScope : RuntimeActivation :=
  { recursiveEntryActivation with scopes := [(0, 0)] }

theorem recursive_entry_reached :
    ExitReached 32 recursiveCheckpointConfig
      (.statement 28 recursiveEntryScope (.letS 0 (.call 1 [.byVal (.lit .i64 1)] 0) 0)) recursiveEntryBound := by
  have globals : initGlobals 32 recursiveCheckpointConfig (List.range recursiveCheckpointConfig.module.globals.size) .initial = .ok () .initial := by cbv
  have lookup : getImplementation recursiveCheckpointConfig recursiveCheckpointConfig.module.entry .initial = .ok (0, recursiveEntryImpl) .initial := by cbv
  have channels : channelsFor recursiveCheckpointConfig.layout 0 recursiveEntryImpl.results.toList 0 .initial = .ok [] .initial := by cbv
  have call : ExitReached 32 recursiveCheckpointConfig (.call 32 ⟨0, 0, #[], [], []⟩ 0 [] [] 0) .initial := by
    exact .call .initial (.moduleEntry 32 .initial .initial .initial .initial 0 recursiveEntryImpl [] globals lookup channels)
  have receiving : CallArgumentPrefix recursiveCheckpointConfig 0 [] 0 .initial 0 recursiveEntryImpl [] .initial := by
    exact .actual .initial .initial .initial 0 recursiveEntryImpl [] lookup rfl rfl
  have arguments : evalArguments 31 recursiveCheckpointConfig ⟨0, 0, #[], [], []⟩ recursiveEntryImpl.vars
      recursiveEntryImpl.params.toList [] .initial = .ok [] .initial := by cbv
  have depth : ExecutionState.initial.activations.length < Goose.Core.maxCallDepth := by cbv
  have callPrefix := CallActivationPrefix.actual .initial .initial .initial .initial 0 recursiveEntryImpl [] [] [] receiving arguments rfl depth
  let initialState := ExecutionState.initial
  have entered : { initialState with
      nextAct := initialState.nextAct + 1
      activations := ⟨0, initialState.nextAct, recursiveEntryImpl.vars, [], []⟩ :: initialState.activations } = recursiveEntryEntered := by cbv
  rw [entered] at callPrefix
  have activation : ExitReached 32 recursiveCheckpointConfig
      (.activation 31 recursiveEntryActivation [] recursiveEntryImpl.body 0) recursiveEntryEntered := by
    exact .call call (.callActivation 31 ⟨0, 0, #[], [], []⟩ 0 [] [] 0 .initial recursiveEntryEntered
      recursiveEntryActivation [] recursiveEntryImpl.body (by simpa [recursiveEntryActivation, ExecutionState.initial] using callPrefix))
  have implementation : recursiveCheckpointConfig.module.impls[recursiveEntryActivation.implementation]? = some recursiveEntryImpl := by cbv
  have body : ExitReached 32 recursiveCheckpointConfig
      (.activationBody 30 recursiveEntryActivation [] recursiveEntryImpl.body) recursiveEntryEntered :=
    .call activation (.activationBody 30 recursiveEntryActivation [] recursiveEntryImpl.body 0 recursiveEntryEntered recursiveEntryImpl implementation)
  have scope : ExitReached 32 recursiveCheckpointConfig
      (.activationScope 29 recursiveEntryActivation [] recursiveEntryImpl.body) recursiveEntryEntered :=
    .call body (.activationScope 29 recursiveEntryActivation [] recursiveEntryImpl.body recursiveEntryEntered)
  have binding : bindAll recursiveEntryActivation.act recursiveEntryEntered.nextScope [] { recursiveEntryEntered with
      nextScope := recursiveEntryEntered.nextScope + 1
      activations := recursiveEntryEntered.activations.map (fun current => if current.act == recursiveEntryActivation.act then
        { current with scopes := (0, recursiveEntryEntered.nextScope) :: recursiveEntryActivation.scopes } else current) } =
      .ok () recursiveEntryBound := by cbv
  have environment : { recursiveEntryActivation with scopes :=
      (0, recursiveEntryEntered.nextScope) :: recursiveEntryActivation.scopes } = recursiveEntryScope := by cbv
  have statements : ExitReached 32 recursiveCheckpointConfig
      (.statements 29 recursiveEntryScope [.letS 0 (.call 1 [.byVal (.lit .i64 1)] 0) 0,
        .print [.view (.of (.var 0))] 0]) recursiveEntryBound := by
    have edge := ExitCallSite.activationStatements (config := recursiveCheckpointConfig) 29 recursiveEntryActivation [] 0
      [.letS 0 (.call 1 [.byVal (.lit .i64 1)] 0) 0, .print [.view (.of (.var 0))] 0] none
      recursiveEntryEntered recursiveEntryBound binding
    rw [environment] at edge
    exact .call scope (by simpa [recursiveEntryImpl] using edge)
  exact .call statements (.statementsHead 28 recursiveEntryScope _ _ recursiveEntryBound)

def recursiveEntryAllocated : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 5 recursiveCheckpointConfig .initial)

theorem recursive_entry_builder_call_reached :
    ExitReached 32 recursiveCheckpointConfig
      (.call 26 recursiveEntryScope 1 [.byVal (.lit .i64 1)] [.construct 0] 0) recursiveEntryAllocated := by
  let descriptor : LocalVar := ⟨"result", array, .immutable, 0, 0⟩
  let expression : Expr := .call 1 [.byVal (.lit .i64 1)] 0
  have named : StatementLetNamedPrefix recursiveCheckpointConfig recursiveEntryScope 0 0 recursiveEntryBound
      descriptor (.local 0 0 0) none recursiveEntryBound := by
    apply StatementLetNamedPrefix.absent recursiveEntryBound recursiveEntryBound descriptor (.local 0 0 0) recursiveEntryImpl
    all_goals cbv
  have materialized : materializeProducer 27 ⟨recursiveCheckpointConfig.module, recursiveEntryScope.vars⟩ expression
      (evalValue 27 recursiveCheckpointConfig recursiveEntryScope expression) recursiveEntryBound = .ok none recursiveEntryBound := by cbv
  have allocation : newDestination recursiveCheckpointConfig.layout recursiveEntryScope.act descriptor.ty .value 0 none
      (producerCount? ⟨recursiveCheckpointConfig.module, recursiveEntryScope.vars⟩ expression) recursiveEntryBound =
      .ok 0 recursiveEntryAllocated := by cbv
  have buildPrefix : StatementLetBuildPrefix 27 recursiveCheckpointConfig recursiveEntryScope 0 expression 0
      recursiveEntryBound 0 recursiveEntryAllocated := by
    exact .actual recursiveEntryBound recursiveEntryBound recursiveEntryBound recursiveEntryAllocated recursiveEntryAllocated
      descriptor (.local 0 0 0) none 0 named (by simpa using materialized) (by simpa using allocation) rfl
  have build : ExitReached 32 recursiveCheckpointConfig
      (.build 27 recursiveEntryScope 0 expression) recursiveEntryAllocated :=
    .call recursive_entry_reached (.statements (.letBuild 27 recursiveEntryScope 0 expression 0 recursiveEntryBound recursiveEntryAllocated 0 buildPrefix))
  have renewed : liftConstruction 0 (renewReceivingDestination 0) recursiveEntryAllocated = .ok 0 recursiveEntryAllocated := by cbv
  have site : ProducerInvocationChild recursiveCheckpointConfig (.build 27 recursiveEntryScope 0 expression) recursiveEntryAllocated
      (.call 26 recursiveEntryScope 1 [.byVal (.lit .i64 1)] [.construct 0] 0) recursiveEntryAllocated :=
    .build renewed (.call 1 [.byVal (.lit .i64 1)] 0 recursiveEntryAllocated)
  exact .call build (.producer site)

def recursiveBuilderImpl : Impl :=
  ⟨"builder", #[⟨0, .byValue⟩], #[⟨array, .value, none⟩],
    #[⟨"depth", .int .i64, .immutable, 0, 0⟩, ⟨"inner", array, .immutable, 2, 0⟩],
    recursiveOuterBody, .known ⟨[], [], [], [], [], [0], [], [], true, true⟩⟩

def recursiveBuilderActivation : RuntimeActivation := ⟨1, 1, recursiveBuilderImpl.vars, [], [.construct 0]⟩

def recursiveBuilderEntered : ExecutionState := { recursiveEntryAllocated with
  nextAct := recursiveEntryAllocated.nextAct + 1
  activations := recursiveBuilderActivation :: recursiveEntryAllocated.activations }

def recursiveBuilderBound : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 10 recursiveCheckpointConfig .initial)

def recursiveBuilderScope : RuntimeActivation := { recursiveBuilderActivation with scopes := [(0, 1)] }

theorem recursive_entry_builder_branch_reached :
    ExitReached 32 recursiveCheckpointConfig
      (.statement 22 recursiveBuilderScope (.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0))
      recursiveBuilderBound := by
  have lookup : getImplementation recursiveCheckpointConfig 1 recursiveEntryAllocated = .ok (1, recursiveBuilderImpl) recursiveEntryAllocated := by cbv
  have renew : liftConstruction 0 (renewReceivingDestination 0) recursiveEntryAllocated = .ok 0 recursiveEntryAllocated := by cbv
  have adapt : liftConstruction 0 (adaptDestinationType 0 array) recursiveEntryAllocated = .ok () recursiveEntryAllocated := by cbv
  have receivingAction : ((([Channel.construct 0].zip recursiveBuilderImpl.results.toList).mapM fun pair => do
        match pair.2.request, pair.1 with
        | .register, _ => pure (Channel.register pair.2.ty)
        | .value, .construct incoming | .elementRun, .construct incoming =>
            let destination ← liftConstruction 0 (renewReceivingDestination incoming)
            liftConstruction 0 (adaptDestinationType destination pair.2.ty)
            pure (.construct destination)
        | .value, .register _ | .elementRun, .register _ => fault .shape
        | _, .completion _ => fault .flow) : EvalM (List Channel)) recursiveEntryAllocated =
      .ok [.construct 0] recursiveEntryAllocated := by
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mapM_cons, List.mapM_nil, bind, pure, renew, adapt, recursiveBuilderImpl]
  have receiving : CallArgumentPrefix recursiveCheckpointConfig 1 [.construct 0] 0 recursiveEntryAllocated
      1 recursiveBuilderImpl [.construct 0] recursiveEntryAllocated :=
    .actual recursiveEntryAllocated recursiveEntryAllocated recursiveEntryAllocated 1 recursiveBuilderImpl [.construct 0] lookup (by cbv) receivingAction
  have arguments : evalArguments 25 recursiveCheckpointConfig recursiveEntryScope recursiveBuilderImpl.vars
      recursiveBuilderImpl.params.toList [.byVal (.lit .i64 1)] recursiveEntryAllocated = .ok [.int .i64 1] recursiveEntryAllocated := by cbv
  have renewal : (([Channel.construct 0].mapM fun channel => match channel with
      | .register ty => pure (Channel.register ty)
      | .construct destination => do pure (.construct (← liftConstruction 0 (renewReceivingDestination destination)))
      | .completion _ => fault .flow) : EvalM (List Channel)) recursiveEntryAllocated = .ok [.construct 0] recursiveEntryAllocated := by cbv
  have depth : recursiveEntryAllocated.activations.length < Goose.Core.maxCallDepth := by cbv
  have callPrefix := CallActivationPrefix.actual recursiveEntryAllocated recursiveEntryAllocated recursiveEntryAllocated
    recursiveEntryAllocated 1 recursiveBuilderImpl [.construct 0] [.construct 0] [.int .i64 1] receiving arguments renewal depth
  have entered : { recursiveEntryAllocated with
      nextAct := recursiveEntryAllocated.nextAct + 1
      activations := ⟨1, recursiveEntryAllocated.nextAct, recursiveBuilderImpl.vars, [], [.construct 0]⟩ :: recursiveEntryAllocated.activations } =
      recursiveBuilderEntered := by cbv
  rw [entered] at callPrefix
  have nextAct : recursiveEntryAllocated.nextAct = 1 := by cbv
  rw [nextAct] at callPrefix
  have activation : ExitReached 32 recursiveCheckpointConfig
      (.activation 25 recursiveBuilderActivation [(0, .int .i64 1)] recursiveBuilderImpl.body 0) recursiveBuilderEntered := by
    exact .call recursive_entry_builder_call_reached (.callActivation 25 recursiveEntryScope 1 [.byVal (.lit .i64 1)] [.construct 0] 0
      recursiveEntryAllocated recursiveBuilderEntered recursiveBuilderActivation [(0, .int .i64 1)] recursiveBuilderImpl.body
      (by simpa [recursiveBuilderActivation, recursiveBuilderImpl] using callPrefix))
  have implementation : recursiveCheckpointConfig.module.impls[recursiveBuilderActivation.implementation]? = some recursiveBuilderImpl := by cbv
  have body : ExitReached 32 recursiveCheckpointConfig
      (.activationBody 24 recursiveBuilderActivation [(0, .int .i64 1)] recursiveBuilderImpl.body) recursiveBuilderEntered :=
    .call activation (.activationBody 24 recursiveBuilderActivation [(0, .int .i64 1)] recursiveBuilderImpl.body 0 recursiveBuilderEntered recursiveBuilderImpl implementation)
  have scope : ExitReached 32 recursiveCheckpointConfig
      (.activationScope 23 recursiveBuilderActivation [(0, .int .i64 1)] recursiveBuilderImpl.body) recursiveBuilderEntered :=
    .call body (.activationScope 23 recursiveBuilderActivation [(0, .int .i64 1)] recursiveBuilderImpl.body recursiveBuilderEntered)
  have binding : bindAll recursiveBuilderActivation.act recursiveBuilderEntered.nextScope [(0, .int .i64 1)] { recursiveBuilderEntered with
      nextScope := recursiveBuilderEntered.nextScope + 1
      activations := recursiveBuilderEntered.activations.map (fun current => if current.act == recursiveBuilderActivation.act then
        { current with scopes := (0, recursiveBuilderEntered.nextScope) :: recursiveBuilderActivation.scopes } else current) } =
      .ok () recursiveBuilderBound := by cbv
  have environment : { recursiveBuilderActivation with scopes :=
      (0, recursiveBuilderEntered.nextScope) :: recursiveBuilderActivation.scopes } = recursiveBuilderScope := by cbv
  have statements : ExitReached 32 recursiveCheckpointConfig
      (.statements 23 recursiveBuilderScope [.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0])
      recursiveBuilderBound := by
    have edge := ExitCallSite.activationStatements (config := recursiveCheckpointConfig) 23 recursiveBuilderActivation
      [(0, .int .i64 1)] 0 [.ifS recursiveBranchCondition recursiveBranchBlock (some recursiveOuterElse) 0] none
      recursiveBuilderEntered recursiveBuilderBound binding
    rw [environment] at edge
    exact .call scope (by simpa [recursiveBuilderImpl, recursiveOuterBody] using edge)
  exact .call statements (.statementsHead 22 recursiveBuilderScope _ [] recursiveBuilderBound)

def recursiveElseBound : ExecutionState := { recursiveBuilderBound with nextScope := recursiveBuilderBound.nextScope + 1 }

def recursiveElseScope : RuntimeActivation := { recursiveBuilderScope with scopes := (2, recursiveBuilderBound.nextScope) :: recursiveBuilderScope.scopes }

def recursiveElseAllocated : ExecutionState := Goose.Proofs.Exit.stepState (runModule 14 recursiveCheckpointConfig .initial)

theorem recursive_outer_activation_reached :
    ExitReached 32 recursiveCheckpointConfig
      (.activation 16 recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody 0) recursiveOuterEntered := by
  have condition : ((do expectBool (← evalValue 21 recursiveCheckpointConfig recursiveBuilderScope recursiveBranchCondition)) : EvalM Bool)
      recursiveBuilderBound = .ok false recursiveBuilderBound := by cbv
  have block : ExitReached 32 recursiveCheckpointConfig
      (.block 21 recursiveBuilderScope [] [] recursiveOuterElse) recursiveBuilderBound :=
    .call recursive_entry_builder_branch_reached (.statements (.ifNo 21 recursiveBuilderScope recursiveBranchCondition recursiveBranchBlock
      recursiveOuterElse 0 recursiveBuilderBound recursiveBuilderBound condition))
  have binding : bindAll recursiveBuilderScope.act recursiveBuilderBound.nextScope []
      { recursiveBuilderBound with nextScope := recursiveBuilderBound.nextScope + 1 } = .ok () recursiveElseBound := by cbv
  have statements : ExitReached 32 recursiveCheckpointConfig
      (.statements 20 recursiveElseScope
        [.letS 1 (.call 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] 0) 0,
          .print [.view (.of (.var 1))] 0, .retValues [.bytes array [65] 0] 0]) recursiveElseBound := by
    have edge := ExitCallSite.blockStatements (config := recursiveCheckpointConfig) 20 recursiveBuilderScope [] [] 2
      [.letS 1 (.call 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] 0) 0,
        .print [.view (.of (.var 1))] 0, .retValues [.bytes array [65] 0] 0] none recursiveBuilderBound recursiveElseBound binding
    exact .call block (by simpa [recursiveOuterElse, recursiveElseScope] using edge)
  let expression : Expr := .call 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] 0
  have statement : ExitReached 32 recursiveCheckpointConfig (.statement 19 recursiveElseScope (.letS 1 expression 0)) recursiveElseBound :=
    .call statements (.statementsHead 19 recursiveElseScope _ _ recursiveElseBound)
  let descriptor : LocalVar := ⟨"inner", array, .immutable, 2, 0⟩
  have named : StatementLetNamedPrefix recursiveCheckpointConfig recursiveElseScope 1 0 recursiveElseBound
      descriptor (.local 1 2 1) none recursiveElseBound := by
    apply StatementLetNamedPrefix.absent recursiveElseBound recursiveElseBound descriptor (.local 1 2 1) recursiveBuilderImpl
    all_goals cbv
  have materialized : materializeProducer 18 ⟨recursiveCheckpointConfig.module, recursiveElseScope.vars⟩ expression
      (evalValue 18 recursiveCheckpointConfig recursiveElseScope expression) recursiveElseBound = .ok none recursiveElseBound := by cbv
  have allocation : newDestination recursiveCheckpointConfig.layout recursiveElseScope.act descriptor.ty .value 0 none
      (producerCount? ⟨recursiveCheckpointConfig.module, recursiveElseScope.vars⟩ expression) recursiveElseBound =
      .ok 1 recursiveElseAllocated := by cbv
  have buildPrefix : StatementLetBuildPrefix 18 recursiveCheckpointConfig recursiveElseScope 1 expression 0
      recursiveElseBound 1 recursiveElseAllocated := by
    exact .actual recursiveElseBound recursiveElseBound recursiveElseBound recursiveElseAllocated recursiveElseAllocated
      descriptor (.local 1 2 1) none 1 named (by simpa using materialized) (by simpa using allocation) rfl
  have build : ExitReached 32 recursiveCheckpointConfig (.build 18 recursiveElseScope 1 expression) recursiveElseAllocated :=
    .call statement (.statements (.letBuild 18 recursiveElseScope 1 expression 0 recursiveElseBound recursiveElseAllocated 1 buildPrefix))
  have renewed : liftConstruction 0 (renewReceivingDestination 1) recursiveElseAllocated = .ok 1 recursiveElseAllocated := by cbv
  have call : ExitReached 32 recursiveCheckpointConfig
      (.call 17 recursiveElseScope 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] [.construct 1] 0) recursiveElseAllocated :=
    .call build (.producer (.build renewed (.call 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] 0 recursiveElseAllocated)))
  have lookup : getImplementation recursiveCheckpointConfig 1 recursiveElseAllocated = .ok (1, recursiveBuilderImpl) recursiveElseAllocated := by cbv
  have renew : liftConstruction 0 (renewReceivingDestination 1) recursiveElseAllocated = .ok 1 recursiveElseAllocated := by cbv
  have adapt : liftConstruction 0 (adaptDestinationType 1 array) recursiveElseAllocated = .ok () recursiveElseAllocated := by cbv
  have receivingAction : ((([Channel.construct 1].zip recursiveBuilderImpl.results.toList).mapM fun pair => do
        match pair.2.request, pair.1 with
        | .register, _ => pure (Channel.register pair.2.ty)
        | .value, .construct incoming | .elementRun, .construct incoming =>
            let destination ← liftConstruction 0 (renewReceivingDestination incoming)
            liftConstruction 0 (adaptDestinationType destination pair.2.ty)
            pure (.construct destination)
        | .value, .register _ | .elementRun, .register _ => fault .shape
        | _, .completion _ => fault .flow) : EvalM (List Channel)) recursiveElseAllocated =
      .ok [.construct 1] recursiveElseAllocated := by
    simp only [List.zip_cons_cons, List.zip_nil_left, List.mapM_cons, List.mapM_nil, bind, pure, renew, adapt, recursiveBuilderImpl]
  have receiving : CallArgumentPrefix recursiveCheckpointConfig 1 [.construct 1] 0 recursiveElseAllocated
      1 recursiveBuilderImpl [.construct 1] recursiveElseAllocated :=
    .actual recursiveElseAllocated recursiveElseAllocated recursiveElseAllocated 1 recursiveBuilderImpl [.construct 1] lookup (by cbv) receivingAction
  have arguments : evalArguments 16 recursiveCheckpointConfig recursiveElseScope recursiveBuilderImpl.vars
      recursiveBuilderImpl.params.toList [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] recursiveElseAllocated =
      .ok [.int .i64 0] recursiveElseAllocated := by cbv
  have renewal : (([Channel.construct 1].mapM fun channel => match channel with
      | .register ty => pure (Channel.register ty)
      | .construct destination => do pure (.construct (← liftConstruction 0 (renewReceivingDestination destination)))
      | .completion _ => fault .flow) : EvalM (List Channel)) recursiveElseAllocated = .ok [.construct 1] recursiveElseAllocated := by cbv
  have depth : recursiveElseAllocated.activations.length < Goose.Core.maxCallDepth := by cbv
  have callPrefix := CallActivationPrefix.actual recursiveElseAllocated recursiveElseAllocated recursiveElseAllocated
    recursiveElseAllocated 1 recursiveBuilderImpl [.construct 1] [.construct 1] [.int .i64 0] receiving arguments renewal depth
  have entered : { recursiveElseAllocated with
      nextAct := recursiveElseAllocated.nextAct + 1
      activations := ⟨1, recursiveElseAllocated.nextAct, recursiveBuilderImpl.vars, [], [.construct 1]⟩ :: recursiveElseAllocated.activations } =
      recursiveOuterEntered := by cbv
  rw [entered] at callPrefix
  have nextAct : recursiveElseAllocated.nextAct = 2 := by cbv
  rw [nextAct] at callPrefix
  exact .call call (.callActivation 16 recursiveElseScope 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] [.construct 1] 0
    recursiveElseAllocated recursiveOuterEntered recursiveOuterActivation [(0, .int .i64 0)] recursiveOuterBody
    (by simpa [recursiveOuterActivation, recursiveCheckpointTarget, recursiveBuilderImpl, array] using callPrefix))

theorem recursive_successful_run_reaches_return :
    ExitReached 32 recursiveCheckpointConfig
      (.statement 4 recursiveCheckpointSource (.returnFrom 0 [.bytes array [66] 0] 0)) recursiveDirectCheckpoint :=
  recursive_outer_activation_reaches_return recursive_outer_activation_reached

def recursiveFullFinal : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 32 recursiveCheckpointConfig .initial)

theorem recursive_successful_run_execution :
    runModule 32 recursiveCheckpointConfig .initial = .ok () recursiveFullFinal ∧
    recursiveFullFinal.construction.stdout.data.toList = [66, 10, 65, 10] := by
  constructor <;> cbv

theorem validated_recursive_uninterrupted_return :
    validate recursiveDestinations = .ok () ∧
    runModule 32 recursiveCheckpointConfig .initial = .ok () recursiveFullFinal ∧
    recursiveFullFinal.construction.stdout.data.toList = [66, 10, 65, 10] ∧
    ExitReached 32 recursiveCheckpointConfig
      (.statement 4 recursiveCheckpointSource (.returnFrom 0 [.bytes array [66] 0] 0)) recursiveDirectCheckpoint ∧
    AcceptedWorld recursiveCheckpointConfig 0 recursiveDirectCheckpoint recursiveCheckpointAmbient
      recursiveCheckpointTypes recursiveCheckpointLive [] [] ∧
    EvaluationHistoryCoverage recursiveDirectCheckpoint recursiveCheckpointAmbient [] ∧
    (∃ after : ExecutionState,
      let cleaned := { after with construction := { after.construction with
        exitReservations := after.construction.exitReservations.set! 0 .released } }
      execStmt 4 recursiveCheckpointConfig recursiveCheckpointSource (.returnFrom 0 [.bytes array [66] 0] 0)
        recursiveDirectCheckpoint = .escape ⟨2, .nonlocal 0⟩ [.completed 1] cleaned ∧
      finishChannels recursiveCheckpointConfig.layout [.construct 1] [.varr (.int .u8)] [.completed 1] 0 cleaned = .ok () cleaned) ∧
    ∃ final : ExecutionState, enterActivation 16 recursiveCheckpointConfig recursiveOuterActivation
      [(0, .int .i64 0)] recursiveOuterBody 0 recursiveOuterEntered = .ok [.completed 1] final := by
  obtain ⟨_, _, _, after, final, handled, _⟩ := recursive_outer_trace_checked_handler recursive_outer_activation_reached
  obtain ⟨built, escaped, finished, _⟩ := recursive_checkpoint_direct_return
  exact ⟨validated_recursive_direct_return.1, recursive_successful_run_execution.1,
    recursive_successful_run_execution.2, recursive_successful_run_reaches_return, recursive_checkpoint_world,
    recursive_checkpoint_ambient_history, ⟨built, escaped, finished⟩, ⟨final, handled⟩⟩

#print axioms validated_recursive_uninterrupted_return
#print axioms recursive_successful_run_execution

#print axioms recursive_successful_run_reaches_return
#print axioms recursive_outer_activation_reached

#print axioms recursive_entry_builder_branch_reached

#print axioms recursive_entry_builder_call_reached

#print axioms recursive_entry_reached

end Goose.Proofs.ConstructionAcceptedExecution
