import Goose.Construct.Validate
import Goose.Proofs.ExitExecution

set_option Elab.async false

namespace Goose.Proofs.ExitExecutionChecks
open Goose.Construct

def array : Ty := .varr (.int .u8)

def recursiveDestinations : Module :=
  ⟨#["exit-execution.goose"], #[], #[],
    #[⟨"entry", #[], #[], #[⟨"result", array, .immutable, 0, 0⟩],
      .mk 0 [.letS 0 (.call 1 [.byVal (.lit .i64 1)] 0) 0,
        .print [.view (.of (.var 0))] 0] none,
      .known ⟨[], [], [], [], [], [], [], [], true, true⟩⟩,
      ⟨"builder", #[⟨0, .byValue⟩], #[⟨array, .value, none⟩],
        #[⟨"depth", .int .i64, .immutable, 0, 0⟩, ⟨"inner", array, .immutable, 2, 0⟩],
        .mk 0 [.ifS (.cmp .eq (.read (.var 0)) (.lit .i64 0))
          (.mk 1 [.expr (.call 2 [] 0) 0] none)
          (some (.mk 2 [.letS 1 (.call 1 [.byVal (.bin .sub (.read (.var 0)) (.lit .i64 1) 0)] 0) 0,
            .print [.view (.of (.var 1))] 0, .retValues [.bytes array [65] 0] 0] none)) 0] none,
        .known ⟨[], [], [], [], [], [0], [], [], true, true⟩⟩,
      ⟨"helper", #[], #[], #[], .mk 0 [.returnFrom 0 [.bytes array [66] 0] 0] none,
        .known ⟨[], [], [], [], [], [], [0], [0], false, false⟩⟩],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "builder", [], [[]], []⟩,
      ⟨2, "helper", [], [], []⟩], 0, #[⟨0, 17, "call"⟩], #[], #[⟨1, []⟩]⟩

def accepts (module : Module) : Bool :=
  match validate module with | .ok _ => true | .error _ => false

theorem recursiveDestinations_validated : accepts recursiveDestinations = true := by
  cbv

def returnedObservation : ExecutionResult → Option (List UInt8 × List Goose.Core.ConstructionEvent)
  | .done .returned stdout events => some (stdout.data.toList, events)
  | _ => none

set_option maxRecDepth 2048 in
theorem recursiveDestinations_execution :
    returnedObservation (eval 200 .release recursiveDestinations) =
      some ([66, 10, 65, 10], [.begin 0, .begin 1, .write 1 0, .publish 1, .write 0 0, .publish 0]) := by
  cbv

def timeoutActivations : ExecutionStep α → Option (List Goose.Core.ActId × Nat)
  | .stop .timeout state => some (state.activations.map (·.act), state.nextAct)
  | _ => none

def selectedActivation : ExecutionStep RuntimeActivation → Option Goose.Core.ActId
  | .ok activation _ => some activation.act
  | _ => none

theorem recursive_live_activations :
    timeoutActivations (runModule 28 ⟨.release, recursiveDestinations⟩ .initial) =
      some ([3, 2, 1, 0], 4) := by cbv

theorem recursive_live_activations_fresh :
    Goose.Proofs.ExitExecution.FreshActivations
      (Goose.Proofs.Exit.stepState (runModule 28 ⟨.release, recursiveDestinations⟩ .initial)) :=
  Goose.Proofs.ExitExecution.runModule_freshActivations _ _

set_option maxRecDepth 2048 in
theorem recursive_live_nearest_target :
    selectedActivation (targetActivation ⟨.release, recursiveDestinations⟩ 0
      (Goose.Proofs.Exit.stepState (runModule 28 ⟨.release, recursiveDestinations⟩ .initial))) = some 2 := by
  cbv

def overlappingTargets : Module :=
  ⟨#["overlapping-targets.goose"], #[.int .i64], #[],
    #[⟨"entry", #[], #[], #[⟨"result", .int .i64, .immutable, 0, 0⟩],
        .mk 0 [.letS 0 (.call 1 [] 0) 0, .print [.expr (.read (.var 0))] 0] none,
        .known ⟨[], [], [], [], [], [], [], [], false, true⟩⟩,
      ⟨"member", #[], #[⟨.int .i64, .register, none⟩], #[],
        .mk 0 [.expr (.call 2 [] 0) 0] (some (.lit .i64 999)),
        .known ⟨[], [], [], [], [], [], [], [], false, false⟩⟩,
      ⟨"escape", #[], #[], #[], .mk 0 [.returnFrom 1 [.lit .i64 7] 0] none,
        .known ⟨[], [], [], [], [], [], [1], [1], false, false⟩⟩,
      ⟨"other", #[], #[⟨.int .i64, .register, none⟩], #[],
        .mk 0 [] (some (.lit .i64 9)),
        .known ⟨[], [], [], [], [], [], [], [], false, false⟩⟩],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "member", [], [[]], []⟩,
      ⟨2, "escape", [], [], []⟩, ⟨3, "other", [], [[]], []⟩], 0,
    #[⟨0, 17, "let"⟩], #[], #[⟨1, []⟩, ⟨1, [3]⟩]⟩

theorem overlappingTargets_validated : accepts overlappingTargets = true := by cbv

theorem overlappingTargets_execution :
    returnedObservation (eval 100 .release overlappingTargets) = some ([55, 10], []) := by cbv

def overlapReachable : ExecutionState :=
  Goose.Proofs.Exit.stepState (runModule 15 ⟨.release, overlappingTargets⟩ .initial)

def overlapExit : ExecutionStep Flow :=
  match overlapReachable.activations.head? with
  | some source => execStmt 100 ⟨.release, overlappingTargets⟩ source
      (.returnFrom 1 [.lit .i64 7] 0) overlapReachable
  | none => .stop (.fault .unbound) overlapReachable

def exitObservation : ExecutionStep α → Option (ExitAddress × List Carrier)
  | .escape address carriers _ => some (address, carriers)
  | _ => none

theorem overlappingTargets_live_stack :
    timeoutActivations (runModule 15 ⟨.release, overlappingTargets⟩ .initial) =
      some ([2, 1, 0], 3) := by cbv

theorem overlappingTargets_reachable_address :
    exitObservation overlapExit = some (⟨1, .nonlocal 1⟩, [.register (.int .i64 7)]) := by cbv

def inactiveTarget : Module := { overlappingTargets with
  impls := overlappingTargets.impls.mapIdx fun index implementation =>
    if index == 0 then { implementation with vars := #[], body := .mk 0 [.expr (.call 2 [] 0) 0] none }
    else implementation }

theorem inactiveTarget_rejected :
    validate inactiveTarget = .error ⟨.summary, "V-SUMMARY: missing required nonlocal target"⟩ := by cbv

def argumentReceivingRenewal : Module :=
  let integer : Ty := .int .i64
  let result : Ty := .varr integer
  let interrupted := Expr.arrLit result [.lit .i64 1,
    .ifE (.bool true) (.mk 4 [.brk 0] none) (.mk 5 [] (some (.lit .i64 2))) 0] 0
  let argument := Expr.ifE (.bool true)
    (.mk 2 [.while (.bool true) (.mk 3 [.breakValue interrupted 0] none) 0,
      .print [.text "argument finished"] 0] (some (.lit .i64 0)))
    (.mk 6 [] (some (.lit .i64 0))) 0
  let entry : Impl := ⟨"entry", #[], #[], #[⟨"result", result, .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.call 1 [] 0) 0, .print [.view (.of (.var 0))] 0] none, .unknown⟩
  let caller : Impl := ⟨"caller", #[], #[⟨result, .value, none⟩], #[],
    .mk 0 [] (some (.blockE (.mk 1 [] (some (.call 2 [.byVal argument] 0))) 0)), .unknown⟩
  let helper : Impl := ⟨"helper", #[⟨0, .byValue⟩], #[⟨result, .value, none⟩],
    #[⟨"parameter", integer, .immutable, 0, 0⟩],
    .mk 0 [.print [.text "helper entered"] 0] (some (.arrLit result [.lit .i64 9] 0)), .unknown⟩
  ⟨#["argument-receiving-renewal.goose"], #[integer, result], #[], #[entry, caller, helper],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "caller", [], [[]], []⟩, ⟨2, "helper", [], [[]], []⟩], 0,
    #[⟨0, 1, "call"⟩], #[], #[]⟩

theorem argumentReceivingRenewal_validated : validate argumentReceivingRenewal = .ok () := by cbv

theorem argumentReceivingRenewal_execution :
    returnedObservation (eval 100 .release argumentReceivingRenewal) =
      some ("argument finished\nhelper entered\n[9]\n".toUTF8.data.toList,
        [.begin 0, .write 0 0, .abandon 0, .begin 1, .write 1 0, .publish 1]) := by decide +kernel

theorem argumentReceivingRenewal_destinations :
    let state := Goose.Proofs.Exit.stepState (runModule 100 ⟨.release, argumentReceivingRenewal⟩ .initial)
    (state.construction.destinations[0]?.map PendingDestination.progress,
      state.construction.destinationResumptions.map Prod.fst,
      state.construction.destinations[1]?.map PendingDestination.progress) =
        (some .abandoned, [0], some (.published 1)) := by decide +kernel

private def carriedNamedInnerValues : Expr := .values [.bytes array [65] 0, .resultLocal 0 0]

private def carriedNamedOuterValues : Expr := .values [
  .ifE (.bool true) (.mk 2 [.breakValue carriedNamedInnerValues 0] none)
    (.mk 3 [] (some (.bytes array [67] 0))) 0,
  .resultLocal 0 0]

private def carriedNamedProducer : Impl := ⟨"producer", #[],
  #[⟨array, .value, none⟩, ⟨array, .value, some 0⟩],
  #[⟨"second", array, .immutable, 0, 0⟩],
  .mk 0 [.letS 0 (.bytes array [66] 0) 0]
    (some (.blockE (.mk 1 [.breakValue carriedNamedOuterValues 0] none) 0)), .unknown⟩

private def carriedNamedEntry : Impl := ⟨"entry", #[], #[],
  #[⟨"first", array, .immutable, 0, 0⟩, ⟨"second", array, .immutable, 0, 0⟩],
  .mk 0 [.receive [0, 1] (.call 1 [] 0) 0,
    .print [.view (.of (.var 0)), .view (.of (.var 1))] 0] none, .unknown⟩

def carriedNamedHandoff : Module := ⟨#["borrowed-rearm.goose"], #[.int .u8, array], #[], #[carriedNamedEntry, carriedNamedProducer],
  #[⟨0, "entry", [], [], []⟩, ⟨1, "producer", [], [[], []], []⟩], 0,
  #[⟨0, 1, "let"⟩], #[], #[]⟩

theorem carriedNamedHandoff_validated : validate carriedNamedHandoff = .ok () := by cbv

theorem carriedNamedHandoff_execution :
    returnedObservation (eval 200 .release carriedNamedHandoff) =
      some ([65, 66, 10], [.begin 0, .begin 1, .write 1 0, .write 0 0, .publish 0, .publish 1]) := by cbv

private def carriedNamedCallPrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) :
    EvalM (RuntimeActivation × List (Goose.Core.VarId × Value)) := do
  let (id, implementation) ← getImplementation config context
  if channels.length != implementation.results.size then fault .arity
  let callable ← (channels.zip implementation.results.toList).mapM fun (channel, result) => do
    match result.request, channel with
    | .register, _ => pure (Channel.register result.ty)
    | .value, .construct incoming | .elementRun, .construct incoming =>
        let destination ← liftConstruction 0 (renewReceivingDestination incoming)
        liftConstruction 0 (adaptDestinationType destination result.ty)
        pure (.construct destination)
    | .value, .register _ | .elementRun, .register _ => fault .shape
    | _, .completion _ => fault .flow
  let values ← evalArguments fuel config environment implementation.vars implementation.params.toList arguments
  let callable ← callable.mapM fun channel => match channel with
    | .register ty => pure (.register ty)
    | .construct destination => do pure (.construct (← liftConstruction 0 (renewReceivingDestination destination)))
    | .completion _ => fault .flow
  let state ← EvalM.get
  if state.activations.length ≥ Goose.Core.maxCallDepth then timeout
  let act ← freshAct
  let activation : RuntimeActivation := ⟨id, act, implementation.vars, [], callable⟩
  let state ← EvalM.get
  EvalM.set { state with activations := activation :: state.activations }
  pure (activation, (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value))

private def carriedNamedScopePrefix (environment : RuntimeActivation) (scope : Nat)
    (pre : List (Goose.Core.VarId × Value)) : EvalM RuntimeActivation := do
  let scopeInst ← freshScope
  let localEnvironment := { environment with scopes := (scope, scopeInst) :: environment.scopes }
  let state ← EvalM.get
  EvalM.set { state with activations := state.activations.map (fun current =>
    if current.act == environment.act then { current with scopes := localEnvironment.scopes } else current) }
  bindAll environment.act scopeInst pre
  pure localEnvironment

private def carriedNamedOuterPrefix : EvalM RuntimeActivation := do
  let config : EvalConfig := ⟨.release, carriedNamedHandoff⟩
  initGlobals 200 config []
  let (_, implementation) ← getImplementation config 0
  let rootChannels ← channelsFor config.layout 0 implementation.results.toList 0
  let (entryActivation, pre) ← carriedNamedCallPrefix 199 config ⟨0, 0, #[], [], []⟩ 0 [] rootChannels
  let entryEnvironment ← carriedNamedScopePrefix entryActivation 0 pre
  let channels ← ([0, 1] : List Nat).mapM fun _ => do
    pure (Channel.construct (← newDestination config.layout entryEnvironment.act array .value 0))
  let channels ← channels.mapM fun channel => match channel with
    | .construct incoming => do pure (Channel.construct (← liftConstruction 0 (renewReceivingDestination incoming)))
    | channel => pure channel
  let (activation, pre) ← carriedNamedCallPrefix 193 config entryEnvironment 1 [] channels
  let environment ← carriedNamedScopePrefix activation 0 pre
  let _ ← execStmts 191 config environment [.letS 0 (.bytes array [66] 0) 0]
  let planned ← activation.channels.mapM fun channel => match channel with
    | .construct incoming => do pure (Channel.completion (← liftConstruction 0 (waitExitDestination incoming)))
    | _ => fault .flow
  let state ← EvalM.get
  let target : BreakTarget := ⟨state.nextScope, environment.act, .block, planned⟩
  EvalM.set { state with nextScope := state.nextScope + 1, breaks := target :: state.breaks }
  carriedNamedScopePrefix environment 1 []

private def carriedNamedInnerPrefix (environment : RuntimeActivation) : EvalM RuntimeActivation := do
  let target ← currentBreak environment.act (some .block)
  let activation := { environment with channels := target.channels }
  let operands := match carriedNamedOuterValues with | .values operands => operands | _ => []
  let _ ← exitChannels environment activation operands 0
  carriedNamedScopePrefix environment 2 []

private def carriedNamedPhase (result : ExecutionStep α) : Option NamedReservationStage :=
  let reservation : Option ExitReservation := (Goose.Proofs.Exit.stepState result).construction.exitReservations[1]?
  match reservation with
  | some (.active (.named stage) _ _ _) => some stage
  | _ => none

private def carriedNamedInner : ExecutionStep Flow :=
  match carriedNamedOuterPrefix .initial with
  | .ok environment state =>
      match carriedNamedInnerPrefix environment state with
      | .ok inner ready => execStmt 180 ⟨.release, carriedNamedHandoff⟩ inner (.breakValue carriedNamedInnerValues 0) ready
      | _ => .stop (.fault .flow) state
  | _ => .stop (.fault .flow) .initial

private def carriedNamedOuter : ExecutionStep Flow :=
  match carriedNamedOuterPrefix .initial with
  | .ok environment state => execStmt 187 ⟨.release, carriedNamedHandoff⟩ environment (.breakValue carriedNamedOuterValues 0) state
  | _ => .stop (.fault .flow) .initial

private def carriedNamedJump (result : ExecutionStep Flow) : Option (Nat × List Carrier) :=
  match result with
  | .jump target (.breakValue carriers) _ => some (target, carriers)
  | _ => none

private def carriedNamedMaterialized : ExecutionStep (List Carrier) :=
  match carriedNamedOuter with
  | .jump _ (.breakValue carriers) state =>
      ((do
        landCarriersInto 0 [.completion 0, .completion 1] carriers
        materializeOwnedCarriers 0 [0, 1] carriers) : EvalM (List Carrier)) state
  | _ => .stop (.fault .flow) .initial

theorem carriedNamedHandoff_inner_ready :
    (carriedNamedJump carriedNamedInner, carriedNamedPhase carriedNamedInner) =
      (some (2, [.completed 0, .pendingNamed 1]), some .ready) := by cbv

theorem carriedNamedHandoff_outer_ready :
    (carriedNamedJump carriedNamedOuter, carriedNamedPhase carriedNamedOuter) =
      (some (2, [.completed 0, .pendingNamed 1]), some .ready) := by cbv

theorem carriedNamedHandoff_materialized :
    (match carriedNamedMaterialized with | .ok carriers _ => some carriers | _ => none,
      carriedNamedPhase carriedNamedMaterialized) =
        (some [.completed 0, .completed 1], some .materialized) := by cbv

private def unusedNamedMarkRearm (interruption : Stmt) : Module :=
  let integer : Ty := .int .i64
  let interrupted := Expr.ifE (.bool true) (.mk 3 [interruption] none)
    (.mk 4 [] (some (.lit .i64 0))) 0
  let producer : Impl := ⟨"producer", #[],
    #[⟨array, .value, some 0⟩, ⟨integer, .register, none⟩],
    #[⟨"named", array, .immutable, 0, 0⟩, ⟨"index", integer, .immutable, 2, 0⟩],
    .mk 0 [.letS 0 (.bytes array [66] 0) 0]
      (some (.blockE (.mk 1 [.forRange 1 (.lit .i64 0) (.lit .i64 1)
        (.mk 2 [.breakValue (.values [.resultLocal 0 0, interrupted]) 0] none) 0]
        (some (.values [.resultLocal 0 0, .lit .i64 7]))) 0)), .unknown⟩
  let entry : Impl := ⟨"entry", #[], #[],
    #[⟨"bytes", array, .immutable, 0, 0⟩, ⟨"number", integer, .immutable, 0, 0⟩],
    .mk 0 [.receive [0, 1] (.call 1 [] 0) 0,
      .print [.view (.of (.var 0)), .expr (.read (.var 1))] 0] none, .unknown⟩
  ⟨#["unused-named-mark-rearm.goose"], #[.int .u8, integer, array], #[], #[entry, producer],
    #[⟨0, "entry", [], [], []⟩, ⟨1, "producer", [], [[], []], []⟩], 0,
    #[⟨0, 1, "let"⟩], #[], #[]⟩

theorem unusedNamedMarkRearm_break_validated : validate (unusedNamedMarkRearm (.brk 0)) = .ok () := by cbv

theorem unusedNamedMarkRearm_continue_validated : validate (unusedNamedMarkRearm (.cont 0)) = .ok () := by cbv

theorem unusedNamedMarkRearm_break_execution :
    returnedObservation (eval 200 .release (unusedNamedMarkRearm (.brk 0))) =
      some ([66, 55, 10], [.begin 0, .write 0 0, .publish 0]) := by cbv

theorem unusedNamedMarkRearm_continue_execution :
    returnedObservation (eval 200 .release (unusedNamedMarkRearm (.cont 0))) =
      some ([66, 55, 10], [.begin 0, .write 0 0, .publish 0]) := by cbv

#print axioms unusedNamedMarkRearm_break_validated
#print axioms unusedNamedMarkRearm_continue_validated
#print axioms unusedNamedMarkRearm_break_execution
#print axioms unusedNamedMarkRearm_continue_execution

#print axioms carriedNamedHandoff_validated
#print axioms carriedNamedHandoff_execution
#print axioms carriedNamedHandoff_inner_ready
#print axioms carriedNamedHandoff_outer_ready
#print axioms carriedNamedHandoff_materialized

#print axioms argumentReceivingRenewal_validated
#print axioms argumentReceivingRenewal_execution
#print axioms argumentReceivingRenewal_destinations

#print axioms recursiveDestinations_validated
#print axioms recursiveDestinations_execution
#print axioms recursive_live_activations
#print axioms recursive_live_activations_fresh
#print axioms recursive_live_nearest_target
#print axioms overlappingTargets_validated
#print axioms overlappingTargets_execution
#print axioms overlappingTargets_live_stack
#print axioms overlappingTargets_reachable_address
#print axioms inactiveTarget_rejected
#print axioms Goose.Proofs.ExitExecution.preservesFresh_copyValue
#print axioms Goose.Proofs.ExitExecution.preservesFresh_deliverCarriers
#print axioms Goose.Proofs.ExitExecution.preservesFresh_truncateOwner
#print axioms Goose.Proofs.ExitExecution.preservesFresh_appendFixedValues
#print axioms Goose.Proofs.ExitExecution.preservesFresh_appendRun
#print axioms Goose.Proofs.ExitExecution.evaluation_preservesFresh
#print axioms Goose.Proofs.ExitExecution.initGlobals_preservesFresh
#print axioms Goose.Proofs.ExitExecution.runModule_freshActivations
#print axioms Goose.Proofs.ExitExecution.targetActivation_selects_nearest
#print axioms Goose.Proofs.ExitExecution.runModule_selectedTarget_nearest

end Goose.Proofs.ExitExecutionChecks
