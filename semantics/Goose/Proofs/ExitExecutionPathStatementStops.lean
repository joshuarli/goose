import Goose.Proofs.ExitExecutionInvocationStatementsReplay
import Goose.Proofs.ExitExecutionInvocationStatementsGlobalReplay
import Goose.Proofs.ExitExecutionPathExitChannelsUnwind

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem statementStop_bind_assoc (action : EvalM α) (next : α → EvalM β)
    (last : β → EvalM γ) :
    ((action >>= next) >>= last) = (action >>= fun value => next value >>= last) := by
  funext state
  cases evaluated : action state <;> simp only [bind, evaluated]

private theorem statementGlobalValuePrefix_build_stop (fuel : Nat) (config : EvalConfig)
    (global : Goose.Core.GlobalId) (initial prepared allocated : ExecutionState)
    (descriptor : Global) (environment : RuntimeActivation) (destination : Nat)
    (setup : statementInvocation_globalEnvironmentPrefix config global initial =
      .ok (descriptor, environment) prepared)
    (nonfixed : descriptor.ty.nonfixed = true)
    (materialize : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ descriptor.init = none)
    (allocation : newDestination (LayoutEnv.ofModule config.module) environment.act descriptor.ty
      .value descriptor.org none (producerCount? ⟨config.module, environment.vars⟩ descriptor.init) prepared =
      .ok destination allocated)
    (stopped : buildExpr fuel config environment destination descriptor.init allocated = .stop reason before) :
    statementInvocation_globalValuePrefix fuel config global initial = .stop reason before := by
  unfold statementInvocation_globalValuePrefix
  rw [statementInvocation_bind_step, setup]
  simp [nonfixed, materializeProducer, materialize, allocation, constructLocal, bind, pure, stopped]

private theorem statementGlobalValuePrefix_materialize_stop (fuel : Nat) (config : EvalConfig)
    (global : Goose.Core.GlobalId) (initial prepared : ExecutionState) (descriptor : Global)
    (environment : RuntimeActivation) (count : Nat)
    (setup : statementInvocation_globalEnvironmentPrefix config global initial =
      .ok (descriptor, environment) prepared)
    (nonfixed : descriptor.ty.nonfixed = true)
    (materialize : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ descriptor.init = some count)
    (stopped : evalValue fuel config environment descriptor.init prepared = .stop reason before) :
    statementInvocation_globalValuePrefix fuel config global initial = .stop reason before := by
  unfold statementInvocation_globalValuePrefix
  rw [statementInvocation_bind_step, setup]
  simp [nonfixed, materializeProducer, materialize, bind, stopped]

private theorem statementGlobalValuePrefix_fixed_stop (fuel : Nat) (config : EvalConfig)
    (global : Goose.Core.GlobalId) (initial prepared : ExecutionState) (descriptor : Global)
    (environment : RuntimeActivation)
    (setup : statementInvocation_globalEnvironmentPrefix config global initial =
      .ok (descriptor, environment) prepared)
    (fixed : descriptor.ty.nonfixed = false)
    (stopped : evalValue fuel config environment descriptor.init prepared = .stop reason before) :
    statementInvocation_globalValuePrefix fuel config global initial = .stop reason before := by
  unfold statementInvocation_globalValuePrefix
  rw [statementInvocation_bind_step, setup]
  simp [fixed, stopped]

private theorem statementGlobalPrefix_stop (fuel : Nat) (config : EvalConfig)
    (global : Goose.Core.GlobalId) (globals : List Goose.Core.GlobalId) (initial : ExecutionState)
    (reason : Goose.Core.Stop) (before : ExecutionState)
    (stopped : statementInvocation_globalValuePrefix fuel config global initial = .stop reason before) :
    initGlobals fuel config (global :: globals) initial = .stop reason before := by
  rw [statementGlobal_next_action]
  simp only [bind, stopped]

private theorem statementGlobalNext_stop (fuel : Nat) (config : EvalConfig)
    (global : Goose.Core.GlobalId) (globals : List Goose.Core.GlobalId) (initial prepared : ExecutionState)
    (setup : ((do
      let value ← statementInvocation_globalValuePrefix fuel config global
      bindRoot (.global global) value) : EvalM Unit) initial = .ok () prepared)
    (reason : Goose.Core.Stop) (before : ExecutionState)
    (stopped : initGlobals fuel config globals prepared = .stop reason before) :
    initGlobals fuel config (global :: globals) initial = .stop reason before := by
  rw [statementGlobal_next_action, ← statementStop_bind_assoc,
    statementInvocation_bind_step, setup]
  dsimp only []
  exact stopped

private theorem statementOwner_bind_assoc (action : EvalM α) (next : α → EvalM β)
    (last : β → EvalM γ) :
    ((action >>= next) >>= last) = (action >>= fun value => next value >>= last) := by
  funext state
  cases evaluated : action state <;> simp only [bind, evaluated]

private theorem statementOwner_bind_pure (value : α) (next : α → EvalM β) :
    ((pure value : EvalM α) >>= next) = next value := rfl

private def statementOwnerGuard (snapshot : Option PendingDestination) (destination : Nat)
    (action : EvalM α) : EvalM α := fun state =>
  let finish := fun (carriers : List Carrier) (result : ExecutionState → ExecutionStep α)
      (state' : ExecutionState) =>
    match snapshot with
    | none => result state'
    | some parent =>
        match restoreCompletedOwner parent destination
            (carriers.filterMap fun carrier => match carrier with | .completed id => some id | _ => none)
            state' with
        | .ok () final => result final
        | .stop reason final => .stop reason final
        | .escape target carriers final => .escape target carriers final
        | .jump target kind final => .jump target kind final
  match action state with
  | .escape target carriers state' => finish carriers (.escape target carriers) state'
  | .jump target kind state' =>
      finish (match kind with | .breakValue carriers => carriers | .continueLoop => [])
        (.jump target kind) state'
  | result => result

private theorem statementOwnerExtension_action (stored : StoredValue) (allocate : EvalM Nat)
    (action : Nat → EvalM α) :
    withOwnerExtension stored allocate action = ((do
      let snapshot ← ((match stored.destination with
        | none => pure none
        | some id => do
            let parent ← getDestination id
            pure (match parent.progress with | .built _ => some parent | _ => none)) :
          EvalM (Option PendingDestination))
      let destination ← allocate
      statementOwnerGuard snapshot destination (action destination)) : EvalM α) := by
  unfold withOwnerExtension statementOwnerGuard
  cases stored.destination <;> simp only [statementOwner_bind_assoc, statementOwner_bind_pure]
  all_goals rfl

private theorem statementOwner_bind_ok (action : EvalM α) (next : α → EvalM β)
    (initial prepared : ExecutionState) (value : α)
    (selected : action initial = .ok value prepared) :
    (action >>= next) initial = next value prepared := by
  simp only [bind, selected]

private theorem statementWithOwnerExtension_stop (stored : StoredValue) (allocate : EvalM Nat)
    (action : Nat → EvalM α) (initial sampled prepared : ExecutionState)
    (snapshot : Option PendingDestination) (destination : Nat)
    (snapshotPrefix : StatementOwnerSnapshot stored initial snapshot sampled)
    (allocation : allocate sampled = .ok destination prepared)
    (reason : Goose.Core.Stop) (before : ExecutionState)
    (stopped : action destination prepared = .stop reason before) :
    withOwnerExtension stored allocate action initial = .stop reason before := by
  cases snapshotPrefix
  rename_i snapshotSelected
  rw [statementOwnerExtension_action]
  refine Eq.trans (b := (allocate >>= fun destination =>
      statementOwnerGuard snapshot destination (action destination)) sampled) ?_ ?_
  · exact statementOwner_bind_ok _ _ _ _ _ snapshotSelected
  · rw [statementInvocation_bind_step, allocation]
    simp only [statementOwnerGuard, stopped]

private theorem statementPushBuild_stop (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (owner : Place) (expression : Expr)
    (origin : Goose.Core.OriginId) (initial prepared : ExecutionState)
    (destination : Nat) (snapshot : Option PendingDestination)
    (setup : StatementPushBuildPrefix fuel config environment owner expression origin
      initial snapshot destination prepared)
    (reason : Goose.Core.Stop) (before : ExecutionState)
    (stopped : buildExpr fuel config environment destination expression prepared =
      .stop reason before) :
    Goose.Construct.pushValue (fuel + 1) config environment owner expression origin initial =
      .stop reason before := by
  cases setup with
  | actual located read sampled snapshotted prepared location stored bytes run snapshot destination
      placeSelected storedSelected runSelected nonfixed snapshotSelected allocation =>
    have actionStopped : ((do
        buildExpr fuel config environment destination expression
        publishElementReceiving fuel config.layout location stored
          (← completedReceivingDestination destination) origin) : EvalM Unit) prepared =
        .stop reason before := by
      simp only [statementInvocation_bind_step, stopped]
    have wrapperStopped := statementWithOwnerExtension_stop stored _ (fun destination => do
        buildExpr fuel config environment destination expression
        publishElementReceiving fuel config.layout location stored
          (← completedReceivingDestination destination) origin) sampled snapshotted prepared
      snapshot destination snapshotSelected allocation reason before actionStopped
    rw [Goose.Construct.pushValue, statementInvocation_bind_step, placeSelected]
    dsimp only []
    rw [statementInvocation_bind_step, storedSelected]
    dsimp only []
    rw [statementInvocation_bind_step, runSelected]
    dsimp only []
    simp only [nonfixed, ite_true]
    rw [statementInvocation_bind_step, wrapperStopped]

private theorem statementWhileNext_stop (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (condition : Expr) (body : Block)
    (initial checked prepared : ExecutionState) (flow : Flow)
    (conditionTrue : ((do expectBool (← evalValue fuel config environment condition)) : EvalM Bool)
      initial = .ok true checked)
    (bodyDone : loopBody fuel config environment [] body checked = .ok flow prepared)
    (continues : (∃ value, flow = .normal value) ∨ flow = .continuing)
    (reason : Goose.Core.Stop) (before : ExecutionState)
    (stopped : execWhile fuel config environment condition body prepared = .stop reason before) :
    execWhile (fuel + 1) config environment condition body initial = .stop reason before := by
  rw [Goose.Construct.execWhile]
  rw [← statementStop_bind_assoc]
  rw [statementInvocation_bind_step]
  rw [conditionTrue]
  simp only [ite_eq_left]
  rcases continues with ⟨value, flowEq⟩ | flowEq
  · rw [statementInvocation_bind_step]
    rw [bodyDone]
    rw [flowEq]
    exact stopped
  · rw [statementInvocation_bind_step]
    rw [bodyDone]
    rw [flowEq]
    exact stopped

private theorem statementStop_bind_step (action : EvalM α) (next : α → EvalM β) (state : ExecutionState) :
    (action >>= next) state = match action state with
      | .ok value after => next value after
      | .stop reason after => .stop reason after
      | .escape address carriers after => .escape address carriers after
      | .jump target kind after => .jump target kind after := rfl

private theorem statementStop_bind_pure (value : α) (next : α → EvalM β) :
    ((pure value : EvalM α) >>= next) = next value := rfl

private theorem statementLetBuild_stop (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (initial prepared : ExecutionState) (destination : Nat)
    (setup : StatementLetBuildPrefix fuel config environment localVar expression origin initial destination prepared)
    (reason : Goose.Core.Stop) (before : ExecutionState)
    (stopped : buildExpr fuel config environment destination expression prepared = .stop reason before) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) initial = .stop reason before := by
  cases setup with
  | actual selected materialized allocated prepared descriptor root named destination namedPrefix materialization allocation preparation =>
      cases namedPrefix with
      | absent selected descriptor root implementation lookup nonfixed rootSelected implementationLookup candidate =>
          simp only [Option.isNone, ↓reduceIte] at materialization
          simp only [execStmt, lookup]
          rw [statementStop_bind_step, rootSelected]
          dsimp only []
          simp only [nonfixed, implementationLookup, candidate]
          simp only [ite_true, statementStop_bind_pure, Option.isSome, Option.isNone, Bool.false_eq_true, ite_false]
          rw [statementStop_bind_step, materialization]
          dsimp only []
          simp only [Option.map_none]
          change newDestination config.layout environment.act descriptor.ty .value origin none
            (producerCount? ⟨config.module, environment.vars⟩ expression) materialized = .ok destination allocated at allocation
          have nativeAllocation : newDestination config.layout environment.act descriptor.ty .value origin none
              (none <|> producerCount? ⟨config.module, environment.vars⟩ expression) materialized = .ok destination allocated := allocation
          rw [statementStop_bind_step, nativeAllocation]
          dsimp only []
          have same : allocated = prepared := by simpa only [Option.isSome, Bool.false_eq_true, ite_false, pure, ExecutionStep.ok.injEq, true_and] using preparation
          subst allocated
          rw [statementStop_bind_step, stopped]
      | receiving rooted renewed selected descriptor root implementation result index incoming renewedDestination receiving lookup nonfixed rootSelected implementationLookup candidate channel renewal selection request =>
          simp only [execStmt, lookup]
          rw [statementStop_bind_step, rootSelected]
          dsimp only []
          simp only [nonfixed, implementationLookup, candidate, channel, ite_true]
          rw [statementStop_bind_step, renewal]
          dsimp only []
          rw [statementStop_bind_step, selection]
          dsimp only []
          simp only [request, ite_true, statementStop_bind_pure, Option.isSome, Option.isNone, Bool.false_eq_true, ite_false]
          have sameMaterialized : selected = materialized := by
            simpa only [Option.isNone, Bool.false_eq_true, ite_false, pure, ExecutionStep.ok.injEq, true_and] using materialization
          subst materialized
          simp only [channel] at allocation ⊢
          rw [statementStop_bind_step, allocation]
          dsimp only []
          simp only [Option.isSome, ite_true] at preparation
          rw [statementStop_bind_step, preparation]
          dsimp only []
          rw [statementStop_bind_step, stopped]
      | other rooted renewed selected descriptor root implementation result index incoming renewedDestination receiving lookup nonfixed rootSelected implementationLookup candidate channel renewal selection request =>
          simp only [Option.isNone, ↓reduceIte] at materialization
          simp only [execStmt, lookup]
          rw [statementStop_bind_step, rootSelected]
          dsimp only []
          simp only [nonfixed, implementationLookup, candidate, channel, ite_true]
          rw [statementStop_bind_step, renewal]
          dsimp only []
          rw [statementStop_bind_step, selection]
          dsimp only []
          simp only [request, ite_true, statementStop_bind_pure, Option.isSome, Option.isNone, Bool.false_eq_true, ite_false]
          rw [statementStop_bind_step, materialization]
          dsimp only []
          simp only [Option.map_none]
          change newDestination config.layout environment.act descriptor.ty .value origin none
            (producerCount? ⟨config.module, environment.vars⟩ expression) materialized = .ok destination allocated at allocation
          have nativeAllocation : newDestination config.layout environment.act descriptor.ty .value origin none
              (none <|> producerCount? ⟨config.module, environment.vars⟩ expression) materialized = .ok destination allocated := allocation
          rw [statementStop_bind_step, nativeAllocation]
          dsimp only []
          have same : allocated = prepared := by simpa only [Option.isSome, Bool.false_eq_true, ite_false, pure, ExecutionStep.ok.injEq, true_and] using preparation
          subst allocated
          rw [statementStop_bind_step, stopped]

private theorem statementPrintArgument_stop (config : EvalConfig) (fuel : Nat)
    (environment : RuntimeActivation) (earlier after : List PrintArg) (argument : PrintArg)
    (origin : Goose.Core.OriginId) (initial prepared : ExecutionState) (parts : List ByteArray)
    (printed : earlier.mapM (evalPrintArg fuel config environment) initial = .ok parts prepared)
    (reason : Goose.Core.Stop) (before : ExecutionState)
    (stopped : evalPrintArg fuel config environment argument prepared = .stop reason before) :
    execStmt (fuel + 1) config environment (.print (earlier ++ argument :: after) origin) initial =
      .stop reason before := by
  simp [execStmt, List.mapM_append, List.mapM_cons, bind, printed, stopped]

theorem StatementInvocationEdge.stop_after_child {config : EvalConfig}
    {α β : Type} {parent : ExitInvocation α} {child : ExitInvocation β}
    {parentInitial childPrepared before : ExecutionState} {reason : Goose.Core.Stop}
    (edge : StatementInvocationEdge config parent parentInitial child childPrepared)
    (stopped : child.action config childPrepared = .stop reason before) :
    ∃ finalReason final changes,
      parent.action config parentInitial = .stop finalReason final ∧
      final.construction.stdout = before.construction.stdout ∧
      final.objects = before.objects ∧
      CleanupStorageTrace changes before.construction.storage final.construction.storage := by
  cases edge
  case ifCondition fuel environment condition yes no origin =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    cases no <;> simp [execStmt, bind, stopped]
  case ifYes fuel environment condition yes no origin conditionTrue =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    cases no
    all_goals rw [execStmt, ← statementStop_bind_assoc, statementInvocation_bind_step, conditionTrue]
    all_goals exact stopped
  case loopBlock fuel environment pre body =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, { before with breaks := before.breaks.filter (fun entry => entry.id != parentInitial.nextScope) },
      [], ?_, rfl, rfl, .refl _⟩
    simp [loopBody, withBreakTarget, mapStepState, stopped]
  case globalNext fuel global globals setup =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    exact statementGlobalNext_stop fuel config global globals parentInitial childPrepared setup reason before stopped
  case globalMaterialize fuel global globals descriptor environment count nonfixed materialize setup =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    have prefixStopped := statementGlobalValuePrefix_materialize_stop fuel config global parentInitial
      childPrepared descriptor environment count setup nonfixed materialize stopped
    exact statementGlobalPrefix_stop fuel config global globals parentInitial reason before prefixStopped
  case globalBuild fuel global globals prepared descriptor environment destination nonfixed materialize setup allocation =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    have prefixStopped := statementGlobalValuePrefix_build_stop fuel config global parentInitial
      prepared childPrepared descriptor environment destination setup nonfixed materialize allocation stopped
    exact statementGlobalPrefix_stop fuel config global globals parentInitial reason before prefixStopped
  case globalValue fuel global globals descriptor environment setup fixed =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    have prefixStopped := statementGlobalValuePrefix_fixed_stop fuel config global parentInitial childPrepared
      descriptor environment fixed setup stopped
    exact statementGlobalPrefix_stop fuel config global globals parentInitial reason before prefixStopped
  case pushValue fuel environment owner expression origin setup =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    cases setup with
    | actual =>
        unfold Goose.Construct.pushValue
        simp_all [bind]
  case pushBuild fuel environment owner expression origin destination snapshot setup =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    exact statementPushBuild_stop fuel config environment owner expression origin parentInitial
      childPrepared destination snapshot setup reason before stopped
  case letBuild fuel environment localVar expression origin destination setup =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    exact statementLetBuild_stop fuel config environment localVar expression origin parentInitial childPrepared
      destination setup reason before stopped
  case printArgument fuel environment earlier after argument origin parts printed =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    exact statementPrintArgument_stop config fuel environment earlier after argument origin
      parentInitial childPrepared parts printed reason before stopped
  case pushPlace fuel environment owner expression origin =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    unfold Goose.Construct.pushValue
    simp [bind, stopped]
  case eachNext =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    statement_prepare_prefixes
    statement_execute
    all_goals simp_all
  case eachBody =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    statement_prepare_prefixes
    statement_execute
  case rangeNext =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    statement_execute
    all_goals simp_all
  case rangeBody fuel environment localVar ty first last body within =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    rw [Goose.Construct.execRange]
    rw [ite_eq_left within]
    simp only [bind, stopped]
  case whileBody =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    statement_prepare_prefixes
    statement_execute
  case whileNext fuel environment condition body checked flow continues conditionTrue bodyDone =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    exact statementWhileNext_stop fuel config environment condition body parentInitial
      checked childPrepared flow conditionTrue bodyDone continues reason before stopped
  case whileCondition fuel environment condition body =>
    simp only [ExitInvocation.action] at stopped ⊢
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    simp [Goose.Construct.execWhile, stopped, bind]
  all_goals
    refine ⟨reason, before, [], ?_, rfl, rfl, .refl _⟩
    simp only [ExitInvocation.action] at stopped ⊢
    statement_prepare_prefixes
    statement_execute

#print axioms StatementInvocationEdge.stop_after_child

end Goose.Proofs.ExitExecution
