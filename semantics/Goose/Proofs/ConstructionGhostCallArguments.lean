import Goose.Proofs.ConstructionGhostArguments

namespace Goose.Proofs.ConstructionGhostCallArguments
open Goose.Construct Goose.Proofs.ConstructionGhostArguments

def prepareCallableChannels (environment : RuntimeActivation) (channels : List Channel)
    (implementation : Impl) (origin : Goose.Core.OriginId) : EvalM (List Channel) :=
  (channels.zip implementation.results.toList).mapM fun (channel, result) => do
    match result.request, channel with
    | .register, _ => pure (Channel.register result.ty)
    | .value, .construct incoming | .elementRun, .construct incoming =>
        let destination ← liftConstruction origin (renewReceivingDestination incoming)
        liftConstruction origin (adaptDestinationType destination result.ty)
        pure (.construct destination)
    | .value, .register _ | .elementRun, .register _ => fault .shape
    | _, .completion _ => fault .flow

def callAfterArguments (fuel : Nat) (config : EvalConfig) (id : Goose.Core.ImplId) (implementation : Impl)
    (channels callableChannels : List Channel) (origin : Goose.Core.OriginId) (values : List Value) : EvalM (List Carrier) := do
  let callableChannels ← callableChannels.mapM fun channel => match channel with
    | .register ty => pure (.register ty)
    | .construct destination => do
        pure (.construct (← liftConstruction origin (renewReceivingDestination destination)))
    | .completion _ => fault .flow
  let state ← EvalM.get
  if state.activations.length ≥ Goose.Core.maxCallDepth then timeout
  let act ← freshAct
  let activation : RuntimeActivation := ⟨id, act, implementation.vars, [], callableChannels⟩
  let state ← EvalM.get
  EvalM.set { state with activations := activation :: state.activations }
  let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
  let carriers ← enterActivation fuel config activation pre implementation.body origin
  deliverCarriers fuel config.layout channels carriers origin

def callArgumentsContinuation (fuel : Nat) (config : EvalConfig) (id : Goose.Core.ImplId) (implementation : Impl)
    (channels callableChannels : List Channel) (origin : Goose.Core.OriginId)
    (result : ExecutionStep (List Value)) : ExecutionStep (List Carrier) :=
  match result with
  | .ok values state => callAfterArguments fuel config id implementation channels callableChannels origin values state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem invokeCall_argumentReplay (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (before lookupReady argumentsReady : ExecutionState) (id : Goose.Core.ImplId) (implementation : Impl)
    (callableChannels : List Channel)
    (lookup : getImplementation config context before = .ok (id, implementation) lookupReady)
    (arity : channels.length = implementation.results.size)
    (prepared : prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady) :
    ∃ outcome visits,
      ArgumentReplay config environment implementation.vars fuel 0 implementation.params.toList arguments argumentsReady outcome visits ∧
      visits.map ArgumentInvocation.argument = arguments.take visits.length ∧
      (visits.map ArgumentInvocation.ordinal).Nodup ∧
      invokeCall (fuel + 1) config environment context arguments channels origin before =
        callArgumentsContinuation fuel config id implementation channels callableChannels origin outcome := by
  obtain ⟨visits, replay⟩ := argumentReplay_exists fuel config environment implementation.vars 0
    implementation.params.toList arguments argumentsReady
  refine ⟨_, visits, replay, replay.sourceOrder, replay.once, ?_⟩
  simp only [invokeCall, bind, lookup, arity, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  change (prepareCallableChannels environment channels implementation origin >>= fun selected =>
    evalArguments fuel config environment implementation.vars implementation.params.toList arguments >>= fun values =>
      callAfterArguments fuel config id implementation channels selected origin values) lookupReady = _
  simp only [bind, prepared, callArgumentsContinuation, callAfterArguments]
  cases evalArguments fuel config environment implementation.vars implementation.params.toList arguments argumentsReady <;> rfl

private def witnessModule : Module :=
  ⟨#[], #[], #[], #[⟨"callee", #[⟨0, .byValue⟩], #[], #[⟨"x", .int .i64, .immutable, 0, 0⟩],
    .mk 0 [.print [.text "callee"] 0] none, .unknown⟩], #[⟨0, "callee", [], [], []⟩], 0, #[], #[], #[]⟩
private def witnessConfig : EvalConfig := ⟨.release, witnessModule⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 4, #[], [], []⟩
private def witnessArguments : List Arg :=
  [.byVal (.blockE (.mk 1 [.print [.text "arg"] 0] (some (.lit .i64 7))) 0)]
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem callWitness_sideEffect :
    ∃ state, invokeCall 60 witnessConfig witnessEnvironment 0 witnessArguments [] 0 .initial =
      .ok [] state ∧ state.construction.stdout.data.toList = [97, 114, 103, 10, 99, 97, 108, 108, 101, 101, 10] := by
  refine ⟨stepState (invokeCall 60 witnessConfig witnessEnvironment 0 witnessArguments [] 0 .initial), ?_, ?_⟩ <;>
    unfold witnessConfig witnessModule witnessEnvironment witnessArguments stepState <;> cbv

#print axioms callWitness_sideEffect
#print axioms invokeCall_argumentReplay
end Goose.Proofs.ConstructionGhostCallArguments
