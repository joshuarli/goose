import Goose.Proofs.ConstructionGhostCallActivation

namespace Goose.Proofs.ConstructionGhostCallSetup
open Goose.Construct Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostCallActivation

def terminalCall {α : Type} : ExecutionStep α → Option (ExecutionStep (List Carrier))
  | .ok _ _ => none
  | .stop reason state => some (.stop reason state)
  | .escape address carriers state => some (.escape address carriers state)
  | .jump target kind state => some (.jump target kind state)

theorem invokeCall_lookupTerminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (before : ExecutionState) (terminal : ExecutionStep (List Carrier))
    (lookup : terminalCall (getImplementation config context before) = some terminal) :
    invokeCall (fuel + 1) config environment context arguments channels origin before = terminal := by
  cases result : getImplementation config context before <;> simp_all [terminalCall, invokeCall, bind]

theorem invokeCall_arityFault (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (before lookupReady : ExecutionState) (id : Goose.Core.ImplId) (implementation : Impl)
    (lookup : getImplementation config context before = .ok (id, implementation) lookupReady)
    (arity : channels.length ≠ implementation.results.size) :
    invokeCall (fuel + 1) config environment context arguments channels origin before = .stop (.fault .arity) lookupReady := by
  simp [invokeCall, bind, lookup, arity, fault, EvalM.stop]

theorem invokeCall_preparationTerminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (before lookupReady : ExecutionState) (id : Goose.Core.ImplId) (implementation : Impl)
    (terminal : ExecutionStep (List Carrier))
    (lookup : getImplementation config context before = .ok (id, implementation) lookupReady)
    (arity : channels.length = implementation.results.size)
    (prepared : terminalCall (prepareCallableChannels environment channels implementation origin lookupReady) = some terminal) :
    invokeCall (fuel + 1) config environment context arguments channels origin before = terminal := by
  simp only [invokeCall, bind, lookup, arity, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  change (prepareCallableChannels environment channels implementation origin >>= fun selected =>
    evalArguments fuel config environment implementation.vars implementation.params.toList arguments >>= fun values =>
      callAfterArguments fuel config id implementation channels selected origin values) lookupReady = _
  cases result : prepareCallableChannels environment channels implementation origin lookupReady <;>
    simp_all [terminalCall, bind]

theorem invokeCall_argumentsTerminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (before lookupReady argumentsReady : ExecutionState) (id : Goose.Core.ImplId) (implementation : Impl)
    (callableChannels : List Channel) (terminal : ExecutionStep (List Carrier))
    (lookup : getImplementation config context before = .ok (id, implementation) lookupReady)
    (arity : channels.length = implementation.results.size)
    (prepared : prepareCallableChannels environment channels implementation origin lookupReady = .ok callableChannels argumentsReady)
    (result : terminalCall (evalArguments fuel config environment implementation.vars implementation.params.toList arguments argumentsReady) = some terminal) :
    invokeCall (fuel + 1) config environment context arguments channels origin before = terminal := by
  obtain ⟨outcome, visits, replay, ordered, once, execution⟩ :=
    invokeCall_argumentReplay fuel config environment context arguments channels origin before lookupReady argumentsReady id implementation
      callableChannels lookup arity prepared
  rw [execution]
  rw [replay.sound] at result
  cases outcome <;> simp_all [terminalCall, callArgumentsContinuation]

theorem callAfterArguments_refreshTerminal (fuel : Nat) (config : EvalConfig) (id : Goose.Core.ImplId)
    (implementation : Impl) (channels callableChannels : List Channel) (origin : Goose.Core.OriginId)
    (values : List Value) (before : ExecutionState) (terminal : ExecutionStep (List Carrier))
    (refresh : terminalCall (refreshCallableChannels callableChannels origin before) = some terminal) :
    callAfterArguments fuel config id implementation channels callableChannels origin values before = terminal := by
  change (refreshCallableChannels callableChannels origin >>= fun selected => do
    let state ← EvalM.get
    if state.activations.length ≥ Goose.Core.maxCallDepth then timeout
    let act ← freshAct
    let activation : RuntimeActivation := ⟨id, act, implementation.vars, [], selected⟩
    let state ← EvalM.get
    EvalM.set { state with activations := activation :: state.activations }
    let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
    let carriers ← enterActivation fuel config activation pre implementation.body origin
    deliverCarriers fuel config.layout channels carriers origin) before = _
  cases result : refreshCallableChannels callableChannels origin before <;> simp_all [terminalCall, bind]

theorem callAfterArguments_depthTerminal (fuel : Nat) (config : EvalConfig) (id : Goose.Core.ImplId)
    (implementation : Impl) (channels callableChannels refreshed : List Channel) (origin : Goose.Core.OriginId)
    (values : List Value) (before ready : ExecutionState)
    (refresh : refreshCallableChannels callableChannels origin before = .ok refreshed ready)
    (depth : Goose.Core.maxCallDepth ≤ ready.activations.length) :
    callAfterArguments fuel config id implementation channels callableChannels origin values before = .stop .timeout ready := by
  change (refreshCallableChannels callableChannels origin >>= fun selected => do
    let state ← EvalM.get
    if state.activations.length ≥ Goose.Core.maxCallDepth then timeout
    let act ← freshAct
    let activation : RuntimeActivation := ⟨id, act, implementation.vars, [], selected⟩
    let state ← EvalM.get
    EvalM.set { state with activations := activation :: state.activations }
    let pre := (implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value)
    let carriers ← enterActivation fuel config activation pre implementation.body origin
    deliverCarriers fuel config.layout channels carriers origin) before = _
  simp [bind, refresh, EvalM.get, depth, timeout, EvalM.stop]

theorem callAfterArguments_classification (fuel : Nat) (config : EvalConfig) (id : Goose.Core.ImplId)
    (implementation : Impl) (channels callableChannels : List Channel) (origin : Goose.Core.OriginId)
    (values : List Value) (before : ExecutionState) :
    (∃ terminal, terminalCall (refreshCallableChannels callableChannels origin before) = some terminal ∧
      callAfterArguments fuel config id implementation channels callableChannels origin values before = terminal) ∨
    (∃ refreshed ready, refreshCallableChannels callableChannels origin before = .ok refreshed ready ∧
      Goose.Core.maxCallDepth ≤ ready.activations.length ∧
      callAfterArguments fuel config id implementation channels callableChannels origin values before = .stop .timeout ready) ∨
    (∃ refreshed ready, refreshCallableChannels callableChannels origin before = .ok refreshed ready ∧
      ready.activations.length < Goose.Core.maxCallDepth ∧
      let activation : RuntimeActivation := ⟨id, ready.nextAct, implementation.vars, [], refreshed⟩
      let activated := { ready with nextAct := ready.nextAct + 1, activations := activation :: ready.activations }
      callAfterArguments fuel config id implementation channels callableChannels origin values before =
        (enterActivation fuel config activation
          ((implementation.params.toList.zip values).map fun (parameter, value) => (parameter.var, value))
          implementation.body origin >>= fun carriers => deliverCarriers fuel config.layout channels carriers origin) activated) := by
  cases refresh : refreshCallableChannels callableChannels origin before with
  | ok refreshed ready =>
      by_cases depth : ready.activations.length < Goose.Core.maxCallDepth
      · exact Or.inr (Or.inr ⟨refreshed, ready, rfl, depth,
          callAfterArguments_activation fuel config id implementation channels callableChannels refreshed origin values before ready refresh depth⟩)
      · have maxDepth := Nat.le_of_not_gt depth
        exact Or.inr (Or.inl ⟨refreshed, ready, rfl, maxDepth,
          callAfterArguments_depthTerminal fuel config id implementation channels callableChannels refreshed origin values before ready refresh maxDepth⟩)
  | stop reason state =>
      exact Or.inl ⟨.stop reason state, by simp [refresh, terminalCall],
        callAfterArguments_refreshTerminal fuel config id implementation channels callableChannels origin values before _ (by simp [refresh, terminalCall])⟩
  | escape address carriers state =>
      exact Or.inl ⟨.escape address carriers state, by simp [refresh, terminalCall],
        callAfterArguments_refreshTerminal fuel config id implementation channels callableChannels origin values before _ (by simp [refresh, terminalCall])⟩
  | jump target kind state =>
      exact Or.inl ⟨.jump target kind state, by simp [refresh, terminalCall],
        callAfterArguments_refreshTerminal fuel config id implementation channels callableChannels origin values before _ (by simp [refresh, terminalCall])⟩

#print axioms callAfterArguments_classification
#print axioms invokeCall_argumentsTerminal
#print axioms callAfterArguments_refreshTerminal
#print axioms callAfterArguments_depthTerminal
#print axioms invokeCall_lookupTerminal
#print axioms invokeCall_arityFault
#print axioms invokeCall_preparationTerminal
end Goose.Proofs.ConstructionGhostCallSetup
