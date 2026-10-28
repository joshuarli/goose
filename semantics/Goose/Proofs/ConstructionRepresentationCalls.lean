import Goose.Proofs.ConstructionRepresentation

set_option Elab.async false

namespace Goose.Proofs.ConstructionRepresentation
open Goose.Construct

private theorem withCompletionChannels_register_success (ty : Ty) (origin : Goose.Core.OriginId)
    (action : List Channel → EvalM (List Carrier)) (state after : ExecutionState) (value : Value)
    (evaluated : action [.register ty] state = .ok [.register value] after) :
    withCompletionChannels [.register ty] origin action state = .ok [.register value] after := by
  simp [withCompletionChannels, completionChannelSetup, materializeOwnedCarriers, List.mapM_cons, List.mapM_nil,
    bind, pure, evaluated, List.forIn_nil]

theorem fixedInitializer_activationBody {fuel : Nat} {ty : Ty} {expression : Expr}
    (initializer : FixedInitializer fuel ty expression) (config : EvalConfig)
    (activation : RuntimeActivation) (channels : activation.channels = [.register ty])
    (scope : Nat) (state : ExecutionState) :
    ∃ value after, execActivationBody (fuel + 2) config activation [] (.mk scope [] (some expression)) state =
      .ok [.register value] after ∧ ValueRepresentation ty value ∧
      after.construction = state.construction := by
  let scopedEnv := { activation with scopes := (scope, state.nextScope) :: activation.scopes }
  let prepared : ExecutionState := { state with
    nextScope := state.nextScope + 1
    activations := state.activations.map (fun current =>
      if current.act == activation.act then { current with scopes := scopedEnv.scopes } else current) }
  obtain ⟨value, produced, represented⟩ := fixedInitializer_produce initializer config scopedEnv prepared
  have completed := withCompletionChannels_register_success ty (expressionOrigin expression)
    (fun channels => evalProduce (fuel + 1) config scopedEnv channels expression) prepared prepared value produced
  refine ⟨value, releaseScopeState activation scope state.nextScope prepared, ?_, represented, rfl⟩
  simp only [execActivationBody, execResultScope, freshScope, EvalM.get, EvalM.set,
    bind, pure, withScope, bindAll, List.forIn_nil, execStmts, channels]
  simp only [scopedEnv, prepared, channels] at completed
  simp only [completed, releaseScope, EvalM.get, EvalM.set, bind]
  rfl

theorem fixedInitializer_enterActivation {fuel : Nat} {ty : Ty} {expression : Expr}
    (initializer : FixedInitializer fuel ty expression) (config : EvalConfig)
    (activation : RuntimeActivation) (implementation : Impl)
    (present : config.module.impls[activation.implementation]? = some implementation)
    (channels : activation.channels = [.register ty])
    (results : implementation.results = #[⟨ty, .register, none⟩])
    (scope : Nat) (origin : Goose.Core.OriginId) (state : ExecutionState) :
    ∃ value after, enterActivation (fuel + 3) config activation [] (.mk scope [] (some expression)) origin state =
      .ok [.register value] after ∧ ValueRepresentation ty value ∧
      after.construction = state.construction := by
  obtain ⟨value, after, evaluated, represented, construction⟩ :=
    fixedInitializer_activationBody initializer config activation channels scope state
  refine ⟨value, { after with activations := after.activations.filter (fun current => current.act != activation.act) },
    ?_, represented, construction⟩
  simp [enterActivation, present, finishActivation, evaluated, channels, results,
    finishChannels, landCarriersInto, finishChannel, List.forIn_cons, List.forIn_nil, bind, pure]

theorem fixedInitializer_invokeCall {fuel : Nat} {ty : Ty} {expression : Expr}
    (initializer : FixedInitializer fuel ty expression) (config : EvalConfig)
    (environment : RuntimeActivation) (context : Goose.Core.ContextId) (contextInfo : Context)
    (implementation : Impl)
    (contextPresent : config.module.contexts[context]? = some contextInfo)
    (present : config.module.impls[contextInfo.impl]? = some implementation)
    (parameters : implementation.params = #[])
    (results : implementation.results = #[⟨ty, .register, none⟩])
    (scope : Nat) (body : implementation.body = .mk scope [] (some expression))
    (origin : Goose.Core.OriginId) (state : ExecutionState)
    (depth : state.activations.length < Goose.Core.maxCallDepth) :
    ∃ value after, invokeCall (fuel + 4) config environment context [] [.register ty] origin state =
      .ok [.register value] after ∧ ValueRepresentation ty value ∧
      after.construction = state.construction := by
  let activation : RuntimeActivation := ⟨contextInfo.impl, state.nextAct, implementation.vars, [], [.register ty]⟩
  let prepared : ExecutionState := { state with
    nextAct := state.nextAct + 1
    activations := activation :: state.activations }
  obtain ⟨value, after, evaluated, represented, construction⟩ := fixedInitializer_enterActivation initializer
    config activation implementation present rfl results scope origin prepared
  refine ⟨value, after, ?_, represented, construction⟩
  simp only [activation, prepared] at evaluated
  simp [invokeCall, getImplementation, contextPresent, present, parameters, results, body,
    evalArguments, freshAct, EvalM.get, EvalM.set, List.mapM_cons, List.mapM_nil, bind, pure,
    Nat.not_le.mpr depth, evaluated, deliverCarriers]

theorem fixedInitializer_callValue {fuel : Nat} {ty : Ty} {expression : Expr}
    (initializer : FixedInitializer fuel ty expression) (config : EvalConfig)
    (environment : RuntimeActivation) (context : Goose.Core.ContextId) (contextInfo : Context)
    (implementation : Impl)
    (contextPresent : config.module.contexts[context]? = some contextInfo)
    (present : config.module.impls[contextInfo.impl]? = some implementation)
    (parameters : implementation.params = #[])
    (results : implementation.results = #[⟨ty, .register, none⟩])
    (scope : Nat) (body : implementation.body = .mk scope [] (some expression))
    (origin : Goose.Core.OriginId) (state : ExecutionState)
    (depth : state.activations.length < Goose.Core.maxCallDepth) :
    ∃ value after, evalValue (fuel + 5) config environment (.call context [] origin) state =
      .ok value after ∧ ValueRepresentation ty value ∧ after.construction = state.construction := by
  obtain ⟨value, after, evaluated, represented, construction⟩ := fixedInitializer_invokeCall initializer
    config environment context contextInfo implementation contextPresent present parameters results scope body origin state depth
  refine ⟨value, after, ?_, represented, construction⟩
  simp [evalValue, getImplementation, contextPresent, present, channelsFor, results, evaluated,
    publishCarriers, liftConstruction, publishOperation, preflightPublication, ConstructionM.get,
    List.mapM_cons, List.mapM_nil, List.forIn_nil, singleCarrier, carrierValue, bind, pure, Except.bind, Except.pure]

theorem accepted_integerArray_initializer (config : EvalConfig) (id : Goose.Core.ImplId)
    (implementation : Impl) (accepted : validate config.module = .ok ())
    (present : config.module.impls[id]? = some implementation)
    (scope : Nat) (intType : Goose.Core.IntTy) (count : Nat) (values : List Int)
    (origin : Goose.Core.OriginId)
    (body : implementation.body = .mk scope [] (some
      (.arrLit (.arr (.int intType) count) (values.map (.lit intType)) origin)))
    (fuel : Nat) :
    FixedInitializer (fuel + 2) (.arr (.int intType) count)
      (.arrLit (.arr (.int intType) count) (values.map (.lit intType)) origin) := by
  obtain ⟨types, declared, checked⟩ := validated_implementation_typing config.module id implementation accepted present
  rw [body] at checked
  simp only [typeBlock, typeStatements] at checked
  have length := checkedFixedArray_length 4094 _ (.int intType) count
    (values.map (.lit intType)) origin implementation.params.size declared types checked
  rw [length]
  apply FixedInitializer.array (fuel + 1) (.int intType) (values.map (.lit intType)) origin rfl
  intro operand member
  obtain ⟨value, _, equal⟩ := List.mem_map.mp member
  subst operand
  exact .integer fuel intType value

theorem accepted_integerArray_callValue (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (context : Goose.Core.ContextId) (contextInfo : Context)
    (implementation : Impl) (accepted : validate config.module = .ok ())
    (contextPresent : config.module.contexts[context]? = some contextInfo)
    (present : config.module.impls[contextInfo.impl]? = some implementation)
    (parameters : implementation.params = #[])
    (scope : Nat) (intType : Goose.Core.IntTy) (count : Nat) (values : List Int)
    (arrayOrigin callOrigin : Goose.Core.OriginId)
    (results : implementation.results = #[⟨.arr (.int intType) count, .register, none⟩])
    (body : implementation.body = .mk scope [] (some
      (.arrLit (.arr (.int intType) count) (values.map (.lit intType)) arrayOrigin)))
    (state : ExecutionState) (depth : state.activations.length < Goose.Core.maxCallDepth) :
    ∃ elements after,
      evalValue (fuel + 7) config environment (.call context [] callOrigin) state = .ok (.fixed elements) after ∧
      elements.size = count ∧ (∀ value ∈ elements.toList, ValueRepresentation (.int intType) value) ∧
      after.construction = state.construction := by
  have initializer := accepted_integerArray_initializer config contextInfo.impl implementation accepted present
    scope intType count values arrayOrigin body fuel
  obtain ⟨value, after, evaluated, represented, construction⟩ := fixedInitializer_callValue initializer
    config environment context contextInfo implementation contextPresent present parameters results scope body callOrigin state depth
  cases represented with
  | array element count elements inline length children =>
      exact ⟨elements, after, evaluated, length, children, construction⟩
  | stored ty stored nonfixed logicalType =>
      simp [Ty.nonfixed, Ty.variableElement] at nonfixed

#print axioms validated_implementation_typing
#print axioms accepted_integerArray_callValue
#print axioms accepted_integerArray_initializer
#print axioms fixedInitializer_callValue
#print axioms fixedInitializer_invokeCall
#print axioms fixedInitializer_enterActivation
#print axioms fixedInitializer_activationBody

end Goose.Proofs.ConstructionRepresentation
