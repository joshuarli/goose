import Goose.Proofs.ExitExecutionInvocationStatementsCausal
import Goose.Proofs.ExitExecutionPathSequences
import Goose.Proofs.ExitExecutionPathScopes
import Goose.Proofs.ExitExecutionPathRank
import Goose.Proofs.ExitExecutionPathModule
import Goose.Proofs.ExitExecutionInvocationStatements
import Goose.Proofs.ExitExecutionPathHandlers
import Goose.Proofs.ExitExecutionCleanupFrames
import Goose.Proofs.ExitExecutionPathValues
import Goose.Proofs.ExitExecutionPathProducers
import Goose.Proofs.ExitExecutionActivationChannels
import Goose.Proofs.ExitExecutionPathArguments
import Goose.Proofs.ExitExecutionPathCalls
import Goose.Proofs.ExitExecutionPathControls
import Goose.Proofs.ExitExecutionPathCompletion
import Goose.Proofs.ExitExecutionInvocationProducersChannels

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem runModule_reaches_globals (fuel : Nat) (config : EvalConfig) :
    ExitReached fuel config (.globals fuel (List.range config.module.globals.size)) .initial :=
  .call .initial (.moduleGlobals fuel .initial)

private theorem bind_ok_origin (action : EvalM α) (next : α → EvalM β)
    (initial final : ExecutionState) (value : β)
    (normal : (action >>= next) initial = .ok value final) :
    ∃ first middle, action initial = .ok first middle ∧ next first middle = .ok value final := by
  cases evaluated : action initial with
  | ok first middle =>
      simp only [bind, evaluated] at normal
      exact ⟨first, middle, rfl, normal⟩
  | stop reason after | escape target carriers after | jump target kind after =>
      simp only [bind, evaluated] at normal
      cases normal

private theorem invokeCall_returned_activation (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (context : Goose.Core.ContextId) (arguments : List Arg)
    (channels : List Channel) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (carriers : List Carrier)
    (returned : invokeCall (fuel + 1) config environment context arguments channels origin initial = .ok carriers final) :
    ∃ activation pre body entered returnedCarriers afterBody,
      CallActivationPrefix fuel config environment context arguments channels origin initial activation pre body entered ∧
      enterActivation fuel config activation pre body origin entered = .ok returnedCarriers afterBody ∧
      deliverCarriers fuel config.layout channels returnedCarriers origin afterBody = .ok carriers final := by
  simp only [invokeCall] at returned
  obtain ⟨⟨id, implementation⟩, lookupState, lookup, rest⟩ := bind_ok_origin _ _ initial final carriers returned
  split at rest
  · simp only [fault] at rest
    cases rest
  · rename_i arity
    obtain ⟨firstChannels, firstState, receiving, rest⟩ := bind_ok_origin _ _ lookupState final carriers rest
    obtain ⟨values, argumentState, argumentsDone, rest⟩ := bind_ok_origin _ _ firstState final carriers rest
    obtain ⟨renewed, ready, renewal, rest⟩ := bind_ok_origin _ _ argumentState final carriers rest
    simp only [EvalM.get, bind] at rest
    split at rest
    · simp only [timeout, EvalM.stop] at rest
      cases rest
    · rename_i depth
      simp only [freshAct, EvalM.get, EvalM.set, bind, pure] at rest
      obtain ⟨returnedCarriers, afterBody, entered, delivered⟩ := bind_ok_origin _ _ _ final carriers rest
      refine ⟨_, _, _, _, returnedCarriers, afterBody, ?_, entered, delivered⟩
      exact CallActivationPrefix.actual initial firstState argumentState ready id implementation
        firstChannels renewed values
        (.actual initial lookupState firstState id implementation firstChannels lookup (Bool.eq_false_iff.mpr arity) receiving)
        argumentsDone renewal (Nat.lt_of_not_ge depth)

private theorem CallArgumentPrefix.escape_arguments
    {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {context : Goose.Core.ContextId} {arguments : List Arg} {channels : List Channel} {origin : Goose.Core.OriginId}
    {initial prepared final : ExecutionState} {id : Goose.Core.ImplId} {implementation : Impl}
    {firstChannels : List Channel} {address : ExitAddress} {carriers : List Carrier}
    (receiving : CallArgumentPrefix config context channels origin initial id implementation firstChannels prepared)
    (escaped : evalArguments fuel config environment implementation.vars implementation.params.toList arguments prepared =
      .escape address carriers final) :
    invokeCall (fuel + 1) config environment context arguments channels origin initial = .escape address carriers final := by
  cases receiving with
  | actual lookupState firstState id implementation firstChannels lookup arity receiving =>
      simp only [bind] at receiving
      simp only [invokeCall, bind, lookup, arity, Bool.false_eq_true, ↓reduceIte]
      erw [receiving]
      simp only [escaped]

private theorem CallActivationPrefix.escape_activation
    {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {context : Goose.Core.ContextId} {arguments : List Arg} {channels : List Channel} {origin : Goose.Core.OriginId}
    {initial entered final : ExecutionState} {activation : RuntimeActivation}
    {pre : List (Goose.Core.VarId × Value)} {body : Block} {address : ExitAddress} {carriers : List Carrier}
    (prepared : CallActivationPrefix fuel config environment context arguments channels origin initial activation pre body entered)
    (escaped : enterActivation fuel config activation pre body origin entered = .escape address carriers final) :
    invokeCall (fuel + 1) config environment context arguments channels origin initial = .escape address carriers final := by
  cases prepared with
  | actual firstState argumentState ready id implementation firstChannels renewed values
      receiving argumentsDone renewal depth =>
      cases receiving with
      | actual lookupState firstState id implementation firstChannels lookup arity receiving =>
          simp only [bind, pure] at receiving renewal
          simp only [invokeCall, bind, lookup, arity, Bool.false_eq_true, ↓reduceIte]
          erw [receiving]
          simp only [argumentsDone]
          erw [renewal]
          simp only [EvalM.get, Nat.not_le.mpr depth, ↓reduceIte, freshAct, EvalM.set, bind, pure, escaped]

private theorem reached_call_escape_origin (rootFuel fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (context : Goose.Core.ContextId) (arguments : List Arg)
    (channels : List Channel) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.call (fuel + 1) environment context arguments channels origin) initial)
    (escaped : invokeCall (fuel + 1) config environment context arguments channels origin initial =
      .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared : ExecutionState),
      ExitReached rootFuel config child prepared ∧
      child.action config prepared = .escape address carriers final := by
  rcases callInvocation_escape_inv fuel config environment context arguments channels origin initial final address carriers escaped with
      ⟨id, implementation, firstChannels, prepared, receiving, evaluated⟩ |
      ⟨activation, pre, body, entered, prepared, evaluated⟩
  · exact ⟨List Value, .arguments fuel environment implementation.vars implementation.params.toList arguments,
      prepared, .call reached (.callArguments fuel environment context arguments channels origin initial prepared id implementation
        firstChannels receiving), evaluated⟩
  · exact ⟨List Carrier, .activation fuel activation pre body origin, entered,
      .call reached (.callActivation fuel environment context arguments channels origin initial entered activation pre body prepared), evaluated⟩

#print axioms reached_call_escape_origin

private theorem fresh_of_normal (action : EvalM α) (initial final : ExecutionState) (value : α)
    (normal : action initial = .ok value final) (fresh : FreshActivations initial)
    (preserved : PreservesFresh action) : FreshActivations final := by
  have after := preserved initial fresh
  simpa only [normal, Goose.Proofs.Exit.stepState] using after

private theorem CallArgumentPrefix.fresh
    {config : EvalConfig} {context : Goose.Core.ContextId} {channels : List Channel} {origin : Goose.Core.OriginId}
    {initial prepared : ExecutionState} {id : Goose.Core.ImplId} {implementation : Impl} {firstChannels : List Channel}
    (receiving : CallArgumentPrefix config context channels origin initial id implementation firstChannels prepared)
    (fresh : FreshActivations initial) : FreshActivations prepared := by
  cases receiving
  have previous := evaluation_preservesFresh 0 config
  apply fresh_of_normal (List.mapM _ _) _ _ _ (by assumption)
  · exact fresh_of_normal (getImplementation config context) initial _ _ (by assumption) fresh
      (stateQuery_preservesFresh _ (stateQuery_getImplementation config context))
  · fresh_eval previous

private theorem CallActivationPrefix.fresh
    {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {context : Goose.Core.ContextId} {arguments : List Arg} {channels : List Channel} {origin : Goose.Core.OriginId}
    {initial entered : ExecutionState} {activation : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)} {body : Block}
    (prepared : CallActivationPrefix fuel config environment context arguments channels origin initial activation pre body entered)
    (fresh : FreshActivations initial) : FreshActivations entered := by
  cases prepared with
  | actual firstState argumentState ready id implementation firstChannels renewed values
      receiving argumentsDone renewal depth =>
      have previous := evaluation_preservesFresh fuel config
      have freshFirst := receiving.fresh fresh
      have freshArguments := fresh_of_normal _ _ _ _ argumentsDone freshFirst (previous.arguments _ _ _ _)
      have freshReady := fresh_of_normal _ _ _ _ renewal freshArguments (by fresh_eval previous)
      exact fresh_activation_push ready ⟨id, ready.nextAct, implementation.vars, [], renewed⟩ freshReady rfl

private theorem fresh_scope_prepared (environment : RuntimeActivation) (scope : Nat)
    (initial : ExecutionState) (fresh : FreshActivations initial) :
    FreshActivations { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == environment.act then
        { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } := by
  apply fresh_activations_map { initial with nextScope := initial.nextScope + 1 }
  · intro activation
    split <;> rfl
  · exact fresh

private theorem ArgumentValuePrefix.continuation {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {vars : Array LocalVar} {parameter : Param} {argument : Arg} {initial middle : ExecutionState} {value : Value}
    (prefixResult : ArgumentValuePrefix fuel config environment vars parameter argument initial value middle)
    (parameters : List Param) (arguments : List Arg) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) (argument :: arguments) initial =
      ((do pure (value :: (← evalArguments fuel config environment vars parameters arguments))) : EvalM (List Value)) middle := by
  cases prefixResult <;> simp only [evalArguments, bind, pure, *]

private theorem ArgumentValuePrefix.fresh {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {vars : Array LocalVar} {parameter : Param} {argument : Arg} {initial final : ExecutionState} {value : Value}
    (prefixResult : ArgumentValuePrefix fuel config environment vars parameter argument initial value final)
    (fresh : FreshActivations initial) : FreshActivations final := by
  have previous := evaluation_preservesFresh fuel config
  cases prefixResult
  case reference =>
    exact fresh_of_normal (evalPlace fuel config environment _) initial final _ (by assumption) fresh (previous.place _ _)
  case value =>
    exact fresh_of_normal (evalValue fuel config environment _) initial final _ (by assumption) fresh (previous.value _ _)
  case materialized =>
    apply fresh_of_normal (carrierValue _) _ final _ (by assumption)
    · apply fresh_of_normal (publishCarriers _ _) _ _ _ (by assumption)
      · apply fresh_of_normal (materializedDestination _ _ _ _ _ _ _) _ _ _ (by assumption)
        · exact fresh_of_normal (materializeProducer fuel _ _ (evalValue fuel config environment _)) initial _ _
            (by assumption) fresh (preservesFresh_materializeProducer _ _ _ _ (previous.value _ _))
        · exact preservesFresh_materializedDestination _ _ _ _ _ _ _
      · exact preservesFresh_publishCarriers _ _
    · exact stateQuery_preservesFresh _ (stateQuery_carrierValue _)
  case constructed =>
    apply fresh_of_normal (carrierValue _) _ final _ (by assumption)
    · apply fresh_of_normal (constructLocal _ _ _ _ _ _) _ _ _ (by assumption)
      · exact fresh_of_normal (materializeProducer fuel _ _ (evalValue fuel config environment _)) initial _ _
          (by assumption) fresh (preservesFresh_materializeProducer _ _ _ _ (previous.value _ _))
      · exact preservesFresh_constructLocal _ _ _ _ _ _ (fun destination => previous.build _ _ _)
    · exact stateQuery_preservesFresh _ (stateQuery_carrierValue _)

private theorem ExitCallSite.fresh {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {callee : ExitInvocation β} {initial middle : ExecutionState}
    (site : ExitCallSite config caller initial callee middle) (fresh : FreshActivations initial) :
    FreshActivations middle := by
  cases site
  case values site => exact ValueInvocationEdge.fresh (fun fuel => evaluation_preservesFresh fuel config) site fresh
  case statements site => exact site.fresh config (fun fuel => evaluation_preservesFresh fuel config) fresh
  case producer site => exact site.fresh (fun fuel => evaluation_preservesFresh fuel config) fresh
  case moduleGlobals | activationBody | activationScope | resultBlockWith | resultScope | statementsHead | operandsHead | argumentReference | argumentValue | argumentMaterialize =>
    exact fresh
  case moduleEntry =>
    apply fresh_of_normal (channelsFor config.layout 0 _ 0) _ _ _ (by assumption)
    · apply fresh_of_normal (getImplementation config config.module.entry) _ _ _ (by assumption)
      · exact fresh_of_normal (initGlobals _ config _) _ _ _ (by assumption) fresh (initGlobals_preservesFresh _ _ _)
      · exact stateQuery_preservesFresh _ (stateQuery_getImplementation _ _)
    · exact preservesFresh_channelsFor _ _ _ _
  case callActivation | callArguments =>
    rename_i prepared
    exact prepared.fresh fresh
  case argumentsTail =>
    rename_i normal
    exact normal.fresh fresh
  case completionProduce =>
    rename_i setup
    apply fresh_of_normal _ _ _ _ setup fresh
    have previous := evaluation_preservesFresh 0 config
    fresh_eval previous
  case argumentBuild =>
    rename_i allocated
    exact fresh_of_normal _ _ _ _ allocated fresh (preservesFresh_newDestination _ _ _ _ _ _ _)
  case operandsTail =>
    rename_i producedNormally selected
    apply fresh_of_normal _ _ _ _ selected
    · exact fresh_of_normal _ _ _ _ producedNormally fresh ((evaluation_preservesFresh _ config).produce _ _ _)
    · exact stateQuery_preservesFresh _ (stateQuery_singleCarrier _)
  case statementsTail =>
    rename_i normal
    exact fresh_of_normal _ _ _ _ normal fresh ((evaluation_preservesFresh _ config).statement _ _)
  case blockStatements =>
    rename_i binding
    exact fresh_of_normal _ _ _ _ binding fresh (preservesFresh_bindAll _ _ _)
  case blockValueTail | blockProduceTail =>
    apply fresh_of_normal (execStmts _ config _ _) _ _ _ (by assumption)
    · exact fresh_of_normal (bindAll _ _ _) { initial with nextScope := initial.nextScope + 1 }
        _ _ (by assumption) fresh (preservesFresh_bindAll _ _ _)
    · exact (evaluation_preservesFresh _ config).statements _ _
  case activationStatements | resultStatements =>
    rename_i binding
    exact fresh_of_normal _ _ _ _ binding (fresh_scope_prepared _ _ _ fresh) (preservesFresh_bindAll _ _ _)
  case activationTail | resultTail =>
    rename_i binding normal
    have boundFresh := fresh_of_normal _ _ _ _ binding (fresh_scope_prepared _ _ _ fresh) (preservesFresh_bindAll _ _ _)
    exact fresh_of_normal _ _ _ _ normal boundFresh ((evaluation_preservesFresh _ config).statements _ _)
  case returnFromOperands | returnFromForwardProduce | returnOperands | returnForwardProduce | returnProduce | breakProduce =>
    rename_i selected setup
    exact fresh_of_normal _ _ _ _ setup fresh (preservesFresh_exitChannels _ _ _ _)

private theorem ExitReached.fresh {fuel : Nat} {config : EvalConfig} {α : Type}
    {invocation : ExitInvocation α} {state : ExecutionState}
    (reached : ExitReached fuel config invocation state) : FreshActivations state := by
  induction reached with
  | initial => exact freshActivations_initial
  | call callerReached site previous => exact site.fresh previous

private theorem reached_call_returned_activation (rootFuel fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (context : Goose.Core.ContextId) (arguments : List Arg)
    (channels : List Channel) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.call (fuel + 1) environment context arguments channels origin) initial)
    (returned : invokeCall (fuel + 1) config environment context arguments channels origin initial = .ok carriers final) :
    ∃ activation pre body entered returnedCarriers afterBody,
      ExitReached rootFuel config (.activation fuel activation pre body origin) entered ∧
      enterActivation fuel config activation pre body origin entered = .ok returnedCarriers afterBody ∧
      deliverCarriers fuel config.layout channels returnedCarriers origin afterBody = .ok carriers final := by
  obtain ⟨activation, pre, body, entered, returnedCarriers, afterBody, prepared, returned, delivered⟩ :=
    invokeCall_returned_activation fuel config environment context arguments channels origin initial final carriers returned
  exact ⟨activation, pre, body, entered, returnedCarriers, afterBody,
    .call reached (.callActivation fuel environment context arguments channels origin initial entered activation pre body prepared),
    returned, delivered⟩

private theorem enterActivation_returned_body (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (body : Block) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (carriers : List Carrier)
    (returned : enterActivation (fuel + 1) config activation pre body origin initial = .ok carriers final) :
    ∃ implementation before,
      config.module.impls[activation.implementation]? = some implementation ∧
      (execActivationBody fuel config activation pre body initial = .ok carriers before ∨
        ∃ address, execActivationBody fuel config activation pre body initial = .escape address carriers before ∧
          address.activation = activation.act) ∧
      finishChannels config.layout activation.channels (implementation.results.toList.map (·.ty)) carriers origin
        { before with activations := before.activations.filter (fun current => current.act != activation.act) } = .ok () final := by
  cases lookup : config.module.impls[activation.implementation]? with
  | none =>
      simp only [enterActivation, lookup, fault, EvalM.stop] at returned
      cases returned
  | some implementation =>
      simp only [enterActivation, lookup] at returned
      cases evaluated : execActivationBody fuel config activation pre body initial with
      | stop reason after | jump target kind after =>
          simp only [finishActivation, evaluated] at returned
          cases returned
      | ok values before =>
          cases landed : finishChannels config.layout activation.channels (implementation.results.toList.map (·.ty)) values origin
              { before with activations := before.activations.filter (fun current => current.act != activation.act) } with
          | ok ignored after =>
              cases ignored
              simp only [finishActivation, evaluated, landed] at returned
              cases returned
              exact ⟨implementation, before, rfl, Or.inl rfl, landed⟩
          | stop reason after | escape target payload after | jump target kind after =>
              simp only [finishActivation, evaluated, landed] at returned
              cases returned
      | escape address values before =>
          by_cases caught : address.activation = activation.act
          · cases landed : finishChannels config.layout activation.channels (implementation.results.toList.map (·.ty)) values origin
                { before with activations := before.activations.filter (fun current => current.act != activation.act) } with
            | ok ignored after =>
                cases ignored
                simp only [finishActivation, evaluated, caught, beq_self_eq_true, ↓reduceIte, landed] at returned
                cases returned
                exact ⟨implementation, before, rfl, Or.inr ⟨address, rfl, caught⟩, landed⟩
            | stop reason after | escape target payload after | jump target kind after =>
                simp only [finishActivation, evaluated, caught, beq_self_eq_true, ↓reduceIte, landed] at returned
                cases returned
          · simp only [finishActivation, evaluated, caught, beq_iff_eq, ↓reduceIte] at returned
            cases returned

theorem runModule_returned_entry (fuel : Nat) (config : EvalConfig) (final : ExecutionState)
    (returned : runModule fuel config .initial = .ok () final) :
    ∃ id implementation globalsState implementationState channels entryState carriers afterCall,
      initGlobals fuel config (List.range config.module.globals.size) .initial = .ok () globalsState ∧
      getImplementation config config.module.entry globalsState = .ok (id, implementation) implementationState ∧
      channelsFor config.layout 0 implementation.results.toList 0 implementationState = .ok channels entryState ∧
      invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0 entryState = .ok carriers afterCall ∧
      publishCarriers 0 carriers afterCall = .ok () final := by
  unfold runModule at returned
  obtain ⟨ignored, globalsState, globals, rest⟩ := bind_ok_origin _ _ .initial final () returned
  cases ignored
  obtain ⟨⟨id, implementation⟩, implementationState, lookup, rest⟩ :=
    bind_ok_origin _ _ globalsState final () rest
  obtain ⟨channels, entryState, receiving, rest⟩ := bind_ok_origin _ _ implementationState final () rest
  obtain ⟨carriers, afterCall, called, published⟩ := bind_ok_origin _ _ entryState final () rest
  exact ⟨id, implementation, globalsState, implementationState, channels, entryState, carriers, afterCall,
    globals, lookup, receiving, called, published⟩

private theorem runModule_returned_reaches_entry (fuel : Nat) (config : EvalConfig) (final : ExecutionState)
    (returned : runModule fuel config .initial = .ok () final) :
    ∃ channels entryState carriers afterCall,
      ExitReached fuel config (.call fuel ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0) entryState ∧
      invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0 entryState = .ok carriers afterCall := by
  obtain ⟨id, implementation, globalsState, implementationState, channels, entryState, carriers, afterCall,
      globals, lookup, receiving, called, published⟩ := runModule_returned_entry fuel config final returned
  exact ⟨channels, entryState, carriers, afterCall,
    .call .initial (.moduleEntry fuel .initial globalsState implementationState entryState
      id implementation channels globals lookup receiving), called⟩

private theorem runModule_returned_reaches_handler (fuel : Nat) (config : EvalConfig) (final : ExecutionState)
    (returned : runModule fuel config .initial = .ok () final) :
    ∃ activationFuel activation pre body entered carriers afterBody,
      fuel = activationFuel + 1 ∧
      ExitReached fuel config (.activation activationFuel activation pre body 0) entered ∧
      enterActivation activationFuel config activation pre body 0 entered = .ok carriers afterBody := by
  obtain ⟨channels, entryState, carriers, afterCall, reached, called⟩ :=
    runModule_returned_reaches_entry fuel config final returned
  cases fuel with
  | zero =>
      simp only [invokeCall, timeout, EvalM.stop] at called
      cases called
  | succ fuel =>
      obtain ⟨activation, pre, body, entered, returnedCarriers, afterBody, reached, enteredNormally, delivered⟩ :=
        reached_call_returned_activation (fuel + 1) fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0
          entryState afterCall carriers reached called
      exact ⟨fuel, activation, pre, body, entered, returnedCarriers, afterBody, rfl, reached, enteredNormally⟩

private theorem runModule_returned_reaches_body (fuel : Nat) (config : EvalConfig) (final : ExecutionState)
    (returned : runModule fuel config .initial = .ok () final) :
    ∃ bodyFuel activation pre body entered carriers before,
      fuel = bodyFuel + 2 ∧
      ExitReached fuel config (.activationBody bodyFuel activation pre body) entered ∧
      (execActivationBody bodyFuel config activation pre body entered = .ok carriers before ∨
        ∃ address, execActivationBody bodyFuel config activation pre body entered = .escape address carriers before ∧
          address.activation = activation.act) := by
  obtain ⟨activationFuel, activation, pre, body, entered, carriers, afterBody, fuelShape, reached, enteredNormally⟩ :=
    runModule_returned_reaches_handler fuel config final returned
  cases activationFuel with
  | zero =>
      simp only [enterActivation, timeout, EvalM.stop] at enteredNormally
      cases enteredNormally
  | succ bodyFuel =>
      obtain ⟨implementation, before, lookup, occurrence, landed⟩ :=
        enterActivation_returned_body bodyFuel config activation pre body 0 entered afterBody carriers enteredNormally
      exact ⟨bodyFuel, activation, pre, body, entered, carriers, before, fuelShape,
        .call reached (.activationBody bodyFuel activation pre body 0 entered implementation lookup), occurrence⟩

private theorem execActivationBody_returned_scope (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (initial final : ExecutionState) (carriers : List Carrier)
    (returned : execActivationBody (fuel + 1) config activation pre body initial = .ok carriers final) :
    ∃ value, (ExitInvocation.activationScope fuel activation pre body).action config initial =
      .ok (.normal value, carriers) final := by
  simp only [execActivationBody] at returned
  obtain ⟨⟨flow, values⟩, afterScope, scopedResult, remaining⟩ := bind_ok_origin _ _ initial final carriers returned
  cases flow with
  | normal value =>
      simp only [pure] at remaining
      cases remaining
      exact ⟨value, scopedResult⟩
  | breaking value | continuing =>
      simp only [fault, EvalM.stop] at remaining
      cases remaining

private theorem runModule_returned_reaches_scope (fuel : Nat) (config : EvalConfig) (final : ExecutionState)
    (returned : runModule fuel config .initial = .ok () final) :
    ∃ scopeFuel activation pre body entered carriers before,
      fuel = scopeFuel + 3 ∧
      ExitReached fuel config (.activationScope scopeFuel activation pre body) entered ∧
      ((∃ value, (ExitInvocation.activationScope scopeFuel activation pre body).action config entered =
          .ok (.normal value, carriers) before) ∨
        ∃ address, (ExitInvocation.activationScope scopeFuel activation pre body).action config entered =
          .escape address carriers before ∧ address.activation = activation.act) := by
  obtain ⟨bodyFuel, activation, pre, body, entered, carriers, before, fuelShape, reached, occurrence⟩ :=
    runModule_returned_reaches_body fuel config final returned
  cases bodyFuel with
  | zero =>
      rcases occurrence with normal | ⟨address, escaped, caught⟩
      · simp only [execActivationBody, timeout, EvalM.stop] at normal
        cases normal
      · simp only [execActivationBody, timeout, EvalM.stop] at escaped
        cases escaped
  | succ scopeFuel =>
      refine ⟨scopeFuel, activation, pre, body, entered, carriers, before, fuelShape,
        .call reached (.activationScope scopeFuel activation pre body entered), ?_⟩
      rcases occurrence with normal | ⟨address, escaped, caught⟩
      · exact Or.inl (execActivationBody_returned_scope scopeFuel config activation pre body entered before carriers normal)
      · exact Or.inr ⟨address,
          execActivationBody_escape_origin scopeFuel config activation pre body entered before address carriers escaped, caught⟩

private theorem reached_block_escape_call (rootFuel fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.block (fuel + 1) environment pre channels (.mk scope statements tail)) initial)
    (escaped : execBlock (fuel + 1) config environment pre channels (.mk scope statements tail) initial =
      .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (childState before : ExecutionState),
      ExitReached rootFuel config child childState ∧
      child.action config childState = .escape address carriers before ∧
      final = releaseScopeState environment scope initial.nextScope before := by
  obtain ⟨bound, before, binding, origin, released⟩ :=
    execBlock_escape_call fuel config environment pre channels scope statements tail initial final address carriers escaped
  rcases origin with fromStatements | ⟨value, middle, expression, normal, tailPresent, fromTail⟩
  · exact ⟨Flow, .statements fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements,
      bound, before, .call reached
        (.blockStatements fuel environment pre channels scope statements tail initial bound binding), fromStatements, released⟩
  · subst tail
    rcases fromTail with ⟨empty, fromValue⟩ | ⟨nonempty, fromProduce⟩
    · exact ⟨Value, .value fuel
        { environment with scopes := (scope, initial.nextScope) :: environment.scopes } expression,
        middle, before, .call reached
          (.blockValueTail fuel environment pre channels scope statements expression initial bound middle value binding normal empty),
        fromValue, released⟩
    · exact ⟨List Carrier, .produce fuel
        { environment with scopes := (scope, initial.nextScope) :: environment.scopes } channels expression,
        middle, before, .call reached
          (.blockProduceTail fuel environment pre channels scope statements expression initial bound middle value binding normal nonempty),
        fromProduce, released⟩

private theorem arguments_tail_escape {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {vars : Array LocalVar} {parameter : Param} {argument : Arg} {initial middle final : ExecutionState} {value : Value}
    (prefixResult : ArgumentValuePrefix fuel config environment vars parameter argument initial value middle)
    (parameters : List Param) (arguments : List Arg) (address : ExitAddress) (carriers : List Carrier)
    (escaped : evalArguments fuel config environment vars parameters arguments middle = .escape address carriers final) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) (argument :: arguments) initial =
      .escape address carriers final := by
  rw [prefixResult.continuation parameters arguments]
  simp only [bind, escaped]

private theorem arguments_reference_escape (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (mutability : Goose.Core.Mutability) (place : Place) (arguments : List Arg)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : evalPlace fuel config environment place initial = .escape address carriers final) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) (.byRef mutability place :: arguments) initial =
      .escape address carriers final := by
  simp only [evalArguments, bind, escaped]

private theorem arguments_value_escape (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param) (operand : Expr) (arguments : List Arg)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : evalValue fuel config environment operand initial = .escape address carriers final) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) (.byVal operand :: arguments) initial =
      .escape address carriers final := by
  simp only [evalArguments, bind, escaped]

private theorem arguments_materialize_escape (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param) (operand : Expr) (arguments : List Arg)
    (descriptor : LocalVar) (count : Nat) (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (lookup : vars[parameter.var]? = some descriptor)
    (materialized : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = some count)
    (escaped : evalValue fuel config environment operand initial = .escape address carriers final) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) (.construct operand :: arguments) initial =
      .escape address carriers final := by
  simp only [evalArguments, lookup, materializeProducer, materialized, bind, escaped]

private theorem arguments_build_escape (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (parameters : List Param) (operand : Expr) (arguments : List Arg)
    (descriptor : LocalVar) (destination : Nat) (initial prepared final : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier)
    (lookup : vars[parameter.var]? = some descriptor)
    (materialized : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = none)
    (allocated : newDestination config.layout environment.act descriptor.ty .value (expressionOrigin operand) none
      (producerCount? ⟨config.module, environment.vars⟩ operand) initial = .ok destination prepared)
    (escaped : buildExpr fuel config environment destination operand prepared = .escape address carriers final) :
    evalArguments (fuel + 1) config environment vars (parameter :: parameters) (.construct operand :: arguments) initial =
      .escape address carriers final := by
  simp only [EvalConfig.layout] at allocated
  simp only [evalArguments, lookup, materializeProducer, materialized, constructLocal, bind, pure, allocated, escaped]

private theorem reached_arguments_escape_call (rootFuel fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (vars : Array LocalVar) (parameters : List Param) (arguments : List Arg)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.arguments fuel environment vars parameters arguments) initial)
    (escaped : evalArguments fuel config environment vars parameters arguments initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared : ExecutionState),
      ExitReached rootFuel config child prepared ∧ child.action config prepared = .escape address carriers final := by
  obtain ⟨β, child, prepared, site, childEscape⟩ := argumentsInvocation_escape_inv fuel config environment vars parameters arguments
    initial final address carriers escaped
  exact ⟨β, child, prepared, .call reached site, childEscape⟩

private theorem operands_head_escape (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channel : Channel) (channels : List Channel) (operand : Expr) (operands : List Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : evalProduce fuel config environment [channel] operand initial = .escape address carriers final) :
    evalOperands (fuel + 1) config environment (channel :: channels) (operand :: operands) initial =
      .escape address carriers final := by
  simp only [evalOperands, bind, escaped]

private theorem operands_tail_escape (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (channel : Channel) (channels : List Channel) (operand : Expr) (operands : List Expr)
    (initial produced middle final : ExecutionState) (raw : List Carrier) (carrier : Carrier)
    (address : ExitAddress) (carriers : List Carrier)
    (normal : evalProduce fuel config environment [channel] operand initial = .ok raw produced)
    (selected : singleCarrier raw produced = .ok carrier middle)
    (escaped : evalOperands fuel config environment channels operands middle = .escape address carriers final) :
    evalOperands (fuel + 1) config environment (channel :: channels) (operand :: operands) initial =
      .escape address carriers final := by
  simp only [evalOperands, bind, normal, selected, escaped]

private theorem reached_operands_escape_call (rootFuel fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channel : Channel) (channels : List Channel)
    (operand : Expr) (operands : List Expr) (initial final : ExecutionState)
    (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.operands (fuel + 1) environment (channel :: channels) (operand :: operands)) initial)
    (escaped : evalOperands (fuel + 1) config environment (channel :: channels) (operand :: operands) initial =
      .escape address carriers final) :
    ∃ child : ExitInvocation (List Carrier), ∃ childState,
      ExitReached rootFuel config child childState ∧ child.action config childState = .escape address carriers final := by
  simp only [evalOperands] at escaped
  cases production : evalProduce fuel config environment [channel] operand initial with
  | escape target returned after =>
      simp only [bind, production] at escaped
      cases escaped
      exact ⟨.produce fuel environment [channel] operand, initial,
        .call reached (.operandsHead fuel environment channel channels operand operands initial), production⟩
  | stop reason after | jump target kind after =>
      simp only [bind, production] at escaped
      cases escaped
  | ok raw produced =>
      simp only [bind, production] at escaped
      cases selected : singleCarrier raw produced with
      | ok carrier middle =>
          simp only [selected] at escaped
          cases tailResult : evalOperands fuel config environment channels operands middle with
          | escape target returned after =>
              simp only [tailResult] at escaped
              cases escaped
              exact ⟨.operands fuel environment channels operands, middle,
                .call reached (.operandsTail fuel environment channel channels operand operands initial produced middle
                  raw carrier production selected), tailResult⟩
          | ok value after | stop reason after | jump target kind after =>
              simp only [tailResult, pure] at escaped
              cases escaped
      | stop reason after =>
          simp only [selected] at escaped
          cases escaped
      | escape target returned after | jump target kind after =>
          unfold singleCarrier at selected
          split at selected <;> cases selected

private theorem block_statements_escape (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (initial bound before : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (escaped : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements bound =
        .escape address carriers before) :
    execBlock (fuel + 1) config environment pre channels (.mk scope statements tail) initial =
      .escape address carriers (releaseScopeState environment scope initial.nextScope before) := by
  simp only [execBlock, freshScope, withScope, releaseScope, EvalM.get, EvalM.set, bind, pure, binding, escaped]

private theorem block_value_tail_escape (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (expression : Expr)
    (initial bound middle before : ExecutionState) (value : Value) (address : ExitAddress) (carriers : List Carrier)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (normal : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements bound = .ok (.normal value) middle)
    (empty : channels.isEmpty = true)
    (escaped : evalValue fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } expression middle =
        .escape address carriers before) :
    execBlock (fuel + 1) config environment pre channels (.mk scope statements (some expression)) initial =
      .escape address carriers (releaseScopeState environment scope initial.nextScope before) := by
  simp only [execBlock, freshScope, withScope, releaseScope, EvalM.get, EvalM.set, bind, pure, binding, normal, empty, ↓reduceIte, escaped]

private theorem block_produce_tail_escape (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (expression : Expr)
    (initial bound middle before : ExecutionState) (value : Value) (address : ExitAddress) (carriers : List Carrier)
    (binding : bindAll environment.act initial.nextScope pre
      { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
    (normal : execStmts fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements bound = .ok (.normal value) middle)
    (nonempty : channels.isEmpty = false)
    (escaped : evalProduce fuel config
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } channels expression middle =
        .escape address carriers before) :
    execBlock (fuel + 1) config environment pre channels (.mk scope statements (some expression)) initial =
      .escape address carriers (releaseScopeState environment scope initial.nextScope before) := by
  simp only [execBlock, freshScope, withScope, releaseScope, EvalM.get, EvalM.set, bind, pure, binding, normal, nonempty, Bool.false_eq_true, ↓reduceIte, escaped]

private theorem resultScope_statements_escape
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (statementsAction : RuntimeActivation → List Stmt → EvalM Flow)
    (tailAction : RuntimeActivation → Expr → EvalM (List Carrier))
    (initial bound before : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (binding : bindAll environment.act initial.nextScope pre { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == environment.act then
        { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound)
    (escaped : statementsAction
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements bound =
        .escape address carriers before) :
    execResultScope environment pre channels (.mk scope statements tail) statementsAction tailAction initial =
      .escape address carriers (releaseScopeState environment scope initial.nextScope before) := by
  simp only [execResultScope, freshScope, withScope, releaseScope, EvalM.get, EvalM.set, bind, pure, binding, escaped]

private theorem resultScope_tail_escape
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (expression : Expr)
    (statementsAction : RuntimeActivation → List Stmt → EvalM Flow)
    (tailAction : RuntimeActivation → Expr → EvalM (List Carrier))
    (initial bound middle before : ExecutionState) (value : Value) (address : ExitAddress) (carriers : List Carrier)
    (binding : bindAll environment.act initial.nextScope pre { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == environment.act then
        { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound)
    (normal : statementsAction
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements bound = .ok (.normal value) middle)
    (escaped : tailAction
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } expression middle =
        .escape address carriers before) :
    execResultScope environment pre channels (.mk scope statements (some expression)) statementsAction tailAction initial =
      .escape address carriers (releaseScopeState environment scope initial.nextScope before) := by
  simp only [execResultScope, freshScope, withScope, releaseScope, EvalM.get, EvalM.set, bind, pure, binding, normal, escaped]

private theorem enterActivation_propagates_escape (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (origin : Goose.Core.OriginId) (implementation : Impl)
    (initial before : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (lookup : config.module.impls[activation.implementation]? = some implementation)
    (escaped : execActivationBody fuel config activation pre body initial = .escape address carriers before)
    (different : address.activation ≠ activation.act) :
    enterActivation (fuel + 1) config activation pre body origin initial = .escape address carriers
      { before with activations := before.activations.filter (fun current => current.act != activation.act) } := by
  simp only [enterActivation, lookup, finishActivation, escaped, beq_iff_eq, different, ↓reduceIte]

private theorem enterActivation_catches_escape (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (origin : Goose.Core.OriginId) (implementation : Impl)
    (initial before final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (lookup : config.module.impls[activation.implementation]? = some implementation)
    (escaped : execActivationBody fuel config activation pre body initial = .escape address carriers before)
    (same : address.activation = activation.act)
    (landed : finishChannels config.layout activation.channels (implementation.results.toList.map (·.ty)) carriers origin
      { before with activations := before.activations.filter (fun current => current.act != activation.act) } = .ok () final) :
    enterActivation (fuel + 1) config activation pre body origin initial = .ok carriers final := by
  simp only [enterActivation, lookup, finishActivation, escaped, beq_iff_eq, same, ↓reduceIte, landed]

private theorem reached_activation_escape_body (rootFuel fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (origin : Goose.Core.OriginId) (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.activation (fuel + 1) activation pre body origin) initial)
    (escaped : enterActivation (fuel + 1) config activation pre body origin initial = .escape address carriers final) :
    ∃ before,
      ExitReached rootFuel config (.activationBody fuel activation pre body) initial ∧
      execActivationBody fuel config activation pre body initial = .escape address carriers before ∧
      address.activation ≠ activation.act ∧
      final = { before with activations := before.activations.filter (fun current => current.act != activation.act) } := by
  obtain ⟨implementation, before, lookup, evaluated, different, filtered⟩ :=
    enterActivation_escape_origin fuel config activation pre body origin initial final address carriers escaped
  exact ⟨before, .call reached (.activationBody fuel activation pre body origin initial implementation lookup),
    evaluated, different, filtered⟩

#print axioms reached_activation_escape_body

private theorem reached_activationBody_escape_scope (rootFuel fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.activationBody (fuel + 1) activation pre body) initial)
    (escaped : execActivationBody (fuel + 1) config activation pre body initial = .escape address carriers final) :
    ExitReached rootFuel config (.activationScope fuel activation pre body) initial ∧
      (ExitInvocation.activationScope fuel activation pre body).action config initial = .escape address carriers final := by
  exact ⟨.call reached (.activationScope fuel activation pre body initial),
    execActivationBody_escape_origin fuel config activation pre body initial final address carriers escaped⟩

#print axioms reached_activationBody_escape_scope

private theorem reached_completion_escape_produce (rootFuel fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (expression : Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.completionTail fuel environment channels expression) initial)
    (escaped : (ExitInvocation.completionTail fuel environment channels expression).action config initial =
      .escape address carriers final) :
    ∃ (planned : List (Channel × Option Nat)) (prepared before : ExecutionState),
      ExitReached rootFuel config (.produce fuel environment (planned.map Prod.fst) expression) prepared ∧
      evalProduce fuel config environment (planned.map Prod.fst) expression prepared = .escape address carriers before ∧
      exitChannelCleanupBorrowed (expressionOrigin expression) [] (planned.filterMap Prod.snd) true carriers before = .ok () final := by
  obtain ⟨planned, prepared, before, setup, evaluated, cleaned⟩ :=
    completionInvocation_escape_inv fuel config environment channels expression initial final address carriers escaped
  exact ⟨planned, prepared, before,
    .call reached (.completionProduce fuel environment channels expression initial prepared planned setup), evaluated, cleaned⟩

#print axioms reached_completion_escape_produce

private theorem reached_resultBlock_escape_scope (rootFuel fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (body : Block)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.resultBlock (fuel + 1) environment channels body) initial)
    (escaped : execResultBlock (fuel + 1) config environment channels body initial = .escape address carriers final) :
    ExitReached rootFuel config (.resultBlockWith fuel environment [] channels body) initial ∧
      execResultBlockWith fuel config environment [] channels body initial = .escape address carriers final := by
  exact ⟨.call reached (.resultBlockWith fuel environment channels body initial), by simpa only [execResultBlock] using escaped⟩

private theorem reached_resultBlockWith_escape_scope (rootFuel fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.resultBlockWith (fuel + 1) environment pre channels body) initial)
    (escaped : execResultBlockWith (fuel + 1) config environment pre channels body initial = .escape address carriers final) :
    ExitReached rootFuel config (.resultScope fuel environment pre channels body) initial ∧
      (ExitInvocation.resultScope fuel environment pre channels body).action config initial = .escape address carriers final := by
  exact ⟨.call reached (.resultScope fuel environment pre channels body initial), by simpa only [execResultBlockWith, ExitInvocation.action] using escaped⟩

#print axioms reached_resultBlock_escape_scope
#print axioms reached_resultBlockWith_escape_scope

private theorem reached_activationScope_escape_call (rootFuel fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.activationScope fuel environment pre (.mk scope statements tail)) initial)
    (escaped : (ExitInvocation.activationScope fuel environment pre (.mk scope statements tail)).action config initial =
      .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (childState before : ExecutionState),
      ExitReached rootFuel config child childState ∧
      child.action config childState = .escape address carriers before ∧
      final = releaseScopeState environment scope initial.nextScope before := by
  obtain ⟨bound, before, binding, origin, released⟩ :=
    execResultScope_escape_call environment pre environment.channels scope statements tail
      (fun localEnvironment statements => execStmts fuel config localEnvironment statements)
      (fun localEnvironment expression => withCompletionChannels environment.channels (expressionOrigin expression)
        (fun channels => evalProduce fuel config localEnvironment channels expression)) initial final address carriers escaped
  rcases origin with fromStatements | ⟨value, middle, expression, normal, tailPresent, fromTail⟩
  · exact ⟨Flow, .statements fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements,
      bound, before, .call reached
        (.activationStatements fuel environment pre scope statements tail initial bound binding), fromStatements, released⟩
  · subst tail
    exact ⟨List Carrier, .completionTail fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } environment.channels expression,
      middle, before, .call reached
        (.activationTail fuel environment pre scope statements expression initial bound middle value binding normal),
      fromTail, released⟩

private theorem reached_resultScope_escape_call (rootFuel fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.resultScope fuel environment pre channels (.mk scope statements tail)) initial)
    (escaped : (ExitInvocation.resultScope fuel environment pre channels (.mk scope statements tail)).action config initial =
      .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (childState before : ExecutionState),
      ExitReached rootFuel config child childState ∧
      child.action config childState = .escape address carriers before ∧
      final = releaseScopeState environment scope initial.nextScope before := by
  obtain ⟨bound, before, binding, origin, released⟩ :=
    execResultScope_escape_call environment pre channels scope statements tail
      (fun localEnvironment statements => execStmts fuel config localEnvironment statements)
      (fun localEnvironment expression => evalProduce fuel config localEnvironment channels expression)
      initial final address carriers escaped
  rcases origin with fromStatements | ⟨value, middle, expression, normal, tailPresent, fromTail⟩
  · exact ⟨Flow, .statements fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements,
      bound, before, .call reached
        (.resultStatements fuel environment pre channels scope statements tail initial bound binding), fromStatements, released⟩
  · subst tail
    exact ⟨List Carrier, .produce fuel
      { environment with scopes := (scope, initial.nextScope) :: environment.scopes } channels expression,
      middle, before, .call reached
        (.resultTail fuel environment pre channels scope statements expression initial bound middle value binding normal),
      fromTail, released⟩

private theorem targetActivation_of_nearest_stack (config : EvalConfig) (targetId : Nat)
    (initial : ExecutionState) (activation : RuntimeActivation) (target : Goose.Core.NonlocalTarget)
    (discarded outer : List RuntimeActivation)
    (declared : config.module.targets[targetId]? = some target)
    (stack : initial.activations = discarded ++ activation :: outer)
    (included : target.contains activation.implementation = true)
    (excluded : ∀ earlier ∈ discarded, target.contains earlier.implementation = false) :
    targetActivation config targetId initial = .ok activation initial := by
  have earlier : discarded.find? (fun current => target.contains current.implementation) = none := by
    apply List.find?_eq_none.mpr
    intro current member
    simp only [excluded current member, Bool.false_eq_true, not_false_eq_true]
  have selected : selectTarget? target initial.activations = some activation := by
    rw [stack]
    simp only [selectTarget?, List.find?_append, earlier, List.find?_cons, included, Option.or]
  simp only [targetActivation, declared, EvalM.get, bind, selected, pure]

private theorem reached_returnFrom_escape_operands (rootFuel fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (targetId : Nat) (operands : List Expr) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.statement (fuel + 1) environment (.returnFrom targetId operands origin)) initial)
    (escaped : execStmt (fuel + 1) config environment (.returnFrom targetId operands origin) initial =
      .escape address carriers final) :
    (∃ activation channels prepared afterOperands,
      targetActivation config targetId initial = .ok activation initial ∧
      exitChannels environment activation operands origin initial = .ok channels prepared ∧
      ExitReached rootFuel config (.operands fuel environment channels operands) prepared ∧
      evalOperands fuel config environment channels operands prepared = .escape address carriers afterOperands ∧
      exitChannelCleanupBorrowed origin (borrowedExitChannelReceipts activation initial)
        (exitChannelReservationTokens initial.construction.exitReservations.size prepared) true carriers
        afterOperands = .ok () final) ∨
    ∃ activation channels prepared raw afterOperands afterMaterialized,
      targetActivation config targetId initial = .ok activation initial ∧
      exitChannels environment activation operands origin initial = .ok channels prepared ∧
      ExitReached rootFuel config (.operands fuel environment channels operands) prepared ∧
      evalOperands fuel config environment channels operands prepared = .ok raw afterOperands ∧
      materializeOwnedCarriers origin (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
        raw afterOperands = .ok carriers afterMaterialized ∧
      exitChannelCleanupBorrowed origin (borrowedExitChannelReceipts activation initial)
        (exitChannelReservationTokens initial.construction.exitReservations.size prepared) false carriers
        afterMaterialized = .ok () final ∧
      address = ⟨activation.act, .nonlocal targetId⟩ := by
  obtain ⟨activation, target, discarded, outer, declared, stack, included, excluded, occurrence⟩ :=
    returnFrom_escape_operands_origin fuel config environment targetId operands origin initial final address carriers escaped
  have selected := targetActivation_of_nearest_stack config targetId initial activation target discarded outer
    declared stack included excluded
  rcases occurrence with interrupted | ⟨channels, prepared, raw, afterOperands, afterMaterialized,
      setup, evaluated, materialized, released, emitted⟩
  · obtain ⟨channels, prepared, afterOperands, setup, evaluated, canceled⟩ :=
      withExitChannels_escape_origin environment activation operands origin
        (fun channels => evalOperands fuel config environment channels operands) initial final address carriers interrupted
    exact Or.inl ⟨activation, channels, prepared, afterOperands, selected, setup,
      .call reached (.returnFromOperands fuel environment activation targetId operands origin initial prepared channels selected setup),
      evaluated, canceled⟩
  · exact Or.inr ⟨activation, channels, prepared, raw, afterOperands, afterMaterialized, selected, setup,
      .call reached (.returnFromOperands fuel environment activation targetId operands origin initial prepared channels selected setup),
      evaluated, materialized, released, emitted⟩

private theorem reached_returnFromForward_escape_produce (rootFuel fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (targetId : Nat) (producer : Expr) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.statement (fuel + 1) environment (.returnFromForward targetId producer origin)) initial)
    (escaped : execStmt (fuel + 1) config environment (.returnFromForward targetId producer origin) initial =
      .escape address carriers final) :
    ∃ activation channels prepared,
      targetActivation config targetId initial = .ok activation initial ∧
      ExitReached rootFuel config (.produce fuel environment channels producer) prepared ∧
      ((∃ afterOperands,
          evalProduce fuel config environment channels producer prepared = .escape address carriers afterOperands ∧
          exitChannelCleanupBorrowed origin (borrowedExitChannelReceipts activation initial)
            (exitChannelReservationTokens initial.construction.exitReservations.size prepared) true carriers
            afterOperands = .ok () final) ∨
       ∃ raw afterOperands afterMaterialized,
          evalProduce fuel config environment channels producer prepared = .ok raw afterOperands ∧
          materializeOwnedCarriers origin (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
            raw afterOperands = .ok carriers afterMaterialized ∧
          exitChannelCleanupBorrowed origin (borrowedExitChannelReceipts activation initial)
            (exitChannelReservationTokens initial.construction.exitReservations.size prepared) false carriers
            afterMaterialized = .ok () final ∧
          address = ⟨activation.act, .nonlocal targetId⟩) := by
  obtain ⟨activation, target, discarded, outer, selected, declared, stack, included, excluded, occurrence⟩ :=
    returnFromForward_escape_produce_origin fuel config environment targetId producer origin initial final address carriers escaped
  rcases occurrence with ⟨channels, prepared, afterOperands, setup, evaluated, canceled⟩ |
      ⟨channels, prepared, raw, afterOperands, afterMaterialized, setup, evaluated, materialized, released, emitted⟩
  · exact ⟨activation, channels, prepared, selected,
      .call reached (.returnFromForwardProduce fuel environment activation targetId producer origin initial prepared channels selected setup),
      Or.inl ⟨afterOperands, evaluated, canceled⟩⟩
  · exact ⟨activation, channels, prepared, selected,
      .call reached (.returnFromForwardProduce fuel environment activation targetId producer origin initial prepared channels selected setup),
      Or.inr ⟨raw, afterOperands, afterMaterialized, evaluated, materialized, released, emitted⟩⟩

private theorem reached_returnValues_escape_origin (rootFuel fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (operands : List Expr) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.statement (fuel + 1) environment (.retValues operands origin)) initial)
    (escaped : execStmt (fuel + 1) config environment (.retValues operands origin) initial = .escape address carriers final) :
    ∃ activation, enclosingActivation environment initial = .ok activation initial ∧
      ((∃ channels prepared afterOperands,
        ExitReached rootFuel config (.operands fuel environment channels operands) prepared ∧
        evalOperands fuel config environment channels operands prepared = .escape address carriers afterOperands ∧
        exitChannelCleanupBorrowed origin (borrowedExitChannelReceipts activation initial)
          (exitChannelReservationTokens initial.construction.exitReservations.size prepared) true carriers
          afterOperands = .ok () final) ∨
       (withExitChannels environment activation operands origin
         (fun channels => evalOperands fuel config environment channels operands) initial = .ok carriers final ∧
        address = ⟨activation.act, .ordinary⟩)) := by
  obtain ⟨activation, selected, interrupted | emitted⟩ :=
    returnValuesInvocation_escape_inv fuel config environment operands origin initial final address carriers escaped
  · obtain ⟨channels, prepared, afterOperands, setup, evaluated, canceled⟩ :=
      withExitChannels_escape_origin environment activation operands origin
        (fun channels => evalOperands fuel config environment channels operands) initial final address carriers interrupted
    exact ⟨activation, selected, Or.inl ⟨channels, prepared, afterOperands,
      .call reached (.returnOperands fuel environment activation operands origin initial prepared channels selected setup),
      evaluated, canceled⟩⟩
  · exact ⟨activation, selected, Or.inr emitted⟩

private theorem reached_returnForward_escape_origin (rootFuel fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (producer : Expr) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.statement (fuel + 1) environment (.retForward producer origin)) initial)
    (escaped : execStmt (fuel + 1) config environment (.retForward producer origin) initial = .escape address carriers final) :
    ∃ activation, enclosingActivation environment initial = .ok activation initial ∧
      ((∃ channels prepared afterOperands,
        ExitReached rootFuel config (.produce fuel environment channels producer) prepared ∧
        evalProduce fuel config environment channels producer prepared = .escape address carriers afterOperands ∧
        exitChannelCleanupBorrowed origin (borrowedExitChannelReceipts activation initial)
          (exitChannelReservationTokens initial.construction.exitReservations.size prepared) true carriers
          afterOperands = .ok () final) ∨
       (withExitChannels environment activation (List.replicate activation.channels.length producer) origin
         (fun channels => evalProduce fuel config environment channels producer) initial = .ok carriers final ∧
        address = ⟨activation.act, .ordinary⟩)) := by
  obtain ⟨activation, selected, interrupted | emitted⟩ :=
    returnForwardInvocation_escape_inv fuel config environment producer origin initial final address carriers escaped
  · obtain ⟨channels, prepared, afterOperands, setup, evaluated, canceled⟩ :=
      withExitChannels_escape_origin environment activation (List.replicate activation.channels.length producer) origin
        (fun channels => evalProduce fuel config environment channels producer) initial final address carriers interrupted
    exact ⟨activation, selected, Or.inl ⟨channels, prepared, afterOperands,
      .call reached (.returnForwardProduce fuel environment activation producer origin initial prepared channels selected setup),
      evaluated, canceled⟩⟩
  · exact ⟨activation, selected, Or.inr emitted⟩

private theorem reached_breakProduce_escape_origin (rootFuel fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (producer : Expr) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (reached : ExitReached rootFuel config (.statement (fuel + 1) environment (.breakValue producer origin)) initial)
    (escaped : execStmt (fuel + 1) config environment (.breakValue producer origin) initial = .escape address carriers final) :
    ∃ target channels prepared afterOperands,
      currentBreak environment.act (some .block) initial = .ok target initial ∧
      ExitReached rootFuel config (.produce fuel environment channels producer) prepared ∧
      evalProduce fuel config environment channels producer prepared = .escape address carriers afterOperands ∧
      exitChannelCleanupBorrowed origin
        (borrowedExitChannelReceipts { environment with channels := target.channels } initial)
        (exitChannelReservationTokens initial.construction.exitReservations.size prepared) true carriers
        afterOperands = .ok () final := by
  obtain ⟨target, selected, interrupted⟩ :=
    breakProduceInvocation_escape_inv fuel config environment producer origin initial final address carriers escaped
  obtain ⟨channels, prepared, afterOperands, setup, evaluated, canceled⟩ :=
    withExitChannels_escape_origin environment { environment with channels := target.channels }
      _ origin (fun channels => evalProduce fuel config environment channels producer) initial final address carriers interrupted
  exact ⟨target, channels, prepared, afterOperands, selected,
    .call reached (.breakProduce fuel environment target producer origin initial prepared channels selected setup),
    evaluated, canceled⟩

#print axioms reached_returnValues_escape_origin
#print axioms reached_returnForward_escape_origin
#print axioms reached_breakProduce_escape_origin

private inductive StatementExitPath (config : EvalConfig) (environment : RuntimeActivation)
    (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState) :
    Nat → List Stmt → ExecutionState → Prop
  | head (fuel : Nat) (statement : Stmt) (rest : List Stmt) (initial : ExecutionState)
      (escaped : execStmt fuel config environment statement initial = .escape address carriers final) :
      StatementExitPath config environment address carriers final (fuel + 1) (statement :: rest) initial
  | tail (fuel : Nat) (statement : Stmt) (rest : List Stmt)
      (initial middle : ExecutionState) (value : Value)
      (normal : execStmt fuel config environment statement initial = .ok (.normal value) middle)
      (next : StatementExitPath config environment address carriers final fuel rest middle) :
      StatementExitPath config environment address carriers final (fuel + 1) (statement :: rest) initial

private theorem execStmts_escape_path (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (statements : List Stmt)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmts fuel config environment statements initial = .escape address carriers final) :
    StatementExitPath config environment address carriers final fuel statements initial := by
  induction fuel generalizing statements initial with
  | zero => simp only [execStmts, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel previous =>
      cases statements with
      | nil => simp only [execStmts, pure] at escaped; cases escaped
      | cons statement rest =>
          cases evaluated : execStmt fuel config environment statement initial with
          | stop reason after | jump target kind after =>
              simp only [execStmts, bind, evaluated] at escaped
              cases escaped
          | escape target values after =>
              simp only [execStmts, bind, evaluated] at escaped
              cases escaped
              exact .head fuel statement rest initial evaluated
          | ok flow middle =>
              cases flow with
              | normal value =>
                  simp only [execStmts, bind, evaluated] at escaped
                  exact .tail fuel statement rest initial middle value evaluated
                    (previous rest middle escaped)
              | breaking | continuing =>
                  simp only [execStmts, bind, evaluated, pure] at escaped
                  cases escaped

private theorem StatementExitPath.statement
    {config : EvalConfig} {environment : RuntimeActivation}
    {address : ExitAddress} {carriers : List Carrier} {final : ExecutionState}
    {fuel : Nat} {statements : List Stmt} {initial : ExecutionState}
    (path : StatementExitPath config environment address carriers final fuel statements initial) :
    ∃ statementFuel statement before,
      statementFuel < fuel ∧ statement ∈ statements ∧
      execStmt statementFuel config environment statement before = .escape address carriers final := by
  induction path with
  | head fuel statement rest initial escaped =>
      exact ⟨fuel, statement, initial, Nat.lt_succ_self _, by simp, escaped⟩
  | tail fuel statement rest initial middle value normal next previous =>
      obtain ⟨statementFuel, escapedStatement, before, smaller, member, escaped⟩ := previous
      exact ⟨statementFuel, escapedStatement, before,
        Nat.lt_trans smaller (Nat.lt_succ_self _), by simp [member], escaped⟩

private theorem StatementExitPath.sound
    {config : EvalConfig} {environment : RuntimeActivation}
    {address : ExitAddress} {carriers : List Carrier} {final : ExecutionState}
    {fuel : Nat} {statements : List Stmt} {initial : ExecutionState}
    (path : StatementExitPath config environment address carriers final fuel statements initial) :
    execStmts fuel config environment statements initial = .escape address carriers final := by
  induction path with
  | head fuel statement rest initial escaped =>
      simp only [execStmts, bind, escaped]
  | tail fuel statement rest initial middle value normal next previous =>
      simp only [execStmts, bind, normal, previous]

private theorem StatementExitPath.reached_statement
    {config : EvalConfig} {environment : RuntimeActivation}
    {address : ExitAddress} {carriers : List Carrier} {final : ExecutionState}
    {fuel : Nat} {statements : List Stmt} {initial : ExecutionState}
    (path : StatementExitPath config environment address carriers final fuel statements initial)
    (rootFuel : Nat) (reached : ExitReached rootFuel config (.statements fuel environment statements) initial) :
    ∃ statementFuel statement before,
      statementFuel < fuel ∧ statement ∈ statements ∧
      ExitReached rootFuel config (.statement statementFuel environment statement) before ∧
      execStmt statementFuel config environment statement before = .escape address carriers final := by
  induction path with
  | head fuel statement rest initial escaped =>
      exact ⟨fuel, statement, initial, Nat.lt_succ_self _, by simp,
        .call reached (.statementsHead fuel environment statement rest initial), escaped⟩
  | tail fuel statement rest initial middle value normal next previous =>
      obtain ⟨statementFuel, escapedStatement, before, smaller, member, beforeReached, escaped⟩ :=
        previous (.call reached (.statementsTail fuel environment statement rest initial middle value normal))
      exact ⟨statementFuel, escapedStatement, before,
        Nat.lt_trans smaller (Nat.lt_succ_self _), by simp [member], beforeReached, escaped⟩

private theorem StatementExitPath.fresh_statement
    {config : EvalConfig} {environment : RuntimeActivation}
    {address : ExitAddress} {carriers : List Carrier} {final : ExecutionState}
    {fuel : Nat} {statements : List Stmt} {initial : ExecutionState}
    (path : StatementExitPath config environment address carriers final fuel statements initial)
    (fresh : FreshActivations initial) :
    ∃ statementFuel statement before,
      statementFuel < fuel ∧ statement ∈ statements ∧ FreshActivations before ∧
      execStmt statementFuel config environment statement before = .escape address carriers final := by
  induction path with
  | head fuel statement rest initial escaped =>
      exact ⟨fuel, statement, initial, Nat.lt_succ_self _, by simp, fresh, escaped⟩
  | tail fuel statement rest initial middle value normal next previous =>
      have freshMiddle := (evaluation_preservesFresh fuel config).statement environment statement initial fresh
      rw [normal] at freshMiddle
      obtain ⟨statementFuel, escapedStatement, before, smaller, member, freshBefore, escaped⟩ := previous freshMiddle
      exact ⟨statementFuel, escapedStatement, before,
        Nat.lt_trans smaller (Nat.lt_succ_self _), by simp [member], freshBefore, escaped⟩

theorem execStmts_escape_statement (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (statements : List Stmt)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmts fuel config environment statements initial = .escape address carriers final) :
    ∃ statementFuel statement before,
      statementFuel < fuel ∧ statement ∈ statements ∧
      execStmt statementFuel config environment statement before = .escape address carriers final :=
  (execStmts_escape_path fuel config environment statements initial final address carriers escaped).statement

theorem execStmts_escape_fresh_statement (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (statements : List Stmt)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (fresh : FreshActivations initial)
    (escaped : execStmts fuel config environment statements initial = .escape address carriers final) :
    ∃ statementFuel statement before,
      statementFuel < fuel ∧ statement ∈ statements ∧ FreshActivations before ∧
      execStmt statementFuel config environment statement before = .escape address carriers final :=
  (execStmts_escape_path fuel config environment statements initial final address carriers escaped).fresh_statement fresh

#print axioms CallArgumentPrefix.escape_arguments
#print axioms CallActivationPrefix.escape_activation
#print axioms ArgumentValuePrefix.continuation
#print axioms ArgumentValuePrefix.fresh
#print axioms arguments_tail_escape
#print axioms arguments_reference_escape
#print axioms arguments_value_escape
#print axioms arguments_materialize_escape
#print axioms arguments_build_escape
#print axioms operands_head_escape
#print axioms operands_tail_escape
#print axioms reached_operands_escape_call
#print axioms reached_arguments_escape_call
#print axioms block_statements_escape
#print axioms block_value_tail_escape
#print axioms block_produce_tail_escape
#print axioms resultScope_statements_escape
#print axioms resultScope_tail_escape
#print axioms enterActivation_propagates_escape
#print axioms enterActivation_catches_escape
#print axioms execStmts_escape_statement
#print axioms execStmts_escape_fresh_statement
#print axioms runModule_returned_entry
#print axioms reached_block_escape_call
#print axioms StatementExitPath.reached_statement
#print axioms invokeCall_returned_activation
#print axioms enterActivation_returned_body
#print axioms reached_activationScope_escape_call
#print axioms reached_resultScope_escape_call
#print axioms reached_returnFrom_escape_operands
#print axioms ExitReached.fresh
#print axioms runModule_returned_reaches_scope
#print axioms reached_returnFromForward_escape_produce
#print axioms ExitReached.context

end Goose.Proofs.ExitExecution

namespace Goose.Proofs.ExitExecution
open Goose.Construct Goose.Proofs.ConstructionExecutionOwnership

private theorem projection_of_normal (action : EvalM α) (initial final : ExecutionState) (value : α)
    (normal : action initial = .ok value final) (fresh : FreshActivations initial)
    (preserved : PreservesActivationChannels action) :
    ActivationChannelsProjection final = ActivationChannelsProjection initial := by
  have after := preserved initial fresh
  simpa only [normal, ActivationChannelsOutcome] using after

private theorem CallArgumentPrefix.projection
    {config : EvalConfig} {context : Goose.Core.ContextId} {channels : List Channel} {origin : Goose.Core.OriginId}
    {initial prepared : ExecutionState} {id : Goose.Core.ImplId} {implementation : Impl} {firstChannels : List Channel}
    (receiving : CallArgumentPrefix config context channels origin initial id implementation firstChannels prepared)
    (fresh : FreshActivations initial) : ActivationChannelsProjection prepared = ActivationChannelsProjection initial := by
  cases receiving
  rename_i lookupState arity lookup receiving
  have previousFresh := evaluation_preservesFresh 0 config
  have previousChannels := evaluationActivationChannels_zero config
  have lookupFresh := fresh_of_normal _ _ _ _ lookup fresh
    (stateQuery_preservesFresh _ (stateQuery_getImplementation config context))
  have lookupProjection := projection_of_normal _ _ _ _ lookup fresh
    (preservesActivationChannels_of_stateQuery _ (stateQuery_getImplementation config context))
  have receivingProjection := projection_of_normal _ _ _ _ receiving lookupFresh
    (by activation_channels_eval previousFresh previousChannels)
  exact receivingProjection.trans lookupProjection

private theorem CallActivationPrefix.projection
    {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {context : Goose.Core.ContextId} {arguments : List Arg} {channels : List Channel} {origin : Goose.Core.OriginId}
    {initial entered : ExecutionState} {activation : RuntimeActivation} {pre : List (Goose.Core.VarId × Value)} {body : Block}
    (prepared : CallActivationPrefix fuel config environment context arguments channels origin initial activation pre body entered)
    (fresh : FreshActivations initial) (previousChannels : EvaluationActivationChannels fuel config) :
    ActivationChannelsProjection entered = ownershipActivationChannels activation :: ActivationChannelsProjection initial := by
  cases prepared with
  | actual firstState argumentState ready id implementation firstChannels renewed values
      receiving argumentsDone renewal depth =>
      have previousFresh := evaluation_preservesFresh fuel config
      have firstFresh := receiving.fresh fresh
      have firstProjection := receiving.projection fresh
      have argumentProjection := projection_of_normal _ _ _ _ argumentsDone firstFresh (previousChannels.arguments _ _ _ _)
      have argumentFresh := fresh_of_normal _ _ _ _ argumentsDone firstFresh (previousFresh.arguments _ _ _ _)
      have readyProjection := projection_of_normal _ _ _ _ renewal argumentFresh
        (by activation_channels_eval previousFresh previousChannels)
      change _ :: ActivationChannelsProjection ready = _ :: ActivationChannelsProjection initial
      rw [readyProjection, argumentProjection, firstProjection]

#print axioms CallArgumentPrefix.projection
#print axioms CallActivationPrefix.projection

private theorem projection_scope_prepared (environment : RuntimeActivation) (scope : Nat)
    (initial : ExecutionState) :
    ActivationChannelsProjection { initial with
      nextScope := initial.nextScope + 1
      activations := initial.activations.map (fun current => if current.act == environment.act then
        { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } =
      ActivationChannelsProjection initial := by
  apply activationChannelsProjection_map { initial with nextScope := initial.nextScope + 1 }
  intro activation
  split <;> rfl

def ExitLexicalFrame.projectedHandler : ExitLexicalFrame → Option OwnershipActivationChannels
  | .handler activation _ _ => some (ownershipActivationChannels activation)
  | _ => none

def ExitInvocation.handlerProjection (invocation : ExitInvocation α) (context : List ExitLexicalFrame) :
    List OwnershipActivationChannels :=
  match invocation with
  | .activation _ activeEnvironment _ _ _ =>
      ownershipActivationChannels activeEnvironment :: context.filterMap ExitLexicalFrame.projectedHandler
  | _ => context.filterMap ExitLexicalFrame.projectedHandler

private def ExitRuntimeFrame (context : List ExitLexicalFrame) (invocation : ExitInvocation α)
    (state : ExecutionState) : Prop :=
  ActivationChannelsProjection state = invocation.handlerProjection context

private theorem ExitInvocation.frames_handlers {config : EvalConfig} {α : Type}
    {caller : ExitInvocation α} {initial middle : ExecutionState} {outer inner : List ExitLexicalFrame}
    (frames : caller.frames config initial middle outer inner) :
    inner.filterMap ExitLexicalFrame.projectedHandler = caller.handlerProjection outer := by
  cases caller
  all_goals dsimp only [ExitInvocation.frames, ExitInvocation.handlerProjection] at frames ⊢
  all_goals first | (subst inner; rfl) | (rcases frames with ⟨_, _, rfl⟩; rfl) | skip
  case activationScope fuel environment pre body =>
    cases body
    dsimp only at frames
    subst inner
    rfl
  case resultScope fuel environment pre channels body =>
    cases body
    dsimp only at frames
    subst inner
    rfl
  case block fuel environment pre channels body =>
    cases body
    dsimp only at frames
    subst inner
    rfl
  case produce fuel environment incoming expression =>
    cases expression <;> try dsimp only at frames
    all_goals first | (subst inner; rfl) | (rcases frames with ⟨_, _, _, _, rfl⟩; rfl)
  case build fuel environment incoming expression =>
    rcases frames with ⟨_, _, _, rfl⟩
    cases expression <;> rfl
  case statement fuel environment statement =>
    cases statement <;> try dsimp only at frames
    all_goals first | (subst inner; rfl) | (rcases frames with ⟨_, _, rfl⟩; rfl) | skip
    case ret expression origin =>
      cases expression <;> try dsimp only at frames
      all_goals first | (subst inner; rfl) | (rcases frames with ⟨_, _, rfl⟩; rfl)

private theorem ValueInvocationEdge.child_handlers {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {child : ExitInvocation β} {initial prepared : ExecutionState}
    (site : ValueInvocationEdge config caller initial child prepared) (context : List ExitLexicalFrame) :
    child.handlerProjection context = context.filterMap ExitLexicalFrame.projectedHandler := by
  cases site <;> rfl

private theorem ProducerInvocationChild.child_handlers {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {child : ExitInvocation β} {initial prepared : ExecutionState}
    (site : ProducerInvocationChild config caller initial child prepared) (context : List ExitLexicalFrame) :
    child.handlerProjection context = context.filterMap ExitLexicalFrame.projectedHandler := by
  cases site
  case produce receiving body => cases body <;> rfl
  case build renewed body => cases body <;> rfl
  all_goals rfl

private theorem StatementInvocationEdge.child_handlers {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {child : ExitInvocation β} {initial prepared : ExecutionState}
    (site : StatementInvocationEdge config caller initial child prepared) (context : List ExitLexicalFrame) :
    child.handlerProjection context = context.filterMap ExitLexicalFrame.projectedHandler := by
  cases site <;> rfl

private theorem ArgumentValuePrefix.projection {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {vars : Array LocalVar} {parameter : Param} {argument : Arg} {initial final : ExecutionState} {value : Value}
    (prefixResult : ArgumentValuePrefix fuel config environment vars parameter argument initial value final)
    (fresh : FreshActivations initial) : ActivationChannelsProjection final = ActivationChannelsProjection initial := by
  have previousFresh := evaluation_preservesFresh fuel config
  have previous := evaluationActivationChannels fuel config
  cases prefixResult
  case reference =>
    exact projection_of_normal (evalPlace fuel config environment _) initial final _ (by assumption) fresh (previous.place _ _)
  case value =>
    exact projection_of_normal (evalValue fuel config environment _) initial final _ (by assumption) fresh (previous.value _ _)
  case materialized =>
    have evaluatedFresh := fresh_of_normal (materializeProducer fuel _ _ (evalValue fuel config environment _)) initial _ _
      (by assumption) fresh (preservesFresh_materializeProducer _ _ _ _ (previousFresh.value _ _))
    have evaluatedProjection := projection_of_normal (materializeProducer fuel _ _ (evalValue fuel config environment _)) initial _ _
      (by assumption) fresh (preservesActivationChannels_materializeProducer config _ _ _ _ (previous.value _ _) (previousFresh.value _ _))
    have storedFresh := fresh_of_normal (materializedDestination _ _ _ _ _ _ _) _ _ _
      (by assumption) evaluatedFresh (preservesFresh_materializedDestination _ _ _ _ _ _ _)
    have storedProjection := projection_of_normal (materializedDestination _ _ _ _ _ _ _) _ _ _
      (by assumption) evaluatedFresh (preservesActivationChannels_materializedDestination config _ _ _ _ _ _ _)
    have publishedFresh := fresh_of_normal (publishCarriers _ _) _ _ _ (by assumption) storedFresh (preservesFresh_publishCarriers _ _)
    have publishedProjection := projection_of_normal (publishCarriers _ _) _ _ _ (by assumption) storedFresh (preservesActivationChannels_publishCarriers _ _)
    have convertedProjection := projection_of_normal (carrierValue _) _ final _ (by assumption) publishedFresh
      (preservesActivationChannels_of_stateQuery _ (stateQuery_carrierValue _))
    exact convertedProjection.trans (publishedProjection.trans (storedProjection.trans evaluatedProjection))
  case constructed =>
    have evaluatedFresh := fresh_of_normal (materializeProducer fuel _ _ (evalValue fuel config environment _)) initial _ _
      (by assumption) fresh (preservesFresh_materializeProducer _ _ _ _ (previousFresh.value _ _))
    have evaluatedProjection := projection_of_normal (materializeProducer fuel _ _ (evalValue fuel config environment _)) initial _ _
      (by assumption) fresh (preservesActivationChannels_materializeProducer config _ _ _ _ (previous.value _ _) (previousFresh.value _ _))
    have constructedFresh := fresh_of_normal (constructLocal _ _ _ _ _ _) _ _ _ (by assumption) evaluatedFresh
      (preservesFresh_constructLocal _ _ _ _ _ _ (fun destination => previousFresh.build _ _ _))
    have constructedProjection := projection_of_normal (constructLocal _ _ _ _ _ _) _ _ _ (by assumption) evaluatedFresh
      (preservesActivationChannels_constructLocal _ _ _ _ _ _ (fun destination => previous.build _ _ _) (fun destination => previousFresh.build _ _ _))
    have convertedProjection := projection_of_normal (carrierValue _) _ final _ (by assumption) constructedFresh
      (preservesActivationChannels_of_stateQuery _ (stateQuery_carrierValue _))
    exact convertedProjection.trans (constructedProjection.trans evaluatedProjection)

private theorem ExitCallSite.runtime {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {callee : ExitInvocation β} {initial middle : ExecutionState}
    {outer inner : List ExitLexicalFrame}
    (site : ExitCallSite config caller initial callee middle) (frames : site.frames outer inner)
    (fresh : FreshActivations initial) (runtime : ExitRuntimeFrame outer caller initial) :
    ExitRuntimeFrame inner callee middle := by
  have evaluation := fun fuel => evaluationActivationChannels fuel config
  have globalInitializers := fun fuel globals => initGlobals_activationChannels fuel config globals
  cases site
  case values edge =>
    have projected := (ValueInvocationEdge.transport (fun fuel => evaluation_preservesFresh fuel config) evaluation edge fresh).2
    have handlers := ExitInvocation.frames_handlers frames
    change ActivationChannelsProjection middle = callee.handlerProjection inner
    rw [edge.child_handlers inner]
    exact projected.trans (runtime.trans handlers.symm)
  case producer edge =>
    have projected := edge.channels (fun fuel => evaluation_preservesFresh fuel config) evaluation fresh
    have handlers := ExitInvocation.frames_handlers frames
    change ActivationChannelsProjection middle = callee.handlerProjection inner
    rw [edge.child_handlers inner]
    exact projected.trans (runtime.trans handlers.symm)
  case statements edge =>
    have projected := edge.channels config (fun fuel => evaluation_preservesFresh fuel config) evaluation fresh
    have handlers := ExitInvocation.frames_handlers frames
    change ActivationChannelsProjection middle = callee.handlerProjection inner
    rw [edge.child_handlers inner]
    exact projected.trans (runtime.trans handlers.symm)
  all_goals dsimp only [ExitCallSite.frames, ExitInvocation.frames] at frames
  all_goals first | (rcases frames with ⟨_, _, rfl⟩) | subst inner
  all_goals simp only [ExitRuntimeFrame, ExitInvocation.handlerProjection, List.filterMap_cons,
    ExitLexicalFrame.projectedHandler] at runtime ⊢
  case moduleGlobals | activationBody | activationScope | resultBlockWith | resultScope | statementsHead | operandsHead | argumentReference | argumentValue | argumentMaterialize =>
    exact runtime
  case moduleEntry =>
    rename_i lookup globals receiving
    have globalsFresh := fresh_of_normal _ _ _ _ globals fresh (initGlobals_preservesFresh _ _ _)
    have globalsProjection := projection_of_normal _ _ _ _ globals fresh (globalInitializers _ _)
    have lookupFresh := fresh_of_normal _ _ _ _ lookup globalsFresh
      (stateQuery_preservesFresh _ (stateQuery_getImplementation _ _))
    have lookupProjection := projection_of_normal _ _ _ _ lookup globalsFresh
      (preservesActivationChannels_of_stateQuery _ (stateQuery_getImplementation _ _))
    have receivingProjection := projection_of_normal _ _ _ _ receiving lookupFresh (preservesActivationChannels_channelsFor _ _ _ _)
    exact receivingProjection.trans (lookupProjection.trans (globalsProjection.trans runtime))
  case callActivation =>
    rename_i prepared
    have projected := prepared.projection fresh (evaluation _)
    rw [runtime] at projected
    exact projected
  case callArguments =>
    rename_i receiving
    exact (receiving.projection fresh).trans runtime
  case argumentsTail =>
    rename_i normal
    exact (normal.projection fresh).trans runtime
  case completionProduce =>
    rename_i setup
    unfold CompletionPreparation at setup
    apply Eq.trans (b := ActivationChannelsProjection initial) ?_ runtime
    apply projection_of_normal _ _ _ _ setup fresh
    have previousFresh := evaluation_preservesFresh 0 config
    have previousChannels := evaluation 0
    activation_channels_eval previousFresh previousChannels
  case argumentBuild =>
    exact (projection_of_normal _ _ _ _ (by assumption) fresh
      (preservesActivationChannels_newDestination _ _ _ _ _ _ _)).trans runtime
  case operandsTail =>
    rename_i producedNormally selected
    have producedFresh := fresh_of_normal _ _ _ _ producedNormally fresh ((evaluation_preservesFresh _ config).produce _ _ _)
    have producedProjection := projection_of_normal _ _ _ _ producedNormally fresh ((evaluation _).produce _ _ _)
    have selectedProjection := projection_of_normal _ _ _ _ selected producedFresh
      (preservesActivationChannels_of_stateQuery _ (stateQuery_singleCarrier _))
    exact selectedProjection.trans (producedProjection.trans runtime)
  case statementsTail =>
    rename_i normal
    exact (projection_of_normal _ _ _ _ normal fresh ((evaluation _).statement _ _)).trans runtime
  case blockStatements =>
    rename_i binding
    exact (projection_of_normal _ _ _ _ binding fresh (preservesActivationChannels_bindAll config _ _ _)).trans runtime
  case blockValueTail | blockProduceTail =>
    rename_i branch binding normal
    have boundFresh := fresh_of_normal _ _ _ _ binding fresh (preservesFresh_bindAll _ _ _)
    have boundProjection := projection_of_normal _ _ _ _ binding fresh (preservesActivationChannels_bindAll config _ _ _)
    have statementProjection := projection_of_normal _ _ _ _ normal boundFresh ((evaluation _).statements _ _)
    exact statementProjection.trans (boundProjection.trans runtime)
  case activationStatements | resultStatements =>
    rename_i binding
    have boundProjection := projection_of_normal _ _ _ _ binding (fresh_scope_prepared _ _ _ fresh)
      (preservesActivationChannels_bindAll config _ _ _)
    exact boundProjection.trans ((projection_scope_prepared _ _ _).trans runtime)
  case activationTail | resultTail =>
    rename_i binding normal
    have boundFresh := fresh_of_normal _ _ _ _ binding (fresh_scope_prepared _ _ _ fresh) (preservesFresh_bindAll _ _ _)
    have boundProjection := projection_of_normal _ _ _ _ binding (fresh_scope_prepared _ _ _ fresh)
      (preservesActivationChannels_bindAll config _ _ _)
    have statementProjection := projection_of_normal _ _ _ _ normal boundFresh ((evaluation _).statements _ _)
    exact statementProjection.trans (boundProjection.trans ((projection_scope_prepared _ _ _).trans runtime))
  case returnFromOperands | returnFromForwardProduce | returnOperands | returnForwardProduce | returnProduce | breakProduce =>
    exact (projection_of_normal (exitChannels _ _ _ _) initial middle _ (by assumption) fresh
      (preservesActivationChannels_exitChannels config _ _ _ _)).trans runtime

#print axioms ExitCallSite.runtime

private theorem ExitContextReached.reached {fuel : Nat} {config : EvalConfig} {α : Type}
    {context : List ExitLexicalFrame} {invocation : ExitInvocation α} {state : ExecutionState}
    (reached : ExitContextReached fuel config context invocation state) :
    ExitReached fuel config invocation state := by
  induction reached with
  | initial => exact .initial
  | call callerReached site frames previous => exact .call previous site

theorem ExitContextReached.runtime {fuel : Nat} {config : EvalConfig} {α : Type}
    {context : List ExitLexicalFrame} {invocation : ExitInvocation α} {state : ExecutionState}
    (reached : ExitContextReached fuel config context invocation state) :
    ExitRuntimeFrame context invocation state := by
  induction reached with
  | initial => rfl
  | call callerReached site frames previous =>
      exact site.runtime frames callerReached.reached.fresh previous

private theorem ExitContextReached.selected_handler {rootFuel fuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {environment : RuntimeActivation} {statement : Stmt} {initial : ExecutionState}
    (reached : ExitContextReached rootFuel config context (.statement fuel environment statement) initial)
    (targetId : Nat) (activation : RuntimeActivation) (final : ExecutionState)
    (selected : targetActivation config targetId initial = .ok activation final) :
    ∃ target handler resultTypes origin discarded outer,
      final = initial ∧
      config.module.targets[targetId]? = some target ∧
      context = discarded ++ .handler handler resultTypes origin :: outer ∧
      ownershipActivationChannels handler = ownershipActivationChannels activation ∧
      target.contains handler.implementation = true ∧
      ∀ earlier ∈ discarded,
        (earlier.projectedHandler).any (fun current => target.contains current.implementation) = false := by
  obtain ⟨unchanged, target, runtimeDiscarded, runtimeOuter, declared, stack, included, excluded⟩ :=
    targetActivation_selects_nearest config targetId initial final activation selected
  have runtime := reached.runtime
  change ActivationChannelsProjection initial = context.filterMap ExitLexicalFrame.projectedHandler at runtime
  have found : selectTarget? target initial.activations = some activation := by
    change initial.activations.find? (fun current => target.contains current.implementation) = some activation
    apply List.find?_eq_some_iff_append.mpr
    refine ⟨included, runtimeDiscarded, runtimeOuter, stack, ?_⟩
    intro earlier member
    simp only [excluded earlier member, Bool.not_false]
  have projected : (ActivationChannelsProjection initial).find? (fun current => target.contains current.implementation) =
      some (ownershipActivationChannels activation) := by
    simp only [ActivationChannelsProjection, List.find?_map]
    simpa only [Function.comp_def, ownershipActivationChannels, selectTarget?, Option.map_some] using
      congrArg (Option.map ownershipActivationChannels) found
  rw [runtime, List.find?_filterMap] at projected
  cases fullFound : context.find? (fun frame => (frame.projectedHandler).any (fun current => target.contains current.implementation)) with
  | none =>
      simp only [fullFound, Option.bind_none] at projected
      cases projected
  | some frame =>
      simp only [fullFound, Option.bind_some] at projected
      cases frame with
      | scope scopeEnvironment scope scopeInst | exitChannels origin borrowed tokens => cases projected
      | breakTarget target => cases projected
      | receivingDestination origin destination => cases projected
      | handler handler resultTypes origin =>
          change some (ownershipActivationChannels handler) = some (ownershipActivationChannels activation) at projected
          have same := Option.some.inj projected
          obtain ⟨member, discarded, outer, shape, earlier⟩ := List.find?_eq_some_iff_append.mp fullFound
          refine ⟨target, handler, resultTypes, origin, discarded, outer, unchanged, declared, shape, same, ?_, ?_⟩
          · simpa only [ExitLexicalFrame.projectedHandler, Option.any_some, ownershipActivationChannels] using member
          · intro frame present
            have absent := earlier frame present
            simpa only [Bool.not_eq_true'] using absent

#print axioms ExitContextReached.runtime
#print axioms ExitContextReached.selected_handler

private theorem targetActivation_projection_transport (config : EvalConfig) (targetId : Nat)
    (before after : ExecutionState) (activation : RuntimeActivation)
    (same : ActivationChannelsProjection after = ActivationChannelsProjection before)
    (selected : targetActivation config targetId before = .ok activation before) :
    ∃ current, targetActivation config targetId after = .ok current after ∧
      ownershipActivationChannels current = ownershipActivationChannels activation := by
  obtain ⟨unchanged, target, discarded, outer, declared, stack, included, excluded⟩ :=
    targetActivation_selects_nearest config targetId before before activation selected
  have found : selectTarget? target before.activations = some activation := by
    change before.activations.find? (fun current => target.contains current.implementation) = some activation
    apply List.find?_eq_some_iff_append.mpr
    refine ⟨included, discarded, outer, stack, ?_⟩
    intro earlier member
    simp only [excluded earlier member, Bool.not_false]
  have projected : (ActivationChannelsProjection before).find? (fun current => target.contains current.implementation) =
      some (ownershipActivationChannels activation) := by
    rw [ActivationChannelsProjection, List.find?_map]
    change (selectTarget? target before.activations).map ownershipActivationChannels = some (ownershipActivationChannels activation)
    rw [found]
    rfl
  rw [← same, ActivationChannelsProjection, List.find?_map] at projected
  change (selectTarget? target after.activations).map ownershipActivationChannels = some (ownershipActivationChannels activation) at projected
  cases currentFound : selectTarget? target after.activations with
  | none => simp only [currentFound, Option.map_none] at projected; cases projected
  | some current =>
      simp only [currentFound, Option.map_some] at projected
      exact ⟨current, Goose.Proofs.Exit.target_activation_success config targetId target current after declared currentFound,
        Option.some.inj projected⟩

private theorem operands_preserve_selected_target (fuel : Nat) (config : EvalConfig)
    (environment activation : RuntimeActivation)
    (targetId : Nat) (operands : List Expr) (origin : Goose.Core.OriginId)
    (initial prepared afterOperands : ExecutionState) (channels : List Channel) (raw : List Carrier)
    (fresh : FreshActivations initial)
    (selected : targetActivation config targetId initial = .ok activation initial)
    (setup : exitChannels environment activation operands origin initial = .ok channels prepared)
    (evaluated : evalOperands fuel config environment channels operands prepared = .ok raw afterOperands) :
    ∃ current, targetActivation config targetId afterOperands = .ok current afterOperands ∧
      ownershipActivationChannels current = ownershipActivationChannels activation := by
  have previous := evaluationActivationChannels fuel config
  have preparedProjection := projection_of_normal _ _ _ _ setup fresh (preservesActivationChannels_exitChannels config _ _ _ _)
  have preparedFresh := fresh_of_normal _ _ _ _ setup fresh (preservesFresh_exitChannels _ _ _ _)
  have afterProjection := projection_of_normal _ _ _ _ evaluated preparedFresh (previous.operands _ _ _)
  exact targetActivation_projection_transport config targetId initial afterOperands activation
    (afterProjection.trans preparedProjection) selected

#print axioms targetActivation_projection_transport
#print axioms operands_preserve_selected_target

private theorem ExitContextReached.handler_ids {rootFuel fuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {environment : RuntimeActivation} {statement : Stmt} {initial : ExecutionState}
    (reached : ExitContextReached rootFuel config context (.statement fuel environment statement) initial) :
    ((context.filterMap ExitLexicalFrame.projectedHandler).map (·.act)).Nodup := by
  have runtime := reached.runtime
  change ActivationChannelsProjection initial = context.filterMap ExitLexicalFrame.projectedHandler at runtime
  rw [← runtime]
  have distinct := reached.reached.fresh.1
  simpa only [ActivationChannelsProjection, List.map_map, Function.comp_def, ownershipActivationChannels] using distinct

private theorem lexical_handler_prefix_distinct (discarded outer : List ExitLexicalFrame)
    (handler : RuntimeActivation) (resultTypes : List Ty) (origin : Goose.Core.OriginId)
    (distinct : (((discarded ++ .handler handler resultTypes origin :: outer).filterMap
      ExitLexicalFrame.projectedHandler).map (·.act)).Nodup) :
    ∀ frame ∈ discarded, ∀ earlier,
      frame.projectedHandler = some earlier → earlier.act ≠ handler.act := by
  simp only [List.filterMap_append, List.filterMap_cons, ExitLexicalFrame.projectedHandler,
    List.map_append, List.map_cons, ownershipActivationChannels] at distinct
  have apart := (List.nodup_append.mp distinct).2.2
  intro frame present earlier projected
  have retained : earlier ∈ discarded.filterMap ExitLexicalFrame.projectedHandler :=
    List.mem_filterMap.mpr ⟨frame, present, projected⟩
  exact apart earlier.act (List.mem_map.mpr ⟨earlier, retained, rfl⟩) handler.act (by simp)

#print axioms ExitContextReached.handler_ids
#print axioms lexical_handler_prefix_distinct

private theorem exitCleanup_normal_frame (origin : Goose.Core.OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List Nat) (cancel : Bool) (carriers : List Carrier)
    (initial final : ExecutionState)
    (cleaned : exitChannelCleanupBorrowed origin borrowed tokens cancel carriers initial = .ok () final) :
    final.construction.stdout = initial.construction.stdout ∧ final.objects = initial.objects := by
  have stdout := exitChannelCleanupBorrowed_stdout origin borrowed tokens cancel carriers initial
  have objects := exitChannelCleanupBorrowed_objects origin borrowed tokens cancel carriers initial
  rw [cleaned] at stdout objects
  exact ⟨stdout, objects⟩

private theorem exitDelivery_normal_frame (origin : Goose.Core.OriginId)
    (borrowed : List BorrowedWaitingExitReservation) (tokens : List Nat) (raw carriers : List Carrier)
    (initial materializedState final : ExecutionState)
    (materialized : materializeOwnedCarriers origin tokens raw initial = .ok carriers materializedState)
    (cleaned : exitChannelCleanupBorrowed origin borrowed tokens false carriers materializedState = .ok () final) :
    final.construction.stdout = initial.construction.stdout ∧ final.objects = initial.objects := by
  have stdout := materializeOwnedCarriers_stdout origin tokens raw initial
  have objects := materializeOwnedCarriers_objects origin tokens raw initial
  rw [materialized] at stdout objects
  obtain ⟨cleanupStdout, cleanupObjects⟩ :=
    exitCleanup_normal_frame origin borrowed tokens false carriers materializedState final cleaned
  exact ⟨cleanupStdout.trans stdout, cleanupObjects.trans objects⟩

#print axioms exitDelivery_normal_frame

private theorem ExitContextReached.returnFrom_escape_nearest {rootFuel fuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {environment : RuntimeActivation} {targetId : Nat}
    {operands : List Expr} {origin : Goose.Core.OriginId} {initial final : ExecutionState}
    {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitContextReached rootFuel config context
      (.statement (fuel + 1) environment (.returnFrom targetId operands origin)) initial)
    (escaped : execStmt (fuel + 1) config environment (.returnFrom targetId operands origin) initial =
      .escape address carriers final) :
    (∃ channels prepared afterOperands,
      ExitReached rootFuel config (.operands fuel environment channels operands) prepared ∧
      evalOperands fuel config environment channels operands prepared = .escape address carriers afterOperands ∧
      final.construction.stdout = afterOperands.construction.stdout ∧ final.objects = afterOperands.objects) ∨
    ∃ activation channels prepared raw afterOperands afterMaterialized target handler resultTypes handlerOrigin discarded outer current enteredFuel pre body enteredState implementation emittedCurrent,
      targetActivation config targetId initial = .ok activation initial ∧
      exitChannels environment activation operands origin initial = .ok channels prepared ∧
      ExitReached rootFuel config (.operands fuel environment channels operands) prepared ∧
      evalOperands fuel config environment channels operands prepared = .ok raw afterOperands ∧
      materializeOwnedCarriers origin (exitChannelReservationTokens initial.construction.exitReservations.size prepared)
        raw afterOperands = .ok carriers afterMaterialized ∧
      exitChannelCleanupBorrowed origin (borrowedExitChannelReceipts activation initial)
        (exitChannelReservationTokens initial.construction.exitReservations.size prepared) false carriers
        afterMaterialized = .ok () final ∧
      address = ⟨activation.act, .nonlocal targetId⟩ ∧
      config.module.targets[targetId]? = some target ∧
      context = discarded ++ .handler handler resultTypes handlerOrigin :: outer ∧
      ownershipActivationChannels handler = ownershipActivationChannels activation ∧
      target.contains handler.implementation = true ∧
      (∀ earlier ∈ discarded,
        earlier.projectedHandler.any (fun candidate => target.contains candidate.implementation) = false) ∧
      targetActivation config targetId afterOperands = .ok current afterOperands ∧
      ownershipActivationChannels current = ownershipActivationChannels handler ∧
      (∀ frame ∈ discarded, ∀ earlier, frame.projectedHandler = some earlier → earlier.act ≠ handler.act) ∧
      ExitReached rootFuel config (.activation (enteredFuel + 1) handler pre body handlerOrigin) enteredState ∧
      config.module.impls[handler.implementation]? = some implementation ∧
      resultTypes = implementation.results.toList.map (·.ty) ∧
      final.construction.stdout = afterOperands.construction.stdout ∧ final.objects = afterOperands.objects ∧
      targetActivation config targetId final = .ok emittedCurrent final ∧
      ownershipActivationChannels emittedCurrent = ownershipActivationChannels handler ∧
      address.activation = handler.act := by
  rcases reached_returnFrom_escape_operands rootFuel fuel config environment targetId operands origin initial final
      address carriers reached.reached escaped with
    ⟨activation, channels, prepared, afterOperands, selected, setup, childReached, evaluated, canceled⟩ |
    ⟨activation, channels, prepared, raw, afterOperands, afterMaterialized,
      selected, setup, childReached, evaluated, materialized, cleaned, emitted⟩
  · obtain ⟨stdout, objects⟩ := exitCleanup_normal_frame origin (borrowedExitChannelReceipts activation initial)
      (exitChannelReservationTokens initial.construction.exitReservations.size prepared) true carriers afterOperands final canceled
    exact Or.inl ⟨channels, prepared, afterOperands, childReached, evaluated, stdout, objects⟩
  · obtain ⟨target, handler, resultTypes, handlerOrigin, discarded, outer,
        unchanged, declared, shape, same, included, excluded⟩ := reached.selected_handler targetId activation initial selected
    obtain ⟨current, selectedAfter, sameAfter⟩ := operands_preserve_selected_target fuel config environment activation
      targetId operands origin initial prepared afterOperands channels raw reached.reached.fresh selected setup evaluated
    have distinct := reached.handler_ids
    rw [shape] at distinct
    have apart := lexical_handler_prefix_distinct discarded outer handler resultTypes handlerOrigin distinct
    have handlerMember : ExitLexicalFrame.handler handler resultTypes handlerOrigin ∈ context := by
      rw [shape]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    obtain ⟨enteredFuel, pre, body, enteredState, implementation, entered, lookup, results⟩ :=
      reached.handler_entered handler resultTypes handlerOrigin handlerMember
    obtain ⟨stdout, objects⟩ := exitDelivery_normal_frame origin (borrowedExitChannelReceipts activation initial)
      (exitChannelReservationTokens initial.construction.exitReservations.size prepared) raw carriers
      afterOperands afterMaterialized final materialized cleaned
    have emittedProjection := (evaluationActivationChannels (fuel + 1) config).statement environment
      (.returnFrom targetId operands origin) initial reached.reached.fresh
    rw [escaped] at emittedProjection
    change ActivationChannelsProjection final = ActivationChannelsProjection initial at emittedProjection
    obtain ⟨emittedCurrent, emittedSelected, emittedSame⟩ :=
      targetActivation_projection_transport config targetId initial final activation emittedProjection selected
    have sameId : handler.act = activation.act := congrArg (fun current : OwnershipActivationChannels => current.act) same
    have addressId : address.activation = handler.act := by
      rw [emitted]
      exact sameId.symm
    exact Or.inr ⟨activation, channels, prepared, raw, afterOperands, afterMaterialized,
      target, handler, resultTypes, handlerOrigin, discarded, outer, current, enteredFuel, pre, body, enteredState, implementation, emittedCurrent, selected, setup,
      childReached, evaluated, materialized, cleaned, emitted, declared, shape, same, included, excluded,
      selectedAfter, sameAfter.trans same.symm, apart, entered, lookup, results, stdout, objects, emittedSelected, emittedSame.trans same.symm, addressId⟩

#print axioms ExitContextReached.returnFrom_escape_nearest

end Goose.Proofs.ExitExecution

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

private def handlersMiss (address : ExitAddress) (context : List ExitLexicalFrame) : Prop :=
  ∀ handler ∈ context.filterMap ExitLexicalFrame.projectedHandler, handler.act ≠ address.activation

private theorem escaping_handlerProjection {config : EvalConfig} {α : Type}
    {caller : ExitInvocation α} {initial final : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    {context : List ExitLexicalFrame}
    (escaped : caller.action config initial = .escape address carriers final)
    (misses : handlersMiss address context) :
    ∀ handler ∈ caller.handlerProjection context, handler.act ≠ address.activation := by
  cases caller
  all_goals try exact misses
  case activation fuel activation pre body origin =>
    have different : activation.act ≠ address.activation := by
      cases fuel with
      | zero =>
          simp only [ExitInvocation.action, enterActivation, timeout, EvalM.stop] at escaped
          cases escaped
      | succ fuel =>
          obtain ⟨implementation, before, lookup, evaluated, different, released⟩ :=
            enterActivation_escape_origin fuel config activation pre body origin initial final address carriers escaped
          exact different.symm
    intro handler member
    rcases List.mem_cons.mp member with same | member
    · subst handler
      exact different
    · exact misses handler member

private theorem ExitCallSite.escape_handlersMiss {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {child : ExitInvocation β} {initial prepared final : ExecutionState}
    {address : ExitAddress} {carriers : List Carrier} {outer inner : List ExitLexicalFrame}
    (site : ExitCallSite config caller initial child prepared) (frames : site.frames outer inner)
    (escaped : caller.action config initial = .escape address carriers final)
    (misses : handlersMiss address outer) : handlersMiss address inner := by
  change ∀ handler ∈ inner.filterMap ExitLexicalFrame.projectedHandler, handler.act ≠ address.activation
  rw [ExitInvocation.frames_handlers frames]
  exact escaping_handlerProjection escaped misses

#print axioms ExitCallSite.escape_handlersMiss
end Goose.Proofs.ExitExecution

namespace Goose.Proofs.ExitExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership

private def EscapingSourceChild (config : EvalConfig) {α : Type}
    (caller : ExitInvocation α) (initial : ExecutionState) (address : ExitAddress)
    (carriers : List Carrier) : Prop :=
  ∃ (β : Type) (child : ExitInvocation β) (prepared before : ExecutionState),
    ExitCallSite config caller initial child prepared ∧
    child.action config prepared = .escape address carriers before

private theorem ExitContextReached.selected_not_missing {rootFuel fuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {environment activation : RuntimeActivation} {statement : Stmt}
    {initial : ExecutionState} {address : ExitAddress}
    (reached : ExitContextReached rootFuel config context (.statement fuel environment statement) initial)
    (target : Nat) (selected : targetActivation config target initial = .ok activation initial)
    (misses : handlersMiss address context) : activation.act ≠ address.activation := by
  obtain ⟨targetSet, handler, results, origin, discarded, outer,
    unchanged, declared, shape, same, included, excluded⟩ := reached.selected_handler target activation initial selected
  have member : ownershipActivationChannels handler ∈ context.filterMap ExitLexicalFrame.projectedHandler := by
    rw [shape, List.filterMap_append]
    simp only [List.filterMap_cons, ExitLexicalFrame.projectedHandler, List.mem_append, List.mem_cons,
      true_or, or_true]
  have different := misses (ownershipActivationChannels handler) member
  have sameId := congrArg (fun current : OwnershipActivationChannels => current.act) same
  change handler.act = activation.act at sameId
  change handler.act ≠ address.activation at different
  exact sameId ▸ different

private theorem returnFrom_escaping_child {rootFuel fuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {environment : RuntimeActivation} {target : Nat}
    {operands : List Expr} {origin : Goose.Core.OriginId} {initial final : ExecutionState}
    {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitContextReached rootFuel config context
      (.statement (fuel + 1) environment (.returnFrom target operands origin)) initial)
    (misses : handlersMiss address context)
    (escaped : execStmt (fuel + 1) config environment (.returnFrom target operands origin) initial =
      .escape address carriers final) :
    EscapingSourceChild config (.statement (fuel + 1) environment (.returnFrom target operands origin)) initial address carriers := by
  rcases reached_returnFrom_escape_operands rootFuel fuel config environment target operands origin initial final
      address carriers reached.reached escaped with
    ⟨activation, channels, prepared, before, selected, setup, childReached, evaluated, cleaned⟩ |
    ⟨activation, channels, prepared, raw, before, afterMaterialized, selected, setup, childReached,
      evaluated, materialized, cleaned, emitted⟩
  · exact ⟨List Carrier, .operands fuel environment channels operands, prepared, before,
      .returnFromOperands fuel environment activation target operands origin initial prepared channels selected setup, evaluated⟩
  · have different := reached.selected_not_missing target selected misses
    exact False.elim (different (by rw [emitted]))

private theorem returnFromForward_escaping_child {rootFuel fuel : Nat} {config : EvalConfig}
    {context : List ExitLexicalFrame} {environment : RuntimeActivation} {target : Nat}
    {producer : Expr} {origin : Goose.Core.OriginId} {initial final : ExecutionState}
    {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitContextReached rootFuel config context
      (.statement (fuel + 1) environment (.returnFromForward target producer origin)) initial)
    (misses : handlersMiss address context)
    (escaped : execStmt (fuel + 1) config environment (.returnFromForward target producer origin) initial =
      .escape address carriers final) :
    EscapingSourceChild config (.statement (fuel + 1) environment (.returnFromForward target producer origin)) initial address carriers := by
  obtain ⟨activation, targetSet, discarded, outer, selected, declared, stack, included, excluded, occurrence⟩ :=
    returnFromForward_escape_produce_origin fuel config environment target producer origin initial final address carriers escaped
  rcases occurrence with ⟨channels, prepared, before, setup, evaluated, cleaned⟩ |
    ⟨channels, prepared, raw, before, afterMaterialized, setup, evaluated, materialized, cleaned, emitted⟩
  · exact ⟨List Carrier, .produce fuel environment channels producer, prepared, before,
      .returnFromForwardProduce fuel environment activation target producer origin initial prepared channels selected setup, evaluated⟩
  · have different := reached.selected_not_missing target selected misses
    exact False.elim (different (by rw [emitted]))

#print axioms returnFrom_escaping_child
#print axioms returnFromForward_escaping_child
end Goose.Proofs.ExitExecution

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem returnValues_escaping_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (operands : List Expr) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (nonlocal : address.target ≠ .ordinary)
    (escaped : execStmt (fuel + 1) config environment (.retValues operands origin) initial =
      .escape address carriers final) :
    EscapingSourceChild config (.statement (fuel + 1) environment (.retValues operands origin)) initial address carriers := by
  obtain ⟨activation, selected, interrupted | ⟨normal, emitted⟩⟩ :=
    returnValuesInvocation_escape_inv fuel config environment operands origin initial final address carriers escaped
  · obtain ⟨channels, prepared, before, setup, evaluated, cleaned⟩ :=
      withExitChannels_escape_origin environment activation operands origin
        (fun channels => evalOperands fuel config environment channels operands) initial final address carriers interrupted
    exact ⟨List Carrier, .operands fuel environment channels operands, prepared, before,
      .returnOperands fuel environment activation operands origin initial prepared channels selected setup, evaluated⟩
  · exact False.elim (nonlocal (congrArg ExitAddress.target emitted))

private theorem returnForward_escaping_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (producer : Expr) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (nonlocal : address.target ≠ .ordinary)
    (escaped : execStmt (fuel + 1) config environment (.retForward producer origin) initial =
      .escape address carriers final) :
    EscapingSourceChild config (.statement (fuel + 1) environment (.retForward producer origin)) initial address carriers := by
  obtain ⟨activation, selected, interrupted | ⟨normal, emitted⟩⟩ :=
    returnForwardInvocation_escape_inv fuel config environment producer origin initial final address carriers escaped
  · obtain ⟨channels, prepared, before, setup, evaluated, cleaned⟩ :=
      withExitChannels_escape_origin environment activation _ origin
        (fun channels => evalProduce fuel config environment channels producer) initial final address carriers interrupted
    exact ⟨List Carrier, .produce fuel environment channels producer, prepared, before,
      .returnForwardProduce fuel environment activation producer origin initial prepared channels selected setup, evaluated⟩
  · exact False.elim (nonlocal (congrArg ExitAddress.target emitted))

private theorem returnProduce_escaping_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (producer : Expr) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (nonlocal : address.target ≠ .ordinary)
    (escaped : execStmt (fuel + 1) config environment (.ret (some producer) origin) initial =
      .escape address carriers final) :
    EscapingSourceChild config (.statement (fuel + 1) environment (.ret (some producer) origin)) initial address carriers := by
  obtain ⟨activation, selected, interrupted | ⟨normal, emitted⟩⟩ :=
    returnProduceInvocation_escape_inv fuel config environment producer origin initial final address carriers escaped
  · obtain ⟨channels, prepared, before, setup, evaluated, cleaned⟩ :=
      withExitChannels_escape_origin environment activation _ origin
        (fun channels => evalProduce fuel config environment channels producer) initial final address carriers interrupted
    exact ⟨List Carrier, .produce fuel environment channels producer, prepared, before,
      .returnProduce fuel environment activation producer origin initial prepared channels selected setup, evaluated⟩
  · exact False.elim (nonlocal (congrArg ExitAddress.target emitted))

private theorem breakProduce_escaping_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (producer : Expr) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execStmt (fuel + 1) config environment (.breakValue producer origin) initial =
      .escape address carriers final) :
    EscapingSourceChild config (.statement (fuel + 1) environment (.breakValue producer origin)) initial address carriers := by
  obtain ⟨target, selected, interrupted⟩ :=
    breakProduceInvocation_escape_inv fuel config environment producer origin initial final address carriers escaped
  obtain ⟨channels, prepared, before, setup, evaluated, cleaned⟩ :=
    withExitChannels_escape_origin environment { environment with channels := target.channels } _ origin
      (fun channels => evalProduce fuel config environment channels producer) initial final address carriers interrupted
  exact ⟨List Carrier, .produce fuel environment channels producer, prepared, before,
    .breakProduce fuel environment target producer origin initial prepared channels selected setup, evaluated⟩

#print axioms returnValues_escaping_child
#print axioms returnForward_escaping_child
#print axioms returnProduce_escaping_child
#print axioms breakProduce_escaping_child
end Goose.Proofs.ExitExecution

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem returnNone_nonordinary_impossible (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (nonlocal : address.target ≠ .ordinary)
    (escaped : execStmt (fuel + 1) config environment (.ret none origin) initial =
      .escape address carriers final) : False := by
  simp only [execStmt, bind] at escaped
  cases selected : enclosingActivation environment initial with
  | stop reason after | jump target kind after =>
      simp only [selected] at escaped
      cases escaped
  | escape target payload after =>
      have safe : ProducerNeverEscapes (enclosingActivation environment) := by
        unfold enclosingActivation
        producer_never_escapes_base
      exact safe _ _ _ _ selected
  | ok activation after =>
      simp only [selected] at escaped
      split at escaped
      · simp only [returned] at escaped
        cases escaped
        exact nonlocal rfl
      · split at escaped
        · simp only [returned] at escaped
          cases escaped
          exact nonlocal rfl
        · simp only [fault] at escaped
          cases escaped

#print axioms returnNone_nonordinary_impossible
end Goose.Proofs.ExitExecution

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem call_escaping_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (context : Goose.Core.ContextId) (arguments : List Arg)
    (channels : List Channel) (origin : Goose.Core.OriginId)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : invokeCall fuel config environment context arguments channels origin initial =
      .escape address carriers final) :
    EscapingSourceChild config (.call fuel environment context arguments channels origin) initial address carriers := by
  cases fuel with
  | zero => simp only [invokeCall, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
      rcases callInvocation_escape_inv fuel config environment context arguments channels origin initial final address carriers escaped with
        ⟨id, implementation, firstChannels, prepared, receivingPrefix, evaluated⟩ |
        ⟨activation, pre, body, entered, receivingPrefix, evaluated⟩
      · exact ⟨List Value, .arguments fuel environment implementation.vars implementation.params.toList arguments, prepared, final,
          .callArguments fuel environment context arguments channels origin initial prepared id implementation firstChannels receivingPrefix, evaluated⟩
      · exact ⟨List Carrier, .activation fuel activation pre body origin, entered, final,
          .callActivation fuel environment context arguments channels origin initial entered activation pre body receivingPrefix, evaluated⟩

private theorem activation_escaping_child (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (origin : Goose.Core.OriginId) (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : enterActivation fuel config activation pre body origin initial = .escape address carriers final) :
    EscapingSourceChild config (.activation fuel activation pre body origin) initial address carriers := by
  cases fuel with
  | zero => simp only [enterActivation, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
      obtain ⟨implementation, before, lookup, evaluated, different, released⟩ :=
        enterActivation_escape_origin fuel config activation pre body origin initial final address carriers escaped
      exact ⟨List Carrier, .activationBody fuel activation pre body, initial, before,
        .activationBody fuel activation pre body origin initial implementation lookup, evaluated⟩

private theorem activationBody_escaping_child (fuel : Nat) (config : EvalConfig)
    (activation : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (body : Block)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execActivationBody fuel config activation pre body initial = .escape address carriers final) :
    EscapingSourceChild config (.activationBody fuel activation pre body) initial address carriers := by
  cases fuel with
  | zero => simp only [execActivationBody, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
      exact ⟨Flow × List Carrier, .activationScope fuel activation pre body, initial, final,
        .activationScope fuel activation pre body initial,
        execActivationBody_escape_origin fuel config activation pre body initial final address carriers escaped⟩

private theorem resultBlock_escaping_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (body : Block)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execResultBlock fuel config environment channels body initial = .escape address carriers final) :
    EscapingSourceChild config (.resultBlock fuel environment channels body) initial address carriers := by
  cases fuel with
  | zero => simp only [execResultBlock, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
      exact ⟨Flow × List Carrier, .resultBlockWith fuel environment [] channels body, initial, final,
        .resultBlockWith fuel environment channels body initial, by simpa only [execResultBlock, ExitInvocation.action] using escaped⟩

private theorem resultBlockWith_escaping_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : execResultBlockWith fuel config environment pre channels body initial = .escape address carriers final) :
    EscapingSourceChild config (.resultBlockWith fuel environment pre channels body) initial address carriers := by
  cases fuel with
  | zero => simp only [execResultBlockWith, timeout, EvalM.stop] at escaped; cases escaped
  | succ fuel =>
      exact ⟨Flow × List Carrier, .resultScope fuel environment pre channels body, initial, final,
        .resultScope fuel environment pre channels body initial,
        by simpa only [execResultBlockWith, ExitInvocation.action] using escaped⟩

private theorem completion_escaping_child (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (channels : List Channel) (expression : Expr)
    (initial final : ExecutionState) (address : ExitAddress) (carriers : List Carrier)
    (escaped : (ExitInvocation.completionTail fuel environment channels expression).action config initial =
      .escape address carriers final) :
    EscapingSourceChild config (.completionTail fuel environment channels expression) initial address carriers := by
  obtain ⟨planned, prepared, before, setup, evaluated, cleaned⟩ :=
    completionInvocation_escape_inv fuel config environment channels expression initial final address carriers escaped
  exact ⟨List Carrier, .produce fuel environment (planned.map Prod.fst) expression, prepared, before,
    .completionProduce fuel environment channels expression initial prepared planned setup, evaluated⟩

#print axioms call_escaping_child
#print axioms activation_escaping_child
#print axioms activationBody_escaping_child
#print axioms resultBlock_escaping_child
#print axioms resultBlockWith_escaping_child
#print axioms completion_escaping_child
end Goose.Proofs.ExitExecution

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem invocation_escaping_child
    (config : EvalConfig)
    {rootFuel : Nat} {α : Type} {caller : ExitInvocation α}
    {context : List ExitLexicalFrame} {initial final : ExecutionState}
    {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitContextReached rootFuel config context caller initial)
    (misses : handlersMiss address context) (nonlocal : address.target ≠ .ordinary)
    (escaped : caller.action config initial = .escape address carriers final) :
    EscapingSourceChild config caller initial address carriers := by
  have common {β : Type} (parent : ExitInvocation β) (source : StatementInvocationSource parent)
      (native : parent.action config initial = .escape address carriers final) :
      EscapingSourceChild config parent initial address carriers := by
    obtain ⟨γ, child, prepared, before, site, evaluated⟩ := statementInvocation_escape_inv config parent source initial final address carriers native
    exact ⟨γ, child, prepared, before, .statements site, evaluated⟩
  cases caller
  all_goals try (exact common _ (by trivial) escaped)
  all_goals first
    | (apply call_escaping_child; exact escaped)
    | (apply activation_escaping_child; exact escaped)
    | (apply activationBody_escaping_child; exact escaped)
    | (apply resultBlock_escaping_child; exact escaped)
    | (apply resultBlockWith_escaping_child; exact escaped)
    | (apply completion_escaping_child; exact escaped)
    | skip
  case module fuel =>
    obtain ⟨β, child, prepared, site, evaluated⟩ := moduleInvocation_escape_inv fuel config initial final address carriers escaped
    exact ⟨β, child, prepared, final, site, evaluated⟩
  case value fuel environment expression =>
    obtain ⟨β, child, prepared, site, evaluated⟩ := valueInvocation_escape_inv fuel config environment expression initial address carriers final escaped
    exact ⟨β, child, prepared, final, .values site, evaluated⟩
  case bound fuel environment count defaultValue operand =>
    obtain ⟨β, child, prepared, site, evaluated⟩ := boundInvocation_escape_inv fuel config environment count defaultValue operand initial address carriers final escaped
    exact ⟨β, child, prepared, final, .values site, evaluated⟩
  case place fuel environment operand =>
    obtain ⟨β, child, prepared, site, evaluated⟩ := placeInvocation_escape_inv fuel config environment operand initial address carriers final escaped
    exact ⟨β, child, prepared, final, .values site, evaluated⟩
  case view fuel environment operand =>
    obtain ⟨β, child, prepared, site, evaluated⟩ := viewInvocation_escape_inv fuel config environment operand initial address carriers final escaped
    exact ⟨β, child, prepared, final, .values site, evaluated⟩
  case printArgument fuel environment argument =>
    obtain ⟨β, child, prepared, site, evaluated⟩ := printInvocation_escape_inv fuel config environment argument initial address carriers final escaped
    exact ⟨β, child, prepared, final, .values site, evaluated⟩
  case produce fuel environment channels expression =>
    obtain ⟨β, child, prepared, before, result, evaluated⟩ := produceInvocation_escape_inv fuel config environment channels expression initial address carriers final escaped
    exact ⟨β, child, prepared, before, .producer result.site, evaluated⟩
  case build fuel environment destination expression =>
    obtain ⟨β, child, prepared, before, result, evaluated⟩ := buildInvocation_escape_inv fuel config environment destination expression initial address carriers final escaped
    exact ⟨β, child, prepared, before, .producer result.site, evaluated⟩
  case element fuel environment destination element expression =>
    obtain ⟨β, child, prepared, before, result, evaluated⟩ := elementInvocation_escape_inv fuel config environment destination element expression initial address carriers final escaped
    exact ⟨β, child, prepared, before, .producer result.site, evaluated⟩
  case operands fuel environment channels operands =>
    obtain ⟨β, child, prepared, site, evaluated⟩ := operandsInvocation_escape_inv fuel config environment channels operands initial address carriers final escaped
    exact ⟨β, child, prepared, final, site, evaluated⟩
  case arguments fuel environment vars params arguments =>
    obtain ⟨β, child, prepared, site, evaluated⟩ := argumentsInvocation_escape_inv fuel config environment vars params arguments initial final address carriers escaped
    exact ⟨β, child, prepared, final, site, evaluated⟩
  case statements fuel environment statements =>
    obtain ⟨β, child, prepared, site, evaluated⟩ := statementsInvocation_escape_inv fuel config environment statements initial address carriers final escaped
    exact ⟨β, child, prepared, final, site, evaluated⟩
  case block fuel environment pre channels body =>
    cases body with
    | mk scope statements tail =>
      obtain ⟨β, child, prepared, before, site, evaluated, released⟩ := blockInvocation_escape_inv fuel config environment pre channels scope statements tail initial final address carriers escaped
      exact ⟨β, child, prepared, before, site, evaluated⟩
  case activationScope fuel environment pre body =>
    cases body with
    | mk scope statements tail =>
      obtain ⟨β, child, prepared, before, site, evaluated, released⟩ := activationScopeInvocation_escape_inv fuel config environment pre scope statements tail initial final address carriers escaped
      exact ⟨β, child, prepared, before, site, evaluated⟩
  case resultScope fuel environment pre channels body =>
    cases body with
    | mk scope statements tail =>
      obtain ⟨β, child, prepared, before, site, evaluated, released⟩ := resultScopeInvocation_escape_inv fuel config environment pre channels scope statements tail initial final address carriers escaped
      exact ⟨β, child, prepared, before, site, evaluated⟩
  case statement fuel environment statement =>
    cases fuel with
    | zero => simp only [ExitInvocation.action, execStmt, timeout, EvalM.stop] at escaped; cases escaped
    | succ fuel =>
      by_cases source : StatementInvocationSource (.statement (fuel + 1) environment statement)
      · exact common _ source escaped
      · cases statement <;> simp only [StatementInvocationSource, not_true_eq_false] at source
        case retValues operands origin => exact returnValues_escaping_child fuel config environment operands origin initial final address carriers nonlocal escaped
        case retForward producer origin => exact returnForward_escaping_child fuel config environment producer origin initial final address carriers nonlocal escaped
        case returnFrom target operands origin => exact returnFrom_escaping_child reached misses escaped
        case returnFromForward target producer origin => exact returnFromForward_escaping_child reached misses escaped
        case breakValue producer origin => exact breakProduce_escaping_child fuel config environment producer origin initial final address carriers escaped
        case ret producer origin =>
          cases producer with
          | none => exact False.elim (returnNone_nonordinary_impossible fuel config environment origin initial final address carriers nonlocal escaped)
          | some producer => exact returnProduce_escaping_child fuel config environment producer origin initial final address carriers nonlocal escaped

#print axioms invocation_escaping_child
end Goose.Proofs.ExitExecution

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem no_unhandled_nonordinary
    (config : EvalConfig)
    {rootFuel : Nat} {α : Type} {caller : ExitInvocation α}
    {context : List ExitLexicalFrame} {initial final : ExecutionState}
    {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitContextReached rootFuel config context caller initial)
    (misses : handlersMiss address context) (nonlocal : address.target ≠ .ordinary)
    (escaped : caller.action config initial = .escape address carriers final) : False := by
  obtain ⟨β, child, prepared, before, site, evaluated⟩ :=
    invocation_escaping_child config reached misses nonlocal escaped
  obtain ⟨inner, frames⟩ := site.has_frames context
  exact no_unhandled_nonordinary config (.call reached site frames)
    (site.escape_handlersMiss frames escaped misses) nonlocal evaluated
termination_by caller.rank
decreasing_by exact site.rank_lt

private theorem runModule_no_unhandled_nonordinary
    (config : EvalConfig)
    (fuel : Nat) (address : ExitAddress) (carriers : List Carrier) (final : ExecutionState)
    (nonlocal : address.target ≠ .ordinary)
    (escaped : runModule fuel config .initial = .escape address carriers final) : False :=
  no_unhandled_nonordinary config (.initial (fuel := fuel))
    (by intro handler member; cases member) nonlocal escaped

#print axioms no_unhandled_nonordinary
#print axioms runModule_no_unhandled_nonordinary
end Goose.Proofs.ExitExecution

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem runModule_no_unhandled_nonlocal (fuel : Nat) (config : EvalConfig)
    (activation target : Nat) (carriers : List Carrier) (final : ExecutionState) :
    runModule fuel config .initial ≠ .escape ⟨activation, .nonlocal target⟩ carriers final := by
  intro escaped
  exact runModule_no_unhandled_nonordinary config fuel ⟨activation, .nonlocal target⟩ carriers final (by intro impossible; cases impossible) escaped

#print axioms runModule_no_unhandled_nonlocal
end Goose.Proofs.ExitExecution
