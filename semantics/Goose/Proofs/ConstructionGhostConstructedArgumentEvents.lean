import Goose.Proofs.ConstructionGhostArgumentHistoryInversion

namespace Goose.Proofs.ConstructionGhostConstructedArgumentEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostArguments
open Goose.Proofs.ConstructionGhostArgumentHistoryInversion Goose.Proofs.ConstructionGhostCallArgumentEvents
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostStatementPaths
open Goose.Proofs.ConstructionGhostMaterialization

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

def terminalValue {α : Type} : ExecutionStep α → Option (ExecutionStep Value)
  | .ok _ _ => none
  | .stop reason state => some (.stop reason state)
  | .escape address carriers state => some (.escape address carriers state)
  | .jump target kind state => some (.jump target kind state)

theorem constructedArgument_missingParameter (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (operand : Expr) (before : ExecutionState)
    (missing : vars[parameter.var]? = none) :
    argumentValue fuel config environment vars parameter (.construct operand) before = .stop (.fault .unbound) before := by
  simp [argumentValue, missing, fault, EvalM.stop]

theorem constructedArgument_direct_allocationTerminal (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (operand : Expr) (localVar : LocalVar) (before : ExecutionState)
    (terminal : ExecutionStep Value) (found : vars[parameter.var]? = some localVar)
    (direct : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = none)
    (allocated : terminalValue (newDestination config.layout environment.act localVar.ty .value (expressionOrigin operand) none
      (producerCount? ⟨config.module, environment.vars⟩ operand) before) = some terminal) :
    argumentValue fuel config environment vars parameter (.construct operand) before = terminal := by
  rw [constructedArgument_direct_source fuel config environment vars parameter operand localVar before found direct]
  cases result : newDestination config.layout environment.act localVar.ty .value (expressionOrigin operand) none
    (producerCount? ⟨config.module, environment.vars⟩ operand) before <;> simp_all [terminalValue, bind]

#print axioms constructedArgument_missingParameter
#print axioms constructedArgument_direct_allocationTerminal
theorem constructedArgument_direct_sourcePrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (operand : Expr) (localVar : LocalVar)
    (destination : Goose.Core.DestinationId) (before ready : ExecutionState)
    (found : vars[parameter.var]? = some localVar)
    (direct : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = none)
    (allocated : newDestination config.layout environment.act localVar.ty .value (expressionOrigin operand) none
      (producerCount? ⟨config.module, environment.vars⟩ operand) before = .ok destination ready) :
    EventPrefix (Goose.Proofs.Exit.stepState (buildExpr fuel config environment destination operand ready)).construction.events
      (Goose.Proofs.Exit.stepState (argumentValue fuel config environment vars parameter (.construct operand) before)).construction.events := by
  rw [constructedArgument_direct_source fuel config environment vars parameter operand localVar before found direct]
  simp only [bind, allocated]
  cases built : buildExpr fuel config environment destination operand ready with
  | ok unit state =>
      cases unit
      apply (eventPrefix_iff_isPrefix _ _).mpr
      have kept : PreservesConstructionInvariant (PrefixInvariant state.construction.events)
          (do let destination ← completedReceivingDestination destination
              publishCarriers (expressionOrigin operand) [.completed destination]
              carrierValue (.completed destination)) := by
        apply preservesConstructionInvariant_bind
        · exact stateQuery_preservesConstructionInvariant _ (stateQuery_completedReceivingDestination destination)
        · intro completed
          apply preservesConstructionInvariant_bind
          · exact preservesConstructionInvariant_publishCarriers _ _
          · intro ignored
            exact stateQuery_preservesConstructionInvariant _ (stateQuery_carrierValue _)
      simpa [built, Goose.Proofs.Exit.stepState, ExecutionInvariant, PrefixInvariant, bind] using kept state List.prefix_rfl
  | stop | escape | jump => simp [built, Goose.Proofs.Exit.stepState, eventPrefix_refl]

theorem constructedArgument_materialized_sourcePrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) (operand : Expr) (localVar : LocalVar) (count : Nat) (before : ExecutionState)
    (found : vars[parameter.var]? = some localVar)
    (materialized : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = some count) :
    EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment operand before)).construction.events
      (Goose.Proofs.Exit.stepState (argumentValue fuel config environment vars parameter (.construct operand) before)).construction.events := by
  rw [constructedArgument_execution fuel config environment vars parameter operand before localVar found]
  obtain ⟨tree, execution⟩ := materializeProducer_source_ghost fuel config environment [] operand before count materialized
  rw [execution]
  cases result : evalValue fuel config environment operand before with
  | ok value state =>
      cases value with
      | fixed values =>
          apply (eventPrefix_iff_isPrefix _ _).mpr
          have kept : PreservesConstructionInvariant (PrefixInvariant state.construction.events)
              (do let destination ← materializedDestination fuel config.layout environment.act localVar.ty
                    (expressionOrigin operand) values.size (.fixed values)
                  publishCarriers (expressionOrigin operand) [.completed destination]
                  carrierValue (.completed destination)) := by
            apply preservesConstructionInvariant_bind
            · exact preservesConstructionInvariant_materializedDestination _ _ _ _ _ _ _
            · intro destination
              apply preservesConstructionInvariant_bind
              · exact preservesConstructionInvariant_publishCarriers _ _
              · intro ignored
                exact stateQuery_preservesConstructionInvariant _ (stateQuery_carrierValue _)
          simpa [result, materializationContinuation, constructedArgumentContinuation, bind, pure, Goose.Proofs.Exit.stepState,
            ExecutionInvariant, PrefixInvariant] using kept state List.prefix_rfl
      | int | bool | unit | ref | slice | stored | record =>
          simp [result, materializationContinuation, constructedArgumentContinuation, fault, EvalM.stop,
            Goose.Proofs.Exit.stepState, eventPrefix_refl]
  | stop | escape | jump => simp [result, materializationContinuation, constructedArgumentContinuation, Goose.Proofs.Exit.stepState, eventPrefix_refl]

#print axioms constructedArgument_materialized_sourcePrefix
theorem invokeCall_constructedDirectSource (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) (callBefore before : ExecutionState) (id : Goose.Core.ImplId)
    (implementation : Impl) (callableChannels : List Channel) (outcome : ExecutionStep (List Value))
    (visits : List ArgumentInvocation) (visit : ArgumentInvocation) (operand : Expr) (localVar : LocalVar)
    (destination : Goose.Core.DestinationId) (ready : ExecutionState)
    (history : SourceHistory config fuel path (.arguments environment implementation.vars implementation.params.toList arguments) before outcome)
    (replay : ArgumentReplay config environment implementation.vars fuel 0 implementation.params.toList arguments before outcome visits)
    (member : visit ∈ visits) (constructed : visit.argument = .construct operand)
    (found : implementation.vars[visit.parameter.var]? = some localVar)
    (direct : ordinaryProducerCount? visit.fuel ⟨config.module, environment.vars⟩ operand = none)
    (allocated : newDestination config.layout environment.act localVar.ty .value (expressionOrigin operand) none
      (producerCount? ⟨config.module, environment.vars⟩ operand) visit.before = .ok destination ready)
    (execution : invokeCall (fuel + 1) config environment context arguments channels origin callBefore =
      callArgumentsContinuation fuel config id implementation channels callableChannels origin outcome) :
    ∃ suffix, StatementPath 0 suffix visit.ordinal ∧
      SourceHistory config visit.fuel (path ++ suffix) (.builder environment destination operand) ready
        (buildExpr visit.fuel config environment destination operand ready) ∧
      EventPrefix (Goose.Proofs.Exit.stepState (buildExpr visit.fuel config environment destination operand ready)).construction.events
        (Goose.Proofs.Exit.stepState (invokeCall (fuel + 1) config environment context arguments channels origin callBefore)).construction.events := by
  obtain ⟨suffix, suffixPath, materialized, child⟩ := argumentReplay_constructedPaths replay path history visit member operand constructed
  refine ⟨suffix, suffixPath, child localVar destination ready found direct allocated, ?_⟩
  have sourcePrefix := constructedArgument_direct_sourcePrefix visit.fuel config environment implementation.vars visit.parameter operand
    localVar destination visit.before ready found direct allocated
  have actual := argumentReplay_visitExecutes replay visit member
  rw [constructed] at actual
  rw [actual] at sourcePrefix
  exact eventPrefix_trans _ _ _ sourcePrefix
    (invokeCall_argumentVisitPrefix fuel config environment context arguments channels origin callBefore before id implementation
      callableChannels outcome visits visit replay member execution)

theorem invokeCall_constructedMaterializedSource (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) (callBefore before : ExecutionState) (id : Goose.Core.ImplId)
    (implementation : Impl) (callableChannels : List Channel) (outcome : ExecutionStep (List Value))
    (visits : List ArgumentInvocation) (visit : ArgumentInvocation) (operand : Expr) (localVar : LocalVar) (count : Nat)
    (history : SourceHistory config fuel path (.arguments environment implementation.vars implementation.params.toList arguments) before outcome)
    (replay : ArgumentReplay config environment implementation.vars fuel 0 implementation.params.toList arguments before outcome visits)
    (member : visit ∈ visits) (constructed : visit.argument = .construct operand)
    (found : implementation.vars[visit.parameter.var]? = some localVar)
    (materialized : ordinaryProducerCount? visit.fuel ⟨config.module, environment.vars⟩ operand = some count)
    (execution : invokeCall (fuel + 1) config environment context arguments channels origin callBefore =
      callArgumentsContinuation fuel config id implementation channels callableChannels origin outcome) :
    ∃ suffix, StatementPath 0 suffix visit.ordinal ∧
      SourceHistory config visit.fuel (path ++ suffix) (.value environment operand) visit.before
        (evalValue visit.fuel config environment operand visit.before) ∧
      EventPrefix (Goose.Proofs.Exit.stepState (evalValue visit.fuel config environment operand visit.before)).construction.events
        (Goose.Proofs.Exit.stepState (invokeCall (fuel + 1) config environment context arguments channels origin callBefore)).construction.events := by
  obtain ⟨suffix, suffixPath, child, direct⟩ := argumentReplay_constructedPaths replay path history visit member operand constructed
  refine ⟨suffix, suffixPath, child localVar count found materialized, ?_⟩
  have sourcePrefix := constructedArgument_materialized_sourcePrefix visit.fuel config environment implementation.vars visit.parameter operand
    localVar count visit.before found materialized
  have actual := argumentReplay_visitExecutes replay visit member
  rw [constructed] at actual
  rw [actual] at sourcePrefix
  exact eventPrefix_trans _ _ _ sourcePrefix
    (invokeCall_argumentVisitPrefix fuel config environment context arguments channels origin callBefore before id implementation
      callableChannels outcome visits visit replay member execution)

theorem invokeCall_constructedClassification (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) (callBefore before : ExecutionState) (id : Goose.Core.ImplId)
    (implementation : Impl) (callableChannels : List Channel) (outcome : ExecutionStep (List Value))
    (visits : List ArgumentInvocation) (visit : ArgumentInvocation) (operand : Expr)
    (history : SourceHistory config fuel path (.arguments environment implementation.vars implementation.params.toList arguments) before outcome)
    (replay : ArgumentReplay config environment implementation.vars fuel 0 implementation.params.toList arguments before outcome visits)
    (member : visit ∈ visits) (constructed : visit.argument = .construct operand)
    (execution : invokeCall (fuel + 1) config environment context arguments channels origin callBefore =
      callArgumentsContinuation fuel config id implementation channels callableChannels origin outcome) :
    (implementation.vars[visit.parameter.var]? = none ∧ visit.outcome = .stop (.fault .unbound) visit.before) ∨
    (∃ localVar count suffix, implementation.vars[visit.parameter.var]? = some localVar ∧
      ordinaryProducerCount? visit.fuel ⟨config.module, environment.vars⟩ operand = some count ∧
      StatementPath 0 suffix visit.ordinal ∧
      SourceHistory config visit.fuel (path ++ suffix) (.value environment operand) visit.before
        (evalValue visit.fuel config environment operand visit.before) ∧
      EventPrefix (Goose.Proofs.Exit.stepState (evalValue visit.fuel config environment operand visit.before)).construction.events
        (Goose.Proofs.Exit.stepState (invokeCall (fuel + 1) config environment context arguments channels origin callBefore)).construction.events) ∨
    (∃ localVar terminal, implementation.vars[visit.parameter.var]? = some localVar ∧
      ordinaryProducerCount? visit.fuel ⟨config.module, environment.vars⟩ operand = none ∧
      terminalValue (newDestination config.layout environment.act localVar.ty .value (expressionOrigin operand) none
        (producerCount? ⟨config.module, environment.vars⟩ operand) visit.before) = some terminal ∧ visit.outcome = terminal) ∨
    (∃ localVar destination ready suffix, implementation.vars[visit.parameter.var]? = some localVar ∧
      ordinaryProducerCount? visit.fuel ⟨config.module, environment.vars⟩ operand = none ∧
      newDestination config.layout environment.act localVar.ty .value (expressionOrigin operand) none
        (producerCount? ⟨config.module, environment.vars⟩ operand) visit.before = .ok destination ready ∧
      StatementPath 0 suffix visit.ordinal ∧
      SourceHistory config visit.fuel (path ++ suffix) (.builder environment destination operand) ready
        (buildExpr visit.fuel config environment destination operand ready) ∧
      EventPrefix (Goose.Proofs.Exit.stepState (buildExpr visit.fuel config environment destination operand ready)).construction.events
        (Goose.Proofs.Exit.stepState (invokeCall (fuel + 1) config environment context arguments channels origin callBefore)).construction.events) := by
  have actual := argumentReplay_visitExecutes replay visit member
  rw [constructed] at actual
  cases found : implementation.vars[visit.parameter.var]? with
  | none =>
      exact Or.inl ⟨rfl, actual.symm.trans (constructedArgument_missingParameter visit.fuel config environment implementation.vars visit.parameter operand visit.before found)⟩
  | some localVar =>
      cases countResult : ordinaryProducerCount? visit.fuel ⟨config.module, environment.vars⟩ operand with
      | some count =>
          obtain ⟨suffix, suffixPath, child, kept⟩ := invokeCall_constructedMaterializedSource fuel config environment path context arguments channels origin
            callBefore before id implementation callableChannels outcome visits visit operand localVar count history replay member constructed found countResult execution
          exact Or.inr (Or.inl ⟨localVar, count, suffix, rfl, rfl, suffixPath, child, kept⟩)
      | none =>
          cases allocated : newDestination config.layout environment.act localVar.ty .value (expressionOrigin operand) none
            (producerCount? ⟨config.module, environment.vars⟩ operand) visit.before with
          | ok destination ready =>
              obtain ⟨suffix, suffixPath, child, kept⟩ := invokeCall_constructedDirectSource fuel config environment path context arguments channels origin
                callBefore before id implementation callableChannels outcome visits visit operand localVar destination ready history replay member constructed found countResult allocated execution
              exact Or.inr (Or.inr (Or.inr ⟨localVar, destination, ready, suffix, rfl, rfl, allocated, suffixPath, child, kept⟩))
          | stop reason state =>
              have terminal : terminalValue (newDestination config.layout environment.act localVar.ty .value (expressionOrigin operand) none
                (producerCount? ⟨config.module, environment.vars⟩ operand) visit.before) = some (.stop reason state) := by simp [allocated, terminalValue]
              exact Or.inr (Or.inr (Or.inl ⟨localVar, .stop reason state, rfl, rfl, terminal, actual.symm.trans
                (constructedArgument_direct_allocationTerminal visit.fuel config environment implementation.vars visit.parameter operand localVar visit.before _ found countResult terminal)⟩))
          | escape address carriers state =>
              have terminal : terminalValue (newDestination config.layout environment.act localVar.ty .value (expressionOrigin operand) none
                (producerCount? ⟨config.module, environment.vars⟩ operand) visit.before) = some (.escape address carriers state) := by simp [allocated, terminalValue]
              exact Or.inr (Or.inr (Or.inl ⟨localVar, .escape address carriers state, rfl, rfl, terminal, actual.symm.trans
                (constructedArgument_direct_allocationTerminal visit.fuel config environment implementation.vars visit.parameter operand localVar visit.before _ found countResult terminal)⟩))
          | jump target kind state =>
              have terminal : terminalValue (newDestination config.layout environment.act localVar.ty .value (expressionOrigin operand) none
                (producerCount? ⟨config.module, environment.vars⟩ operand) visit.before) = some (.jump target kind state) := by simp [allocated, terminalValue]
              exact Or.inr (Or.inr (Or.inl ⟨localVar, .jump target kind state, rfl, rfl, terminal, actual.symm.trans
                (constructedArgument_direct_allocationTerminal visit.fuel config environment implementation.vars visit.parameter operand localVar visit.before _ found countResult terminal)⟩))

#print axioms invokeCall_constructedClassification
#print axioms invokeCall_constructedMaterializedSource
#print axioms invokeCall_constructedDirectSource
#print axioms constructedArgument_direct_sourcePrefix
end Goose.Proofs.ConstructionGhostConstructedArgumentEvents
