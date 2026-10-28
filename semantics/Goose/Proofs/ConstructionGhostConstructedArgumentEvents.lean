import Goose.Proofs.ConstructionGhostArgumentHistoryInversion

namespace Goose.Proofs.ConstructionGhostConstructedArgumentEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostArguments
open Goose.Proofs.ConstructionGhostArgumentHistoryInversion Goose.Proofs.ConstructionGhostCallArgumentEvents
open Goose.Proofs.ConstructionGhostCallArguments Goose.Proofs.ConstructionGhostStatementPaths
open Goose.Proofs.ConstructionGhostMaterialization

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

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

#print axioms invokeCall_constructedMaterializedSource
#print axioms invokeCall_constructedDirectSource
#print axioms constructedArgument_direct_sourcePrefix
end Goose.Proofs.ConstructionGhostConstructedArgumentEvents
