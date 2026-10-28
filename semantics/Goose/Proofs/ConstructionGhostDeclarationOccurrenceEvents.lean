import Goose.Proofs.ConstructionGhostDeclarationInversion
import Goose.Proofs.ConstructionGhostDeclarationFallback
import Goose.Proofs.ConstructionGhostNamedDeclarationEvents

namespace Goose.Proofs.ConstructionGhostDeclarationOccurrenceEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionGhostDeclaration Goose.Proofs.ConstructionGhostFixedDeclarationEvents
open Goose.Proofs.ConstructionGhostNonfixedDeclaration Goose.Proofs.ConstructionGhostDeclarationFallback
open Goose.Proofs.ConstructionGhostMaterialization Goose.Proofs.ConstructionGhostMaterializedDeclarationEvents
open Goose.Proofs.ConstructionGhostDirectDeclarationEvents Goose.Proofs.ConstructionGhostNamedDeclaration
open Goose.Proofs.ConstructionGhostNamedDeclarationEvents Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostDeclarationInversion

theorem fallback_execution (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (before rootReady ready : ExecutionState) (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar before = .ok root rootReady)
    (implemented : config.module.impls[environment.implementation]? = some implementation)
    (fallback : DeclarationFallback environment implementation localVar origin rootReady ready) :
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before =
      declarationAfterMaterialization fuel config environment descriptor root expression origin
        (materializeProducer fuel ⟨config.module, environment.vars⟩ expression (evalValue fuel config environment expression) ready) := by
  cases fallback with
  | absent notNamed =>
      exact nonfixedDeclaration_execution fuel config environment localVar expression origin before rootReady
        descriptor root implementation found nonfixed rootResult implemented notNamed
  | selected selectedReady ready result index incoming selected pending named channel renewed queried nonvalue =>
      exact nonfixedDeclaration_nonvalueFallback fuel config environment localVar expression origin before rootReady selectedReady ready
        descriptor root implementation result index incoming selected pending found nonfixed rootResult implemented named channel renewed queried nonvalue

theorem materialization_sourcePrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (expression : Expr) (origin : Goose.Core.OriginId)
    (ready : ExecutionState) :
    EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment expression ready)).construction.events
      (Goose.Proofs.Exit.stepState (declarationAfterMaterialization fuel config environment descriptor root expression origin
        (materializationContinuation (evalValue fuel config environment expression ready)))).construction.events := by
  cases source : evalValue fuel config environment expression ready with
  | ok value state =>
      cases value <;> simp only [source, materializationContinuation, declarationAfterMaterialization, Goose.Proofs.Exit.stepState]
      all_goals first
        | exact declarationContinuation_keepsEventPrefix fuel config environment descriptor root expression origin _ _
        | exact eventPrefix_refl _
  | stop | escape | jump => simp [source, materializationContinuation, declarationAfterMaterialization, Goose.Proofs.Exit.stepState, eventPrefix_refl]

theorem DeclarationOccurrence.sourcePrefix {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {localVar : Goose.Core.VarId} {expression : Expr} {origin : Goose.Core.OriginId} {before sourceReady : ExecutionState}
    {destination : Option Goose.Core.DestinationId}
    (occurrence : DeclarationOccurrence fuel config environment localVar expression origin before destination sourceReady) :
    match destination with
    | none => EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment expression sourceReady)).construction.events
        (Goose.Proofs.Exit.stepState (execStmt (fuel + 1) config environment (.letS localVar expression origin) before)).construction.events
    | some destination => EventPrefix (Goose.Proofs.Exit.stepState (buildExpr fuel config environment destination expression sourceReady)).construction.events
        (Goose.Proofs.Exit.stepState (execStmt (fuel + 1) config environment (.letS localVar expression origin) before)).construction.events := by
  cases occurrence with
  | fixed descriptor root ready found fixed rootResult =>
      obtain ⟨_, execution⟩ := fixedDeclaration_initializer_ghost fuel config environment [] localVar expression origin before sourceReady
        descriptor root found fixed rootResult
      rw [execution, fixedDeclarationContinuation_events]
      exact eventPrefix_refl _
  | materialized descriptor root rootReady implementation ready count found nonfixed rootResult implemented fallback counted =>
      rw [fallback_execution fuel config environment localVar expression origin before rootReady sourceReady descriptor root implementation
        found nonfixed rootResult implemented fallback]
      obtain ⟨_, execution⟩ := materializeProducer_source_ghost fuel config environment [] expression sourceReady count counted
      rw [execution]
      exact materialization_sourcePrefix fuel config environment descriptor root expression origin sourceReady
  | direct descriptor root rootReady implementation ready destination _ found nonfixed rootResult implemented fallback counted allocated =>
      rw [fallback_execution fuel config environment localVar expression origin before rootReady ready descriptor root implementation
        found nonfixed rootResult implemented fallback]
      rw [materializeProducer_none fuel ⟨config.module, environment.vars⟩ expression (evalValue fuel config environment expression) ready counted]
      change EventPrefix (Goose.Proofs.Exit.stepState (buildExpr fuel config environment destination expression sourceReady)).construction.events
        (Goose.Proofs.Exit.stepState (declarationContinuation fuel config environment descriptor root expression origin none ready)).construction.events
      rw [directDeclaration_after_allocation fuel config environment descriptor root expression origin ready sourceReady destination allocated]
      exact directDeclarationAfterBuild_sourcePrefix descriptor root origin destination _
  | named descriptor root rootReady implementation result index incoming selected selectedReady pending ready destination renewedReady _
      found nonfixed rootResult implemented named channel selectedResult queried valueRequest renewed prepared =>
      rw [namedDeclaration_execution fuel config environment localVar expression origin before rootReady selectedReady ready renewedReady sourceReady
        descriptor root implementation result index incoming selected destination pending found nonfixed rootResult implemented named channel
        selectedResult queried valueRequest renewed prepared]
      exact namedDeclarationAfterBuild_sourcePrefix descriptor root origin destination _

theorem DeclarationOccurrence.historyAndEvents {fuel : Nat} {config : EvalConfig} {environment : RuntimeActivation}
    {localVar : Goose.Core.VarId} {expression : Expr} {origin : Goose.Core.OriginId} {before sourceReady : ExecutionState}
    {destination : Option Goose.Core.DestinationId} {path : List Nat}
    (occurrence : DeclarationOccurrence fuel config environment localVar expression origin before destination sourceReady)
    (history : SourceHistory config (fuel + 1) path (.statement environment (.letS localVar expression origin)) before
      (execStmt (fuel + 1) config environment (.letS localVar expression origin) before)) :
    match destination with
    | none => SourceHistory config fuel (path ++ [0]) (.value environment expression) sourceReady
        (evalValue fuel config environment expression sourceReady) ∧
        EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment expression sourceReady)).construction.events
          (Goose.Proofs.Exit.stepState (execStmt (fuel + 1) config environment (.letS localVar expression origin) before)).construction.events
    | some destination => SourceHistory config fuel (path ++ [0]) (.builder environment destination expression) sourceReady
        (buildExpr fuel config environment destination expression sourceReady) ∧
        EventPrefix (Goose.Proofs.Exit.stepState (buildExpr fuel config environment destination expression sourceReady)).construction.events
          (Goose.Proofs.Exit.stepState (execStmt (fuel + 1) config environment (.letS localVar expression origin) before)).construction.events := by
  have child := occurrence_history history fuel environment localVar expression origin destination sourceReady rfl rfl occurrence
  have events := DeclarationOccurrence.sourcePrefix occurrence
  cases destination <;> exact ⟨child, events⟩

#print axioms DeclarationOccurrence.historyAndEvents
#print axioms DeclarationOccurrence.sourcePrefix
#print axioms fallback_execution
#print axioms materialization_sourcePrefix
end Goose.Proofs.ConstructionGhostDeclarationOccurrenceEvents
