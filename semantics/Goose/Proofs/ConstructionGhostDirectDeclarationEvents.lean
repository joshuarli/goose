import Goose.Proofs.ConstructionGhostMaterializedDeclarationEvents

namespace Goose.Proofs.ConstructionGhostDirectDeclarationEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostDeclaration
open Goose.Proofs.ConstructionGhostNonfixedDeclaration Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

theorem directDeclarationAfterBuild_sourcePrefix (descriptor : LocalVar) (root : Goose.Core.RootInst)
    (origin : Goose.Core.OriginId) (destination : Goose.Core.DestinationId) (built : ExecutionStep Unit) :
    EventPrefix (Goose.Proofs.Exit.stepState built).construction.events
      (Goose.Proofs.Exit.stepState (directDeclarationAfterBuild descriptor root origin destination built)).construction.events := by
  cases built with
  | ok unit state =>
      cases unit
      apply (eventPrefix_iff_isPrefix _ _).mpr
      have preserved : PreservesConstructionInvariant (PrefixInvariant state.construction.events)
          (do let completed ← completedReceivingDestination destination
              publishCarriers origin [.completed completed]
              let stored ← storedDestination completed
              bindRoot root (.stored { stored with ty := descriptor.ty, object := none })
              pure (Flow.normal .unit)) := by
        apply preservesConstructionInvariant_bind
        · exact stateQuery_preservesConstructionInvariant _ (stateQuery_completedReceivingDestination destination)
        · intro completed
          apply preservesConstructionInvariant_bind
          · exact preservesConstructionInvariant_publishCarriers _ _
          · intro ignored
            apply preservesConstructionInvariant_bind
            · exact stateQuery_preservesConstructionInvariant _ (stateQuery_storedDestination completed)
            · intro stored
              apply preservesConstructionInvariant_bind
              · exact preservesConstructionInvariant_bindRoot _ _
              · intro ignored; exact preservesConstructionInvariant_pure _
      exact preserved state List.prefix_rfl
  | stop | escape | jump => exact eventPrefix_refl _

theorem directDeclaration_visit_sourceEvents
    (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (visit : StatementInvocation) (member : visit ∈ visits)
    (sourceFuel : Nat) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (ready buildReady : ExecutionState) (destination : Goose.Core.DestinationId)
    (visitFuel : visit.fuel = sourceFuel + 1) (visitStatement : visit.statement = .letS localVar expression origin)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar visit.before = .ok root ready)
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (notNamed : (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = none)
    (direct : ordinaryProducerCount? sourceFuel ⟨config.module, environment.vars⟩ expression = none)
    (allocated : newDestination config.layout environment.act descriptor.ty .value origin none
      (producerCount? ⟨config.module, environment.vars⟩ expression) ready = .ok destination buildReady)
    (supported : FuelSupport config sourceFuel (.builder environment destination expression)) :
    SourceHistory config sourceFuel [environment.act, visit.ordinal, 0] (.builder environment destination expression) buildReady
      (buildExpr sourceFuel config environment destination expression buildReady) ∧
    EventPrefix (Goose.Proofs.Exit.stepState (buildExpr sourceFuel config environment destination expression buildReady)).construction.events
      (Goose.Proofs.Exit.stepState visit.outcome).construction.events := by
  have execution := nonfixedDeclaration_direct sourceFuel config environment localVar expression origin visit.before ready
    descriptor root implementation found nonfixed rootResult implementationFound notNamed direct
  have actual := statementVisit_executes replay visit member
  rw [visitFuel, visitStatement, execution] at actual
  have afterBuild : declarationContinuation sourceFuel config environment descriptor root expression origin none ready =
      directDeclarationAfterBuild descriptor root origin destination (buildExpr sourceFuel config environment destination expression buildReady) := by
    have allocated' : newDestination config.layout environment.act descriptor.ty .value origin none
        ((none : Option (Array Value)).map Array.size <|> producerCount? ⟨config.module, environment.vars⟩ expression) ready =
          .ok destination buildReady := by simpa using allocated
    simp only [declarationContinuation, bind, pure, allocated']
    cases built : buildExpr sourceFuel config environment destination expression buildReady <;>
      simp [directDeclarationAfterBuild, built, bind, pure]
  rw [afterBuild] at actual
  refine ⟨fuelHistory_exists sourceFuel config _ _ buildReady supported, ?_⟩
  rw [← actual]
  exact directDeclarationAfterBuild_sourcePrefix descriptor root origin destination _

def DirectVisitSourceEvents (config : EvalConfig) (environment : RuntimeActivation) (visits : List StatementInvocation) : Prop :=
  ∀ visit ∈ visits, ∀ sourceFuel localVar expression origin descriptor root implementation ready buildReady destination,
    visit.fuel = sourceFuel + 1 → visit.statement = .letS localVar expression origin →
    environment.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = true →
    rootOf environment localVar visit.before = .ok root ready →
    config.module.impls[environment.implementation]? = some implementation →
    (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = none →
    ordinaryProducerCount? sourceFuel ⟨config.module, environment.vars⟩ expression = none →
    newDestination config.layout environment.act descriptor.ty .value origin none
      (producerCount? ⟨config.module, environment.vars⟩ expression) ready = .ok destination buildReady →
    SourceHistory config sourceFuel [environment.act, visit.ordinal, 0] (.builder environment destination expression) buildReady
      (buildExpr sourceFuel config environment destination expression buildReady) ∧
    EventPrefix (Goose.Proofs.Exit.stepState (buildExpr sourceFuel config environment destination expression buildReady)).construction.events
      (Goose.Proofs.Exit.stepState visit.outcome).construction.events

theorem statementReplay_directSourceEvents
    (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (supported : ∀ sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements → ∀ destination,
      FuelSupport config sourceFuel (.builder environment destination expression)) :
    DirectVisitSourceEvents config environment visits := by
  intro visit member sourceFuel localVar expression origin descriptor root implementation ready buildReady destination
    visitFuel visitStatement found nonfixed rootResult implementationFound notNamed direct allocated
  have inMapped : visit.statement ∈ visits.map StatementInvocation.statement := List.mem_map_of_mem member
  rw [replay.sourceOrder] at inMapped
  have inStatements : .letS localVar expression origin ∈ statements := by
    rw [← visitStatement]
    exact List.mem_of_mem_take inMapped
  exact directDeclaration_visit_sourceEvents replay visit member sourceFuel localVar expression origin descriptor root implementation
    ready buildReady destination visitFuel visitStatement found nonfixed rootResult implementationFound notNamed direct allocated
    (supported sourceFuel localVar expression origin inStatements destination)

#print axioms statementReplay_directSourceEvents
#print axioms directDeclarationAfterBuild_sourcePrefix
#print axioms directDeclaration_visit_sourceEvents
end Goose.Proofs.ConstructionGhostDirectDeclarationEvents
