import Goose.Proofs.ConstructionGhostFixedDeclarationEvents
import Goose.Proofs.ConstructionGhostNonfixedDeclaration

namespace Goose.Proofs.ConstructionGhostMaterializedDeclarationEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostDeclaration
open Goose.Proofs.ConstructionGhostMaterialization Goose.Proofs.ConstructionGhostNonfixedDeclaration
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

theorem declarationContinuation_keepsEventPrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (expression : Expr) (origin : Goose.Core.OriginId)
    (materialized : Option (Array Value)) :
    KeepsEventPrefix (declarationContinuation fuel config environment descriptor root expression origin materialized) := by
  intro before
  apply (eventPrefix_iff_isPrefix _ _).mpr
  have preserved : PreservesConstructionInvariant (PrefixInvariant before.construction.events)
      (declarationContinuation fuel config environment descriptor root expression origin materialized) := by
    unfold declarationContinuation
    apply preservesConstructionInvariant_bind
    · exact preservesConstructionInvariant_newDestination _ _ _ _ _ _ _
    · intro destination
      cases materialized <;> apply preservesConstructionInvariant_bind
      all_goals first
        | exact (evaluation_preservesConstructionInvariant (predicate := PrefixInvariant before.construction.events) fuel config).build environment destination expression
        | exact preservesConstructionInvariant_copyValue _ _ _ _ _ _
        | skip
      all_goals
        intro ignored
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
  exact preserved before List.prefix_rfl

theorem materializedDeclaration_visit_sourceEvents
    (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (visit : StatementInvocation) (member : visit ∈ visits)
    (sourceFuel : Nat) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl) (count : Nat) (ready : ExecutionState)
    (visitFuel : visit.fuel = sourceFuel + 1) (visitStatement : visit.statement = .letS localVar expression origin)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar visit.before = .ok root ready)
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (notNamed : (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = none)
    (materialized : ordinaryProducerCount? sourceFuel ⟨config.module, environment.vars⟩ expression = some count)
    (supported : FuelSupport config sourceFuel (.value environment expression)) :
    SourceHistory config sourceFuel [environment.act, visit.ordinal, 0] (.value environment expression) ready
      (evalValue sourceFuel config environment expression ready) ∧
    ready.construction.events = visit.before.construction.events ∧
    EventPrefix (Goose.Proofs.Exit.stepState (evalValue sourceFuel config environment expression ready)).construction.events
      (Goose.Proofs.Exit.stepState visit.outcome).construction.events := by
  obtain ⟨tree, execution⟩ := nonfixedDeclaration_materialized sourceFuel config environment [environment.act, visit.ordinal]
    localVar expression origin visit.before ready descriptor root implementation count found nonfixed rootResult implementationFound notNamed materialized
  have actual := statementVisit_executes replay visit member
  rw [visitFuel, visitStatement, execution] at actual
  have unchanged := rootOf_unchanged environment localVar visit.before
  rw [rootResult] at unchanged
  have same : ready = visit.before := by simpa [Goose.Proofs.Exit.stepState] using unchanged
  refine ⟨fuelHistory_exists sourceFuel config _ _ ready supported, ?_, ?_⟩
  · rw [same]
  · rw [← actual]
    cases source : evalValue sourceFuel config environment expression ready with
    | ok value state =>
        cases value <;> simp only [source, materializationContinuation, declarationAfterMaterialization, Goose.Proofs.Exit.stepState]
        all_goals first
          | exact declarationContinuation_keepsEventPrefix sourceFuel config environment descriptor root expression origin _ _
          | exact eventPrefix_refl _
    | stop | escape | jump => simp [source, materializationContinuation, declarationAfterMaterialization, Goose.Proofs.Exit.stepState, eventPrefix_refl]

def MaterializedVisitSourceEvents (config : EvalConfig) (environment : RuntimeActivation) (visits : List StatementInvocation) : Prop :=
  ∀ visit ∈ visits, ∀ sourceFuel localVar expression origin descriptor root implementation count ready,
    visit.fuel = sourceFuel + 1 → visit.statement = .letS localVar expression origin →
    environment.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = true →
    rootOf environment localVar visit.before = .ok root ready →
    config.module.impls[environment.implementation]? = some implementation →
    (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = none →
    ordinaryProducerCount? sourceFuel ⟨config.module, environment.vars⟩ expression = some count →
    SourceHistory config sourceFuel [environment.act, visit.ordinal, 0] (.value environment expression) ready
      (evalValue sourceFuel config environment expression ready) ∧
    ready.construction.events = visit.before.construction.events ∧
    EventPrefix (Goose.Proofs.Exit.stepState (evalValue sourceFuel config environment expression ready)).construction.events
      (Goose.Proofs.Exit.stepState visit.outcome).construction.events

theorem statementReplay_materializedSourceEvents
    (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (supported : ∀ sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
      FuelSupport config sourceFuel (.value environment expression)) :
    MaterializedVisitSourceEvents config environment visits := by
  intro visit member sourceFuel localVar expression origin descriptor root implementation count ready visitFuel visitStatement
    found nonfixed rootResult implementationFound notNamed materialized
  have inMapped : visit.statement ∈ visits.map StatementInvocation.statement := List.mem_map_of_mem member
  rw [replay.sourceOrder] at inMapped
  have inStatements : .letS localVar expression origin ∈ statements := by
    rw [← visitStatement]
    exact List.mem_of_mem_take inMapped
  exact materializedDeclaration_visit_sourceEvents replay visit member sourceFuel localVar expression origin descriptor root implementation
    count ready visitFuel visitStatement found nonfixed rootResult implementationFound notNamed materialized
    (supported sourceFuel localVar expression origin inStatements)

#print axioms statementReplay_materializedSourceEvents
#print axioms declarationContinuation_keepsEventPrefix
#print axioms materializedDeclaration_visit_sourceEvents
end Goose.Proofs.ConstructionGhostMaterializedDeclarationEvents
