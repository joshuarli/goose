import Goose.Proofs.ConstructionGhostDirectDeclarationEvents
import Goose.Proofs.ConstructionGhostNamedDeclaration

namespace Goose.Proofs.ConstructionGhostNamedDeclarationEvents
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionExecutionProtocol
open Goose.Proofs.ConstructionExecutionEventPrefixProtocol Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostDeclaration
open Goose.Proofs.ConstructionGhostNamedDeclaration Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel

attribute [local instance] eventPrefixPrimitives eventPrefixReservationPrimitives

theorem namedDeclarationAfterBuild_sourcePrefix (descriptor : LocalVar) (root : Goose.Core.RootInst)
    (origin : Goose.Core.OriginId) (destination : Goose.Core.DestinationId) (built : ExecutionStep Unit) :
    EventPrefix (Goose.Proofs.Exit.stepState built).construction.events
      (Goose.Proofs.Exit.stepState (namedDeclarationAfterBuild descriptor root origin destination built)).construction.events := by
  cases built with
  | ok unit state =>
      cases unit
      apply (eventPrefix_iff_isPrefix _ _).mpr
      have preserved : PreservesConstructionInvariant (PrefixInvariant state.construction.events)
          (do let completed ← completedReceivingDestination destination
              let stored ← storedDestination completed
              let object ← liftConstruction origin reserveStorage
              bindRoot root (.stored { stored with ty := descriptor.ty, object := some object })
              pure (Flow.normal .unit)) := by
        apply preservesConstructionInvariant_bind
        · exact stateQuery_preservesConstructionInvariant _ (stateQuery_completedReceivingDestination destination)
        · intro completed
          apply preservesConstructionInvariant_bind
          · exact stateQuery_preservesConstructionInvariant _ (stateQuery_storedDestination completed)
          · intro stored
            apply preservesConstructionInvariant_bind
            · kernel_protocol
            · intro object
              apply preservesConstructionInvariant_bind
              · exact preservesConstructionInvariant_bindRoot _ _
              · intro ignored; exact preservesConstructionInvariant_pure _
      exact preserved state List.prefix_rfl
  | stop | escape | jump => exact eventPrefix_refl _

theorem namedDeclaration_visit_sourceEvents
    (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (visit : StatementInvocation) (member : visit ∈ visits)
    (sourceFuel : Nat) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (rootReady selectedReady destinationReady renewedReady buildReady : ExecutionState)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (implementation : Impl)
    (result : ResultDescriptor) (index : Nat) (incoming selected destination : Goose.Core.DestinationId) (pending : PendingDestination)
    (visitFuel : visit.fuel = sourceFuel + 1) (visitStatement : visit.statement = .letS localVar expression origin)
    (found : environment.vars[localVar]? = some descriptor) (nonfixed : descriptor.ty.nonfixed = true)
    (rootResult : rootOf environment localVar visit.before = .ok root rootReady)
    (implementationFound : config.module.impls[environment.implementation]? = some implementation)
    (named : (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = some (result, index))
    (channelFound : environment.channels[index]? = some (.construct incoming))
    (selectedResult : liftConstruction origin (renewReceivingDestination incoming) rootReady = .ok selected selectedReady)
    (pendingResult : getDestination selected selectedReady = .ok pending destinationReady)
    (valueRequest : pending.capability.request = .value)
    (renewedResult : liftConstruction origin (renewReceivingDestination incoming) destinationReady = .ok destination renewedReady)
    (prepared : liftConstruction origin (prepareNamedBinding destination descriptor.ty) renewedReady = .ok () buildReady)
    (supported : FuelSupport config sourceFuel (.builder environment destination expression)) :
    SourceHistory config sourceFuel [environment.act, visit.ordinal, 0] (.builder environment destination expression) buildReady
      (buildExpr sourceFuel config environment destination expression buildReady) ∧
    EventPrefix (Goose.Proofs.Exit.stepState (buildExpr sourceFuel config environment destination expression buildReady)).construction.events
      (Goose.Proofs.Exit.stepState visit.outcome).construction.events := by
  have execution := namedDeclaration_execution sourceFuel config environment localVar expression origin visit.before rootReady
    selectedReady destinationReady renewedReady buildReady descriptor root implementation result index incoming selected destination pending
    found nonfixed rootResult implementationFound named channelFound selectedResult pendingResult valueRequest renewedResult prepared
  have actual := statementVisit_executes replay visit member
  rw [visitFuel, visitStatement, execution] at actual
  refine ⟨fuelHistory_exists sourceFuel config _ _ buildReady supported, ?_⟩
  rw [← actual]
  exact namedDeclarationAfterBuild_sourcePrefix descriptor root origin destination _

#print axioms namedDeclarationAfterBuild_sourcePrefix
#print axioms namedDeclaration_visit_sourceEvents
end Goose.Proofs.ConstructionGhostNamedDeclarationEvents
