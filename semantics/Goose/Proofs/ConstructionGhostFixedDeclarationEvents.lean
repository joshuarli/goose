import Goose.Proofs.ConstructionGhostStatementEvents
import Goose.Proofs.ConstructionBindingEventsCore
import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostFixedDeclarationEvents
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostDeclaration
open Goose.Proofs.ConstructionGhostInvocation Goose.Proofs.ConstructionAcceptedExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel Goose.Proofs.ConstructionGhostSyntaxFuel

theorem fixedDeclarationContinuation_events (root : Goose.Core.RootInst) (source : ExecutionStep Value) :
    (Goose.Proofs.Exit.stepState (fixedDeclarationContinuation root source)).construction.events =
      (Goose.Proofs.Exit.stepState source).construction.events := by
  cases source with
  | ok value state =>
      have events := bindRoot_events root value state
      simp only [fixedDeclarationContinuation, bind]
      cases bound : bindRoot root value state <;> simpa [bound, pure, Goose.Proofs.Exit.stepState] using events
  | stop | escape | jump => rfl

theorem fixedDeclaration_visit_sourceEvents
    (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (visit : StatementInvocation) (member : visit ∈ visits)
    (sourceFuel : Nat) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (ready : ExecutionState)
    (visitFuel : visit.fuel = sourceFuel + 1)
    (visitStatement : visit.statement = .letS localVar expression origin)
    (found : environment.vars[localVar]? = some descriptor)
    (fixed : descriptor.ty.nonfixed = false)
    (rootResult : rootOf environment localVar visit.before = .ok root ready) :
    EvaluationTree config environment sourceFuel [environment.act, visit.ordinal, 0] expression ready
      (evalValue sourceFuel config environment expression ready) ∧
    ready.construction.events = visit.before.construction.events ∧
    (Goose.Proofs.Exit.stepState visit.outcome).construction.events =
      (Goose.Proofs.Exit.stepState (evalValue sourceFuel config environment expression ready)).construction.events ∧
    EventPrefix visit.before.construction.events (Goose.Proofs.Exit.stepState visit.outcome).construction.events := by
  obtain ⟨tree, execution⟩ := fixedDeclaration_visit_ghost replay visit member sourceFuel localVar expression origin
    descriptor root ready visitFuel visitStatement found fixed rootResult
  have unchanged := rootOf_unchanged environment localVar visit.before
  rw [rootResult] at unchanged
  have same : ready = visit.before := by simpa [Goose.Proofs.Exit.stepState] using unchanged
  refine ⟨tree, ?_, ?_, ?_⟩
  · rw [same]
  · rw [execution]
    exact fixedDeclarationContinuation_events root _
  · have preserved := (evaluation_keepsEventPrefix sourceFuel config).value environment expression ready
    rw [execution, fixedDeclarationContinuation_events, ← same]
    exact preserved

theorem fixedDeclaration_visit_syntaxEvents
    (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (closed : ClosedModuleWithTails config) (visit : StatementInvocation) (member : visit ∈ visits)
    (sourceFuel : Nat) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (ready : ExecutionState)
    (visitFuel : visit.fuel = sourceFuel + 1)
    (visitStatement : visit.statement = .letS localVar expression origin)
    (found : environment.vars[localVar]? = some descriptor)
    (fixed : descriptor.ty.nonfixed = false)
    (rootResult : rootOf environment localVar visit.before = .ok root ready)
    (derivation : ValueSyntax config expression) :
    SourceHistory config sourceFuel [environment.act, visit.ordinal, 0] (.value environment expression) ready
      (evalValue sourceFuel config environment expression ready) ∧
    ready.construction.events = visit.before.construction.events ∧
    (Goose.Proofs.Exit.stepState visit.outcome).construction.events =
      (Goose.Proofs.Exit.stepState (evalValue sourceFuel config environment expression ready)).construction.events ∧
    EventPrefix visit.before.construction.events (Goose.Proofs.Exit.stepState visit.outcome).construction.events := by
  obtain ⟨tree, initial, final, retained⟩ := fixedDeclaration_visit_sourceEvents replay visit member sourceFuel localVar
    expression origin descriptor root ready visitFuel visitStatement found fixed rootResult
  exact ⟨fuelHistory_exists sourceFuel config _ _ ready
    ((syntaxFuel_existsWithTails sourceFuel config closed).value environment expression derivation), initial, final, retained⟩

#print axioms fixedDeclaration_visit_syntaxEvents
#print axioms fixedDeclarationContinuation_events
#print axioms fixedDeclaration_visit_sourceEvents
end Goose.Proofs.ConstructionGhostFixedDeclarationEvents
