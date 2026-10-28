import Goose.Proofs.ConstructionGhostStatementEvents
import Goose.Proofs.ConstructionBindingEventsCore
import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostFixedDeclarationEvents
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostDeclaration
open Goose.Proofs.ConstructionGhostStatementEvents Goose.Proofs.ConstructionGhostBlock
open Goose.Proofs.ConstructionGhostInvocationEventChunks
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

theorem fixedDeclaration_visit_fuelEvents
    (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (visit : StatementInvocation) (member : visit ∈ visits)
    (sourceFuel : Nat) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (ready : ExecutionState)
    (visitFuel : visit.fuel = sourceFuel + 1)
    (visitStatement : visit.statement = .letS localVar expression origin)
    (found : environment.vars[localVar]? = some descriptor)
    (fixed : descriptor.ty.nonfixed = false)
    (rootResult : rootOf environment localVar visit.before = .ok root ready)
    (supported : FuelSupport config sourceFuel (.value environment expression)) :
    SourceHistory config sourceFuel [environment.act, visit.ordinal, 0] (.value environment expression) ready
      (evalValue sourceFuel config environment expression ready) ∧
    ready.construction.events = visit.before.construction.events ∧
    (Goose.Proofs.Exit.stepState visit.outcome).construction.events =
      (Goose.Proofs.Exit.stepState (evalValue sourceFuel config environment expression ready)).construction.events ∧
    EventPrefix visit.before.construction.events (Goose.Proofs.Exit.stepState visit.outcome).construction.events := by
  obtain ⟨tree, initial, final, retained⟩ := fixedDeclaration_visit_sourceEvents replay visit member sourceFuel localVar
    expression origin descriptor root ready visitFuel visitStatement found fixed rootResult
  exact ⟨fuelHistory_exists sourceFuel config _ _ ready supported, initial, final, retained⟩

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
  exact fixedDeclaration_visit_fuelEvents replay visit member sourceFuel localVar expression origin descriptor root ready
    visitFuel visitStatement found fixed rootResult
    ((syntaxFuel_existsWithTails sourceFuel config closed).value environment expression derivation)

theorem statementReplay_fixedSourceEvents
    (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (supported : ∀ sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
      FuelSupport config sourceFuel (.value environment expression)) :
    ∀ visit ∈ visits, ∀ sourceFuel localVar expression origin descriptor root sourceReady,
      visit.fuel = sourceFuel + 1 → visit.statement = .letS localVar expression origin →
      environment.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = false →
      rootOf environment localVar visit.before = .ok root sourceReady →
      SourceHistory config sourceFuel [environment.act, visit.ordinal, 0] (.value environment expression) sourceReady
        (evalValue sourceFuel config environment expression sourceReady) ∧
      (Goose.Proofs.Exit.stepState visit.outcome).construction.events =
        (Goose.Proofs.Exit.stepState (evalValue sourceFuel config environment expression sourceReady)).construction.events := by
  intro visit member sourceFuel localVar expression origin descriptor root sourceReady visitFuel visitStatement found fixed rootResult
  have inMapped : visit.statement ∈ visits.map StatementInvocation.statement := List.mem_map_of_mem member
  rw [replay.sourceOrder] at inMapped
  have inStatements : .letS localVar expression origin ∈ statements := by
    rw [← visitStatement]
    exact List.mem_of_mem_take inMapped
  obtain ⟨history, initial, final, retained⟩ := fixedDeclaration_visit_fuelEvents replay visit member
    sourceFuel localVar expression origin descriptor root sourceReady visitFuel visitStatement found fixed rootResult
    (supported sourceFuel localVar expression origin inStatements)
  exact ⟨history, final⟩

theorem execBlock_fixedSourceEvents (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (scope : Nat)
    (statements : List Stmt) (value : Option Expr) (before ready : ExecutionState)
    (bound : bindAll environment.act before.nextScope pre
      { before with nextScope := before.nextScope + 1 } = .ok () ready)
    (supported : ∀ sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
      FuelSupport config sourceFuel
        (.value { environment with scopes := (scope, before.nextScope) :: environment.scopes } expression)) :
    ∃ outcome visits chunks,
      StatementReplay config { environment with scopes := (scope, before.nextScope) :: environment.scopes }
        fuel 0 statements ready outcome visits ∧
      visits.map StatementInvocation.statement = statements.take visits.length ∧
      (visits.map StatementInvocation.ordinal).Nodup ∧ ChunksAlign (visits.map statementInvocation) chunks ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = ready.construction.events ++ chunks.flatten ∧
      execBlock (fuel + 1) config environment pre channels (.mk scope statements value) before =
        withScope environment scope before.nextScope (fun _ => blockContinuation fuel config
          { environment with scopes := (scope, before.nextScope) :: environment.scopes }
          channels value outcome) { before with nextScope := before.nextScope + 1 } ∧
      ∀ visit ∈ visits, ∀ sourceFuel localVar expression origin descriptor root sourceReady,
        visit.fuel = sourceFuel + 1 → visit.statement = .letS localVar expression origin →
        environment.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = false →
        rootOf { environment with scopes := (scope, before.nextScope) :: environment.scopes } localVar visit.before = .ok root sourceReady →
        SourceHistory config sourceFuel [environment.act, visit.ordinal, 0]
          (.value { environment with scopes := (scope, before.nextScope) :: environment.scopes } expression) sourceReady
          (evalValue sourceFuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } expression sourceReady) ∧
        (Goose.Proofs.Exit.stepState visit.outcome).construction.events =
          (Goose.Proofs.Exit.stepState
            (evalValue sourceFuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } expression sourceReady)).construction.events := by
  obtain ⟨outcome, visits, chunks, replay, forest, ordered, once, aligned, finalEq, execution⟩ :=
    execBlock_initializerEventChunks fuel config environment pre channels scope statements value before ready bound
  refine ⟨outcome, visits, chunks, replay, ordered, once, aligned, finalEq, execution, ?_⟩
  exact statementReplay_fixedSourceEvents replay supported

#print axioms statementReplay_fixedSourceEvents
#print axioms execBlock_fixedSourceEvents
#print axioms fixedDeclaration_visit_fuelEvents
#print axioms fixedDeclaration_visit_syntaxEvents
#print axioms fixedDeclarationContinuation_events
#print axioms fixedDeclaration_visit_sourceEvents
end Goose.Proofs.ConstructionGhostFixedDeclarationEvents
