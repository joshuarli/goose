import Goose.Proofs.ConstructionGhostModuleActivationEvents
import Goose.Proofs.ConstructionGhostMaterializedDeclarationEvents

namespace Goose.Proofs.ConstructionGhostModuleInitializerEvents
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostResultScope Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostStatementEvents Goose.Proofs.ConstructionGhostInvocationEventChunks
open Goose.Proofs.ConstructionGhostModuleActivationEvents Goose.Proofs.ConstructionGhostMaterializedDeclarationEvents

def FixedVisitSourceEvents (config : EvalConfig) (environment : RuntimeActivation) (visits : List StatementInvocation) : Prop :=
  ∀ visit ∈ visits, ∀ sourceFuel localVar expression origin descriptor root ready,
    visit.fuel = sourceFuel + 1 → visit.statement = .letS localVar expression origin →
    environment.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = false →
    rootOf environment localVar visit.before = .ok root ready →
    SourceHistory config sourceFuel [environment.act, visit.ordinal, 0] (.value environment expression) ready
      (evalValue sourceFuel config environment expression ready) ∧
    (Goose.Proofs.Exit.stepState visit.outcome).construction.events =
      (Goose.Proofs.Exit.stepState (evalValue sourceFuel config environment expression ready)).construction.events

theorem runModule_entryInitializerEvents (fuel : Nat) (config : EvalConfig) (context : Context) (implementation : Impl)
    (noGlobals : config.module.globals.size = 0)
    (contextFound : config.module.contexts[config.module.entry]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (body : implementation.body = .mk scope statements tail)
    (supported : ∀ sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
      FuelSupport config sourceFuel (.value ⟨context.impl, 0, implementation.vars, [(scope, 0)], []⟩ expression)) :
    let activation : RuntimeActivation := ⟨context.impl, 0, implementation.vars, [], []⟩
    let activated : ExecutionState := { ExecutionState.initial with nextAct := 1, activations := [activation] }
    let ready := resultScopeStart activation scope activated
    let scopedEnvironment := { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
    ∃ outcome visits chunks,
      StatementReplay config scopedEnvironment fuel 0 statements ready outcome visits ∧
      visits.map StatementInvocation.statement = statements.take visits.length ∧
      (visits.map StatementInvocation.ordinal).Nodup ∧ ChunksAlign (visits.map statementInvocation) chunks ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = ready.construction.events ++ chunks.flatten ∧
      FixedVisitSourceEvents config scopedEnvironment visits ∧ MaterializedVisitSourceEvents config scopedEnvironment visits ∧
      runModule (fuel + 3) config .initial = moduleCallResult
        ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated) := by
  dsimp only
  obtain ⟨outcome, visits, chunks, replay, ordered, once, aligned, finalEq, moduleExecution, enterExecution, bodyExecution, fixed⟩ :=
    runModule_fixedEntryEvents fuel config context implementation noGlobals contextFound implementationFound parametersEmpty resultsEmpty
      scope statements tail body supported
  refine ⟨outcome, visits, chunks, replay, ordered, once, aligned, finalEq, fixed, ?_, moduleExecution⟩
  apply statementReplay_materializedSourceEvents replay
  intro sourceFuel localVar expression origin member
  exact supported sourceFuel localVar expression origin member

#print axioms runModule_entryInitializerEvents
end Goose.Proofs.ConstructionGhostModuleInitializerEvents
