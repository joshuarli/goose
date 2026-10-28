import Goose.Proofs.ConstructionGhostActivationEvents

namespace Goose.Proofs.ConstructionGhostModuleActivationEvents
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostResultScope Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostStatementEvents Goose.Proofs.ConstructionGhostInvocationEventChunks
open Goose.Proofs.ConstructionGhostActivationEvents

theorem runModule_fixedEntryEvents (fuel : Nat) (config : EvalConfig) (context : Context) (implementation : Impl)
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
    ∃ outcome visits chunks,
      StatementReplay config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
        fuel 0 statements ready outcome visits ∧
      visits.map StatementInvocation.statement = statements.take visits.length ∧
      (visits.map StatementInvocation.ordinal).Nodup ∧ ChunksAlign (visits.map statementInvocation) chunks ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = ready.construction.events ++ chunks.flatten ∧
      runModule (fuel + 3) config .initial = moduleCallResult
        ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated) ∧
      enterActivation (fuel + 2) config activation [] implementation.body 0 activated =
        finishActivation config.layout activation (implementation.results.toList.map (·.ty)) 0
          (execActivationBody (fuel + 1) config activation [] implementation.body) activated ∧
      execActivationBody (fuel + 1) config activation [] (.mk scope statements tail) activated =
        activationBodyFinish (withScope activation scope activated.nextScope (fun _ =>
          resultScopeContinuation activation.channels tail
            (fun expression => withCompletionChannels activation.channels (expressionOrigin expression)
              (fun channels => evalProduce fuel config
                { activation with scopes := (scope, activated.nextScope) :: activation.scopes } channels expression)) outcome)
          (resultScopeStart activation scope activated)) ∧
      ∀ visit ∈ visits, ∀ sourceFuel localVar expression origin descriptor root sourceReady,
        visit.fuel = sourceFuel + 1 → visit.statement = .letS localVar expression origin →
        implementation.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = false →
        rootOf { activation with scopes := (scope, activated.nextScope) :: activation.scopes } localVar visit.before = .ok root sourceReady →
        SourceHistory config sourceFuel [activation.act, visit.ordinal, 0]
          (.value { activation with scopes := (scope, activated.nextScope) :: activation.scopes } expression) sourceReady
          (evalValue sourceFuel config { activation with scopes := (scope, activated.nextScope) :: activation.scopes } expression sourceReady) ∧
        (Goose.Proofs.Exit.stepState visit.outcome).construction.events =
          (Goose.Proofs.Exit.stepState
            (evalValue sourceFuel config { activation with scopes := (scope, activated.nextScope) :: activation.scopes } expression sourceReady)).construction.events := by
  dsimp only
  let activation : RuntimeActivation := ⟨context.impl, 0, implementation.vars, [], []⟩
  let activated : ExecutionState := { ExecutionState.initial with nextAct := 1, activations := [activation] }
  let ready := resultScopeStart activation scope activated
  have bound : bindAll activation.act activated.nextScope [] ready = .ok () ready := by simp [bindAll, bind, pure]
  have localSupported : ∀ sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
      FuelSupport config sourceFuel (.value { activation with scopes := (scope, activated.nextScope) :: activation.scopes } expression) := by
    intro sourceFuel localVar expression origin member
    exact supported sourceFuel localVar expression origin member
  obtain ⟨outcome, visits, chunks, replay, ordered, once, aligned, finalEq, execution, sources⟩ :=
    activationBody_fixedSourceEvents fuel config activation [] scope statements tail activated ready bound localSupported
  refine ⟨outcome, visits, chunks, replay, ordered, once, aligned, finalEq, ?_, ?_, execution, sources⟩
  · have module : runModule (fuel + 3) config .initial = moduleCallResult
        (invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 .initial) := by
      simp only [runModule, noGlobals, List.range_zero, initGlobals, getImplementation, contextFound,
        implementationFound, resultsEmpty, Array.toList_empty, channelsFor, List.mapM_nil, bind, pure, moduleCallResult]
      cases invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 .initial <;> rfl
    rw [module, emptyCall_enter (fuel + 1) config ⟨0, 0, #[], [], []⟩ config.module.entry context implementation 0 .initial
      contextFound implementationFound parametersEmpty resultsEmpty (by decide)]
    simp [ExecutionState.initial, activation, activated]
  · simp only [enterActivation, implementationFound]

#print axioms runModule_fixedEntryEvents
end Goose.Proofs.ConstructionGhostModuleActivationEvents
