import Goose.Proofs.ConstructionGhostModuleInitializerEvents

namespace Goose.Proofs.ConstructionGhostEntryInitializerEvents
open Goose.Construct Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostResultScope Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostStatementEvents Goose.Proofs.ConstructionGhostInvocationEventChunks
open Goose.Proofs.ConstructionGhostActivationEvents Goose.Proofs.ConstructionGhostModuleInitializerEvents
open Goose.Proofs.ConstructionGhostMaterializedDeclarationEvents

theorem entryCall_initializerEvents (fuel : Nat) (config : EvalConfig) (before : ExecutionState)
    (contextId : Goose.Core.ContextId) (context : Context) (implementation : Impl)
    (contextFound : config.module.contexts[contextId]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
    (depth : before.activations.length < Goose.Core.maxCallDepth)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (body : implementation.body = .mk scope statements tail)
    (supported : ∀ sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
      FuelSupport config sourceFuel (.value ⟨context.impl, before.nextAct, implementation.vars, [(scope, before.nextScope)], []⟩ expression)) :
    let activation : RuntimeActivation := ⟨context.impl, before.nextAct, implementation.vars, [], []⟩
    let activated := { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }
    let ready := resultScopeStart activation scope activated
    let scopedEnvironment := { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
    ∃ outcome visits chunks,
      StatementReplay config scopedEnvironment fuel 0 statements ready outcome visits ∧
      visits.map StatementInvocation.statement = statements.take visits.length ∧
      (visits.map StatementInvocation.ordinal).Nodup ∧ ChunksAlign (visits.map statementInvocation) chunks ∧
      (Goose.Proofs.Exit.stepState outcome).construction.events = ready.construction.events ++ chunks.flatten ∧
      FixedVisitSourceEvents config scopedEnvironment visits ∧ MaterializedVisitSourceEvents config scopedEnvironment visits ∧
      invokeCall (fuel + 3) config ⟨0, 0, #[], [], []⟩ contextId [] [] 0 before =
        ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
          deliverCarriers (fuel + 2) config.layout [] carriers 0) activated) ∧
      enterActivation (fuel + 2) config activation [] implementation.body 0 activated =
        finishActivation config.layout activation (implementation.results.toList.map (·.ty)) 0
          (execActivationBody (fuel + 1) config activation [] implementation.body) activated := by
  dsimp only
  let activation : RuntimeActivation := ⟨context.impl, before.nextAct, implementation.vars, [], []⟩
  let activated := { before with nextAct := before.nextAct + 1, activations := activation :: before.activations }
  let ready := resultScopeStart activation scope activated
  have bound : bindAll activation.act activated.nextScope [] ready = .ok () ready := by simp [bindAll, bind, pure]
  have localSupported : ∀ sourceFuel localVar expression origin, .letS localVar expression origin ∈ statements →
      FuelSupport config sourceFuel (.value { activation with scopes := (scope, activated.nextScope) :: activation.scopes } expression) := by
    intro sourceFuel localVar expression origin member
    exact supported sourceFuel localVar expression origin member
  obtain ⟨outcome, visits, chunks, replay, ordered, once, aligned, finalEq, execution, fixed⟩ :=
    activationBody_fixedSourceEvents fuel config activation [] scope statements tail activated ready bound localSupported
  refine ⟨outcome, visits, chunks, replay, ordered, once, aligned, finalEq, fixed, ?_, ?_, ?_⟩
  · exact statementReplay_materializedSourceEvents replay localSupported
  · exact emptyCall_enter (fuel + 1) config ⟨0, 0, #[], [], []⟩ contextId context implementation 0 before
      contextFound implementationFound parametersEmpty resultsEmpty depth
  · simp only [enterActivation, implementationFound]

#print axioms entryCall_initializerEvents
end Goose.Proofs.ConstructionGhostEntryInitializerEvents
