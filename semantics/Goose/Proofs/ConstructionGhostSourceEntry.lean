import Goose.Proofs.ConstructionGhostSourceMutual
import Goose.Proofs.ConstructionGhostEntry

namespace Goose.Proofs.ConstructionGhostSourceEntry
open Goose.Construct Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostEntry
open Goose.Proofs.ConstructionGhostResultScope Goose.Proofs.ConstructionGhostBlockInitializers

theorem entry_sourceHistory (fuel : Nat) (config : EvalConfig)
    (context : Context) (implementation : Impl) (scope : Nat) (statements : List Stmt)
    (noGlobals : config.module.globals.size = 0)
    (contextFound : config.module.contexts[config.module.entry]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
    (body : implementation.body = .mk scope statements none)
    (supported : ∀ environment, SupportedOperation config (.statements environment statements)) :
    let activation : RuntimeActivation := ⟨context.impl, 0, implementation.vars, [], []⟩
    let activated := { ExecutionState.initial with nextAct := 1, activations := [activation] }
    let ready := resultScopeStart activation scope activated
    ∃ outcome,
      SourceHistory config (fuel + 1) []
        (.statements { activation with scopes := [(scope, activated.nextScope)] } statements) ready outcome ∧
      runModule (fuel + 4) config .initial =
        (finishActivation config.layout activation [] 0 (fun _ =>
          activationBodyContinuation (withScope activation scope activated.nextScope (fun _ =>
            resultScopeContinuation [] none
              (fun expression => withCompletionChannels [] (expressionOrigin expression)
                (fun channels => evalProduce (fuel + 1) config
                  { activation with scopes := [(scope, activated.nextScope)] } channels expression)) outcome) ready)) >>=
          fun carriers => deliverCarriers (fuel + 3) config.layout [] carriers 0 >>= fun carriers =>
            publishCarriers 0 carriers) activated := by
  dsimp only
  obtain ⟨outcome, visits, replay, forest, execution⟩ :=
    zeroGlobalEntry_initializerForest fuel config context implementation scope statements noGlobals
      contextFound implementationFound parametersEmpty resultsEmpty body
  refine ⟨outcome, ?_, execution⟩
  let environment : RuntimeActivation := { (⟨context.impl, 0, implementation.vars, [], []⟩ : RuntimeActivation) with
    scopes := [(scope, ExecutionState.initial.nextScope)] }
  let ready := resultScopeStart ⟨context.impl, 0, implementation.vars, [], []⟩ scope
    { ExecutionState.initial with nextAct := 1, activations := [⟨context.impl, 0, implementation.vars, [], []⟩] }
  have history := history_exists (fuel + 1) config (.statements environment statements) [] ready (supported environment)
  change SourceHistory config (fuel + 1) [] (.statements environment statements) ready
    (execStmts (fuel + 1) config environment statements ready) at history

  rw [replay.sound] at history
  exact history

private def witnessModule : Module :=
  ⟨#[], #[], #[], #[⟨"entry", #[], #[], #[],
    .mk 0 [.expr (.ifE (.bool true) (.mk 1 [.expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0] none) (.mk 2 [] none) 0) 0] none, .unknown⟩],
    #[⟨0, "entry", [], [], []⟩], 0, #[], #[], #[]⟩
private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem entryWitness_runs :
    ∃ state, runModule 40 ⟨.release, witnessModule⟩ .initial = .ok () state := by
  refine ⟨witnessState (runModule 40 ⟨.release, witnessModule⟩ .initial), ?_⟩
  unfold witnessState witnessModule
  cbv

#print axioms entryWitness_runs

#print axioms entry_sourceHistory
end Goose.Proofs.ConstructionGhostSourceEntry
