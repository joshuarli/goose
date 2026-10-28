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

private def witnessCallee : Impl := ⟨"callee", #[], #[], #[],
  .mk 1 [.print [.text "x"] 0, .expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0] none, .unknown⟩
private def witnessCalleeContext : Context := ⟨1, "callee", [], [], []⟩
private def witnessEntry : Impl := ⟨"entry", #[], #[], #[], .mk 0 [.expr (.fill (.arr .unit 3) (.call 1 [] 0) 0) 0] none, .unknown⟩
private def witnessEntryContext : Context := ⟨0, "entry", [], [], []⟩
private def witnessModule : Module :=
  ⟨#[], #[], #[], #[witnessEntry, witnessCallee], #[witnessEntryContext, witnessCalleeContext], 0, #[], #[], #[]⟩

private theorem entryWitness_supported : ∀ environment,
    SupportedOperation ⟨.release, witnessModule⟩ (.statements environment [.expr (.fill (.arr .unit 3) (.call 1 [] 0) 0) 0]) := by
  intro environment
  have bodySupported : ∀ scopedEnvironment, SupportedOperation ⟨.release, witnessModule⟩
      (.statements scopedEnvironment [.print [.text "x"] 0, .expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0]) := by
    intro scopedEnvironment
    exact .sequence scopedEnvironment (.printText scopedEnvironment "x" 0)
      (.sequence scopedEnvironment (.expression scopedEnvironment 0 (.value scopedEnvironment
        (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))) (.empty scopedEnvironment))
  have callee : SupportedOperation ⟨.release, witnessModule⟩ (.call environment 1 0) := by
    apply SupportedOperation.call environment 1 0 witnessCalleeContext witnessCallee
    · rfl
    · rfl
    · rfl
    · rfl
    · intro act
      exact .activation _ 1 _ 0 bodySupported
  exact .sequence environment (.expression environment 0
    (.fill environment .unit 3 0 (.call 1 [] 0) rfl
      (.valueCall environment 1 0 witnessCalleeContext witnessCallee rfl rfl rfl callee))) (.empty environment)

private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem entryWitness_runs :
    ∃ state, runModule 40 ⟨.release, witnessModule⟩ .initial = .ok () state := by
  refine ⟨witnessState (runModule 40 ⟨.release, witnessModule⟩ .initial), ?_⟩
  unfold witnessState witnessModule
  cbv

theorem entryWitness_fillSourceOnce : ∃ state,
    runModule 40 ⟨.release, witnessModule⟩ .initial = .ok () state ∧
    state.construction.stdout.data.toList = [120, 10] := by
  refine ⟨witnessState (runModule 40 ⟨.release, witnessModule⟩ .initial), ?_, ?_⟩ <;>
    unfold witnessState witnessModule witnessEntry witnessEntryContext witnessCallee witnessCalleeContext <;> cbv

#print axioms entryWitness_fillSourceOnce

theorem entryWitness_nestedCallHistory :
    let activation : RuntimeActivation := ⟨0, 0, #[], [], []⟩
    let activated := { ExecutionState.initial with nextAct := 1, activations := [activation] }
    let environment := { activation with scopes := [(0, activated.nextScope)] }
    ∃ outcome state,
      SourceHistory ⟨.release, witnessModule⟩ 37 [] (.statements environment [.expr (.fill (.arr .unit 3) (.call 1 [] 0) 0) 0])
        (resultScopeStart activation 0 activated) outcome ∧
      runModule 40 ⟨.release, witnessModule⟩ .initial = .ok () state := by
  obtain ⟨outcome, history, execution⟩ := entry_sourceHistory 36 ⟨.release, witnessModule⟩ witnessEntryContext
    witnessEntry 0 [.expr (.fill (.arr .unit 3) (.call 1 [] 0) 0) 0] rfl rfl rfl rfl rfl rfl entryWitness_supported
  obtain ⟨state, finished⟩ := entryWitness_runs
  exact ⟨outcome, state, history, finished⟩

#print axioms entryWitness_nestedCallHistory

#print axioms entryWitness_supported
#print axioms entryWitness_runs

#print axioms entry_sourceHistory
end Goose.Proofs.ConstructionGhostSourceEntry
