import Goose.Proofs.ConstructionGhostResultScope
import Goose.Proofs.ConstructionAcceptedEntryInvocation

namespace Goose.Proofs.ConstructionGhostEntry
open Goose.Construct Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostBlockInitializers Goose.Proofs.ConstructionGhostResultScope
open Goose.Proofs.ConstructionAcceptedExecution

def activationBodyContinuation (result : ExecutionStep (Flow × List Carrier)) : ExecutionStep (List Carrier) :=
  match result with
  | .ok (.normal _, carriers) state => .ok carriers state
  | .ok _ state => .stop (.fault .flow) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem zeroGlobalEntry_initializerForest (fuel : Nat) (config : EvalConfig)
    (context : Context) (implementation : Impl) (scope : Nat) (statements : List Stmt)
    (noGlobals : config.module.globals.size = 0)
    (contextFound : config.module.contexts[config.module.entry]? = some context)
    (implementationFound : config.module.impls[context.impl]? = some implementation)
    (parametersEmpty : implementation.params = #[]) (resultsEmpty : implementation.results = #[])
    (body : implementation.body = .mk scope statements none) :
    let activation : RuntimeActivation := ⟨context.impl, 0, implementation.vars, [], []⟩
    let activated := { ExecutionState.initial with nextAct := 1, activations := [activation] }
    let ready := resultScopeStart activation scope activated
    ∃ outcome visits,
      StatementReplay config { activation with scopes := [(scope, activated.nextScope)] }
        (fuel + 1) 0 statements ready outcome visits ∧
      FixedOrMaterializedInitializerForest config
        { activation with scopes := [(scope, activated.nextScope)] } visits ∧
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
  let activation : RuntimeActivation := ⟨context.impl, 0, implementation.vars, [], []⟩
  let activated := { ExecutionState.initial with nextAct := 1, activations := [activation] }
  let ready := resultScopeStart activation scope activated
  have bound : bindAll activation.act activated.nextScope [] ready = .ok () ready := by
    simp [bindAll, bind, pure]
  obtain ⟨outcome, visits, replay, forest, execution⟩ := execResultScope_initializerForest (fuel + 1) config activation
    [] [] scope statements none
    (fun environment expression => withCompletionChannels [] (expressionOrigin expression)
      (fun channels => evalProduce (fuel + 1) config environment channels expression)) activated ready bound
  refine ⟨outcome, visits, replay, forest, ?_⟩
  rw [zeroGlobals_runModule_entry (fuel + 4) config context implementation noGlobals contextFound implementationFound resultsEmpty]
  have depth : ExecutionState.initial.activations.length < Goose.Core.maxCallDepth := by
    simp [ExecutionState.initial, Goose.Core.maxCallDepth]
  have call := entryCallStep (fuel + 2) config ⟨0, 0, #[], [], []⟩ .initial context implementation
    contextFound implementationFound parametersEmpty resultsEmpty depth
  simp only [ExecutionState.initial, Nat.add_assoc, Nat.reduceAdd] at call
  simp only [bind, ExecutionState.initial]
  rw [call]
  have bodyExecution : execActivationBody (fuel + 2) config activation [] implementation.body activated =
      activationBodyContinuation (withScope activation scope activated.nextScope (fun _ =>
        resultScopeContinuation [] none
          (fun expression => withCompletionChannels [] (expressionOrigin expression)
            (fun channels => evalProduce (fuel + 1) config
              { activation with scopes := [(scope, activated.nextScope)] } channels expression)) outcome) ready) := by
    simp only [execActivationBody, body, bind]
    rw [execution]
    cases result : withScope activation scope activated.nextScope (fun _ =>
      resultScopeContinuation [] none
        (fun expression => withCompletionChannels [] (expressionOrigin expression)
          (fun channels => evalProduce (fuel + 1) config
            { activation with scopes := [(scope, activated.nextScope)] } channels expression)) outcome) ready with
    | ok pair state => cases pair with | mk flow carriers => cases flow <;> simp [activationBodyContinuation, result, bind, pure, fault, EvalM.stop]
    | stop | escape | jump => simp [activationBodyContinuation, result]
  simp only [activation, activated, ExecutionState.initial] at bodyExecution
  simp only [enterActivation, implementationFound, resultsEmpty, Array.toList_empty, List.map_nil, finishActivation]
  simp only [bind, finishActivation]
  rw [bodyExecution]
  simp only [ready, activation, activated, ExecutionState.initial]
  all_goals split <;> simp_all [bind, pure]
  all_goals split <;> simp_all [bind, pure]
  all_goals split <;> simp_all [bind, pure]

private def witnessModule : Module :=
  ⟨#[], #[], #[], #[⟨"entry", #[], #[],
    #[⟨"x", .int .i64, .immutable, 0, 0⟩, ⟨"y", .varr (.int .i64), .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.blockE (.mk 1 [.print [.text "first"] 0] (some (.lit .i64 7))) 0) 0,
      .letS 1 (.blockE (.mk 2 [.print [.text "second"] 0]
        (some (.arrLit (.arr (.int .i64) 2) [.lit .i64 7, .lit .i64 8] 0))) 0) 0] none, .unknown⟩],
    #[⟨0, "entry", [], [], []⟩], 0, #[], #[], #[]⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem entryWitness_sideEffect :
    ∃ state, runModule 100 ⟨.release, witnessModule⟩ .initial = .ok () state ∧
      state.construction.stdout.data.toList =
        [102, 105, 114, 115, 116, 10, 115, 101, 99, 111, 110, 100, 10] := by
  refine ⟨stepState (runModule 100 ⟨.release, witnessModule⟩ .initial), ?_, ?_⟩ <;>
    unfold stepState witnessModule <;> cbv

#print axioms entryWitness_sideEffect
#print axioms zeroGlobalEntry_initializerForest
end Goose.Proofs.ConstructionGhostEntry
