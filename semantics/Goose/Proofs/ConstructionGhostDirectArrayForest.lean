import Goose.Proofs.ConstructionGhostEntry

namespace Goose.Proofs.ConstructionGhostDirectArrayForest
open Goose.Construct Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostDeclaration
open Goose.Proofs.ConstructionGhostBlockInitializers Goose.Proofs.ConstructionGhostNonfixedDeclaration
open Goose.Proofs.ConstructionGhostElements Goose.Proofs.ConstructionInvocationReplay
open Goose.Proofs.ConstructionInitializerLoopReplay Goose.Proofs.ConstructionGhostResultScope
open Goose.Proofs.ConstructionGhostEntry

def DirectArrayInitializerForest (config : EvalConfig) (environment : RuntimeActivation)
    (visits : List StatementInvocation) : Prop :=
  ∀ visit ∈ visits, ∀ fuel localVar ty operands expressionOrigin origin descriptor root implementation
      destination current pending element ready buildReady prepared elementsReady,
    visit.fuel = fuel + 3 → visit.statement = .letS localVar (.arrLit ty operands expressionOrigin) origin →
    environment.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = true →
    rootOf environment localVar visit.before = .ok root ready →
    config.module.impls[environment.implementation]? = some implementation →
    (implementation.results.toList.zipIdx.find? fun (result, _) => result.namedLocal == some localVar) = none →
    element.nonfixed = false →
    newDestination config.layout environment.act descriptor.ty .value origin none
      (producerCount? ⟨config.module, environment.vars⟩ (.arrLit ty operands expressionOrigin)) ready =
        .ok destination buildReady →
    liftConstruction expressionOrigin (renewReceivingDestination destination) buildReady = .ok current prepared →
    getDestination current prepared = .ok pending elementsReady →
    elementType pending.capability.logicalType = some element →
    ∃ outcome children,
      OperandReplay (fun operand => buildElement (fuel + 1) config environment current element operand)
        0 operands [] elementsReady outcome children ∧
      (∀ child ∈ children, FixedElementTree config environment current element (fuel + 1)
        (child.path ([environment.act, visit.ordinal] ++ [0])) child.operand child.before child.outcome) ∧
      children.map Invocation.operand = operands.take children.length ∧
      (children.map Invocation.ordinal).Nodup ∧
      visit.outcome = directDeclarationAfterBuild descriptor root origin destination
        (protectDestination expressionOrigin current (fun _ =>
          match discardValues outcome with
          | .ok _ state => receivingAction expressionOrigin current finishDestination state
          | .stop reason state => .stop reason state
          | .escape address carriers state => .escape address carriers state
          | .jump target kind state => .jump target kind state) prepared)

theorem statementReplay_directArrayForest {config : EvalConfig} {environment : RuntimeActivation}
    {fuel offset : Nat} {statements : List Stmt} {before : ExecutionState}
    {outcome : ExecutionStep Flow} {visits : List StatementInvocation}
    (replay : StatementReplay config environment fuel offset statements before outcome visits) :
    DirectArrayInitializerForest config environment visits := by
  intro visit member sourceFuel localVar ty operands expressionOrigin origin descriptor root implementation
    destination current pending element ready buildReady prepared elementsReady visitFuel visitStatement found nonfixed
    rootResult implementationFound notNamed fixedElement allocated renewed pendingFound elementFound
  obtain ⟨result, children, sourceReplay, forest, ordered, once, execution⟩ :=
    directArrayDeclaration_ghost sourceFuel config environment [environment.act, visit.ordinal] localVar
      ty operands expressionOrigin origin visit.before ready buildReady prepared elementsReady descriptor root implementation
      destination current pending element found nonfixed rootResult implementationFound notNamed fixedElement
      allocated renewed pendingFound elementFound
  refine ⟨result, children, sourceReplay, forest, ordered, once, ?_⟩
  have actual := statementVisit_executes replay visit member
  rw [visitFuel, visitStatement, execution] at actual
  exact actual.symm

theorem zeroGlobalEntry_initializerForests (fuel : Nat) (config : EvalConfig)
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
      DirectArrayInitializerForest config
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
  obtain ⟨outcome, visits, replay, forest, execution⟩ :=
    zeroGlobalEntry_initializerForest fuel config context implementation scope statements noGlobals
      contextFound implementationFound parametersEmpty resultsEmpty body
  exact ⟨outcome, visits, replay, forest, statementReplay_directArrayForest replay, execution⟩

#print axioms zeroGlobalEntry_initializerForests
private def witnessModule : Module :=
  ⟨#[], #[], #[], #[⟨"entry", #[], #[], #[⟨"x", .varr (.int .i64), .immutable, 0, 0⟩],
    .mk 0 [.letS 0 (.arrLit (.varr (.int .i64))
      [.blockE (.mk 1 [.print [.text "once"] 0] (some (.lit .i64 7))) 0, .lit .i64 8] 0) 0] none, .unknown⟩],
    #[⟨0, "entry", [], [], []⟩], 0, #[], #[], #[]⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem directArrayEntryWitness :
    ∃ state, runModule 100 ⟨.release, witnessModule⟩ .initial = .ok () state ∧
      state.construction.stdout.data.toList = [111, 110, 99, 101, 10] := by
  refine ⟨stepState (runModule 100 ⟨.release, witnessModule⟩ .initial), ?_, ?_⟩ <;>
    unfold stepState witnessModule <;> cbv

#print axioms directArrayEntryWitness
#print axioms statementReplay_directArrayForest
end Goose.Proofs.ConstructionGhostDirectArrayForest
