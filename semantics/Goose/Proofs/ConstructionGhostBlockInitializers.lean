import Goose.Proofs.ConstructionGhostBlock
import Goose.Proofs.ConstructionGhostDeclaration
import Goose.Proofs.ConstructionGhostNonfixedDeclaration

namespace Goose.Proofs.ConstructionGhostBlockInitializers
open Goose.Construct Goose.Proofs.ConstructionGhostInvocation Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostBlock Goose.Proofs.ConstructionGhostDeclaration
open Goose.Proofs.ConstructionGhostNonfixedDeclaration Goose.Proofs.ConstructionGhostMaterialization

def FixedOrMaterializedInitializerForest (config : EvalConfig) (environment : RuntimeActivation)
    (visits : List StatementInvocation) : Prop :=
  ∀ visit ∈ visits, ∀ sourceFuel localVar expression origin descriptor root ready,
    visit.fuel = sourceFuel + 1 → visit.statement = .letS localVar expression origin →
    environment.vars[localVar]? = some descriptor →
    rootOf environment localVar visit.before = .ok root ready →
    (descriptor.ty.nonfixed = false →
      EvaluationTree config environment sourceFuel [environment.act, visit.ordinal, 0] expression ready
        (evalValue sourceFuel config environment expression ready) ∧
      visit.outcome = fixedDeclarationContinuation root (evalValue sourceFuel config environment expression ready)) ∧
    (∀ implementation count, descriptor.ty.nonfixed = true →
      config.module.impls[environment.implementation]? = some implementation →
      (implementation.results.toList.zipIdx.find? fun (result, _) =>
        result.namedLocal == some localVar) = none →
      ordinaryProducerCount? sourceFuel ⟨config.module, environment.vars⟩ expression = some count →
      EvaluationTree config environment sourceFuel [environment.act, visit.ordinal, 0] expression ready
        (evalValue sourceFuel config environment expression ready) ∧
      visit.outcome = declarationAfterMaterialization sourceFuel config environment descriptor root expression origin
        (materializationContinuation (evalValue sourceFuel config environment expression ready)))

theorem statementReplay_initializerForest {config : EvalConfig} {environment : RuntimeActivation}
    {fuel offset : Nat} {statements : List Stmt} {before : ExecutionState}
    {outcome : ExecutionStep Flow} {visits : List StatementInvocation}
    (replay : StatementReplay config environment fuel offset statements before outcome visits) :
    FixedOrMaterializedInitializerForest config environment visits := by
  intro visit member sourceFuel localVar expression origin descriptor root ready visitFuel visitStatement found rootResult
  constructor
  · intro fixed
    exact fixedDeclaration_visit_ghost replay visit member sourceFuel localVar expression origin descriptor root ready
      visitFuel visitStatement found fixed rootResult
  · intro implementation count nonfixed implementationFound notNamed materialized
    obtain ⟨tree, execution⟩ := nonfixedDeclaration_materialized sourceFuel config environment
      [environment.act, visit.ordinal] localVar expression origin visit.before ready descriptor root implementation count
      found nonfixed rootResult implementationFound notNamed materialized
    refine ⟨tree, ?_⟩
    have actual := statementVisit_executes replay visit member
    rw [visitFuel, visitStatement, execution] at actual
    exact actual.symm

theorem execBlock_initializerForest (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (scope : Nat)
    (statements : List Stmt) (value : Option Expr) (before ready : ExecutionState)
    (bound : bindAll environment.act before.nextScope pre
      { before with nextScope := before.nextScope + 1 } = .ok () ready) :
    ∃ outcome visits,
      StatementReplay config { environment with scopes := (scope, before.nextScope) :: environment.scopes }
        fuel 0 statements ready outcome visits ∧
      FixedOrMaterializedInitializerForest config { environment with scopes := (scope, before.nextScope) :: environment.scopes } visits ∧
      execBlock (fuel + 1) config environment pre channels (.mk scope statements value) before =
        withScope environment scope before.nextScope (fun _ => blockContinuation fuel config
          { environment with scopes := (scope, before.nextScope) :: environment.scopes }
          channels value outcome) { before with nextScope := before.nextScope + 1 } := by
  obtain ⟨outcome, visits, replay, execution⟩ :=
    execBlock_statementReplay fuel config environment pre channels scope statements value before ready bound
  exact ⟨outcome, visits, replay, statementReplay_initializerForest replay, execution⟩

private def witnessConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[⟨"entry", #[], #[],
    #[⟨"x", .int .i64, .immutable, 0, 0⟩, ⟨"y", .varr (.int .i64), .immutable, 0, 0⟩],
    .mk 0 [] none, .unknown⟩], #[], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 4,
  #[⟨"x", .int .i64, .immutable, 0, 0⟩, ⟨"y", .varr (.int .i64), .immutable, 0, 0⟩], [], []⟩
private def witnessBlock : Block := .mk 0
  [.letS 0 (.blockE (.mk 1 [.print [.text "first"] 0] (some (.lit .i64 7))) 0) 0,
   .letS 1 (.blockE (.mk 2 [.print [.text "second"] 0]
     (some (.arrLit (.arr (.int .i64) 2) [.lit .i64 7, .lit .i64 8] 0))) 0) 0] none
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem blockInitializerWitness :
    ∃ state, execBlock 60 witnessConfig witnessEnvironment [] [] witnessBlock .initial =
      .ok (.normal .unit) state ∧ state.construction.stdout.data.toList =
        [102, 105, 114, 115, 116, 10, 115, 101, 99, 111, 110, 100, 10] := by
  refine ⟨stepState (execBlock 60 witnessConfig witnessEnvironment [] [] witnessBlock .initial), ?_, ?_⟩ <;>
    unfold witnessConfig witnessEnvironment witnessBlock stepState <;> cbv

#print axioms blockInitializerWitness
#print axioms statementReplay_initializerForest
#print axioms execBlock_initializerForest
end Goose.Proofs.ConstructionGhostBlockInitializers
