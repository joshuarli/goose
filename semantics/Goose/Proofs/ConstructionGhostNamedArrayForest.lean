import Goose.Proofs.ConstructionGhostNamedDeclaration
import Goose.Proofs.ConstructionGhostDirectArrayForest

namespace Goose.Proofs.ConstructionGhostNamedArrayForest
open Goose.Construct Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostDeclaration
open Goose.Proofs.ConstructionGhostNamedDeclaration Goose.Proofs.ConstructionGhostElements
open Goose.Proofs.ConstructionInvocationReplay Goose.Proofs.ConstructionInitializerLoopReplay
open Goose.Proofs.ConstructionGhostBlockInitializers Goose.Proofs.ConstructionGhostDirectArrayForest
open Goose.Proofs.ConstructionGhostBlock

def NamedArrayInitializerForest (config : EvalConfig) (environment : RuntimeActivation)
    (visits : List StatementInvocation) : Prop :=
  ∀ visit ∈ visits, ∀ fuel localVar ty operands expressionOrigin origin descriptor root implementation
      result index incoming selected destination current pending arrayPending element rootReady selectedReady
      destinationReady renewedReady buildReady prepared elementsReady,
    visit.fuel = fuel + 3 → visit.statement = .letS localVar (.arrLit ty operands expressionOrigin) origin →
    environment.vars[localVar]? = some descriptor → descriptor.ty.nonfixed = true →
    rootOf environment localVar visit.before = .ok root rootReady →
    config.module.impls[environment.implementation]? = some implementation →
    (implementation.results.toList.zipIdx.find? fun (candidate, _) => candidate.namedLocal == some localVar) = some (result, index) →
    environment.channels[index]? = some (.construct incoming) →
    liftConstruction origin (renewReceivingDestination incoming) rootReady = .ok selected selectedReady →
    getDestination selected selectedReady = .ok pending destinationReady → pending.capability.request = .value →
    liftConstruction origin (renewReceivingDestination incoming) destinationReady = .ok destination renewedReady →
    liftConstruction origin (prepareNamedBinding destination descriptor.ty) renewedReady = .ok () buildReady →
    liftConstruction expressionOrigin (renewReceivingDestination destination) buildReady = .ok current prepared →
    getDestination current prepared = .ok arrayPending elementsReady →
    elementType arrayPending.capability.logicalType = some element → element.nonfixed = false →
    ∃ outcome children,
      OperandReplay (fun operand => buildElement (fuel + 1) config environment current element operand)
        0 operands [] elementsReady outcome children ∧
      (∀ child ∈ children, FixedElementTree config environment current element (fuel + 1)
        (child.path ([environment.act, visit.ordinal] ++ [0])) child.operand child.before child.outcome) ∧
      children.map Invocation.operand = operands.take children.length ∧
      (children.map Invocation.ordinal).Nodup ∧
      visit.outcome = namedDeclarationAfterBuild descriptor root origin destination
        (protectDestination expressionOrigin current (fun _ =>
          match discardValues outcome with
          | .ok _ state => receivingAction expressionOrigin current finishDestination state
          | .stop reason state => .stop reason state
          | .escape address carriers state => .escape address carriers state
          | .jump target kind state => .jump target kind state) prepared)

theorem statementReplay_namedArrayForest {config : EvalConfig} {environment : RuntimeActivation}
    {fuel offset : Nat} {statements : List Stmt} {before : ExecutionState}
    {outcome : ExecutionStep Flow} {visits : List StatementInvocation}
    (replay : StatementReplay config environment fuel offset statements before outcome visits) :
    NamedArrayInitializerForest config environment visits := by
  intro visit member sourceFuel localVar ty operands expressionOrigin origin descriptor root implementation
    result index incoming selected destination current pending arrayPending element rootReady selectedReady
    destinationReady renewedReady buildReady prepared elementsReady visitFuel visitStatement found nonfixed rootResult
    implementationFound named channelFound selectedResult pendingResult valueRequest renewedResult namedPrepared
    arrayRenewed arrayFound elementFound fixedElement
  obtain ⟨result, children, sourceReplay, forest, ordered, once, execution⟩ :=
    namedArrayDeclaration_ghost sourceFuel config environment [environment.act, visit.ordinal] localVar
      ty operands expressionOrigin origin visit.before rootReady selectedReady destinationReady renewedReady buildReady
      prepared elementsReady descriptor root implementation result index incoming selected destination current pending
      arrayPending element found nonfixed rootResult implementationFound named channelFound selectedResult pendingResult
      valueRequest renewedResult namedPrepared arrayRenewed arrayFound elementFound fixedElement
  refine ⟨result, children, sourceReplay, forest, ordered, once, ?_⟩
  have actual := statementVisit_executes replay visit member
  rw [visitFuel, visitStatement, execution] at actual
  exact actual.symm

theorem execBlock_arrayInitializerForests (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (scope : Nat)
    (statements : List Stmt) (value : Option Expr) (before ready : ExecutionState)
    (bound : bindAll environment.act before.nextScope pre
      { before with nextScope := before.nextScope + 1 } = .ok () ready) :
    ∃ outcome visits,
      StatementReplay config { environment with scopes := (scope, before.nextScope) :: environment.scopes }
        fuel 0 statements ready outcome visits ∧
      FixedOrMaterializedInitializerForest config { environment with scopes := (scope, before.nextScope) :: environment.scopes } visits ∧
      DirectArrayInitializerForest config { environment with scopes := (scope, before.nextScope) :: environment.scopes } visits ∧
      NamedArrayInitializerForest config { environment with scopes := (scope, before.nextScope) :: environment.scopes } visits ∧
      execBlock (fuel + 1) config environment pre channels (.mk scope statements value) before =
        withScope environment scope before.nextScope (fun _ => blockContinuation fuel config
          { environment with scopes := (scope, before.nextScope) :: environment.scopes }
          channels value outcome) { before with nextScope := before.nextScope + 1 } := by
  obtain ⟨outcome, visits, replay, forest, execution⟩ :=
    execBlock_initializerForest fuel config environment pre channels scope statements value before ready bound
  exact ⟨outcome, visits, replay, forest, statementReplay_directArrayForest replay,
    statementReplay_namedArrayForest replay, execution⟩

private def witnessConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[⟨"entry", #[], #[⟨.varr (.int .i64), .value, some 0⟩],
    #[⟨"x", .varr (.int .i64), .immutable, 0, 0⟩], .mk 0 [] none, .unknown⟩], #[], 0, #[], #[], #[]⟩⟩
private def witnessAction : EvalM Flow := do
  let destination ← newDestination witnessConfig.layout 4 (.varr (.int .i64)) .value 0
  let environment : RuntimeActivation := ⟨0, 4,
    #[⟨"x", .varr (.int .i64), .immutable, 0, 0⟩], [], [.construct destination]⟩
  execBlock 60 witnessConfig environment [] [] (.mk 0 [.letS 0 (.arrLit (.varr (.int .i64))
    [.blockE (.mk 1 [.print [.text "once"] 0] (some (.lit .i64 7))) 0, .lit .i64 8] 0) 0] none)
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem namedBlockWitness :
    ∃ state, witnessAction .initial = .ok (.normal .unit) state ∧
      state.construction.stdout.data.toList = [111, 110, 99, 101, 10] := by
  refine ⟨stepState (witnessAction .initial), ?_, ?_⟩ <;>
    unfold witnessAction witnessConfig stepState <;> cbv

#print axioms namedBlockWitness
#print axioms execBlock_arrayInitializerForests
#print axioms statementReplay_namedArrayForest
end Goose.Proofs.ConstructionGhostNamedArrayForest
