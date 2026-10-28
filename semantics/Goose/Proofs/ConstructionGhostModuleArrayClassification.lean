import Goose.Proofs.ConstructionGhostArrayElementClassification
import Goose.Proofs.ConstructionGhostModuleResultEvents
import Goose.Proofs.ConstructionGhostDeclaration

namespace Goose.Proofs.ConstructionGhostModuleArrayClassification
open Goose.Construct Goose.Proofs.ConstructionExecution Goose.Proofs.ConstructionInvocationReplay
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostArrayElementClassification
open Goose.Proofs.ConstructionGhostModuleResultEvents Goose.Proofs.ConstructionGhostStatements
open Goose.Proofs.ConstructionGhostDeclaration Goose.Proofs.ConstructionGhostResultScope Goose.Proofs.ConstructionGhostSourceGlobal

theorem moduleEntry_arrayElementClassifications (fuel sourceFuel : Nat) (config : EvalConfig) (activation : RuntimeActivation)
    (implementation : Impl) (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    (activated moduleBefore : ExecutionState) (channels : List Channel) (callResult : ExecutionStep (List Carrier))
    (outcome : ExecutionStep Flow) (visits : List StatementInvocation) (visit : StatementInvocation)
    (path : List Nat) (localVar : Goose.Core.VarId) (incoming current : Goose.Core.DestinationId)
    (ty : Ty) (operands : List Expr) (arrayOrigin origin : Goose.Core.OriginId)
    (initial prepared ready : ExecutionState) (pending : PendingDestination) (element : Ty)
    (found : config.module.impls[activation.implementation]? = some implementation)
    (body : implementation.body = .mk scope statements tail)
    (replay : StatementReplay config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
      fuel 0 statements (resultScopeStart activation scope activated) outcome visits)
    (member : visit ∈ visits)
    (visitFuel : visit.fuel = sourceFuel + 3)
    (visitStatement : visit.statement = .letS localVar (.arrLit ty operands arrayOrigin) origin)
    (supported : ∀ sourceFuel localVar expression statementOrigin, .letS localVar expression statementOrigin ∈ statements →
      FuelSupport config sourceFuel (.value { activation with scopes := (scope, activated.nextScope) :: activation.scopes } expression))
    (call : callResult = ((enterActivation (fuel + 2) config activation [] implementation.body 0 >>= fun carriers =>
      deliverCarriers (fuel + 2) config.layout channels carriers 0) activated))
    (moduleResult : runModule (fuel + 3) config moduleBefore = entryCallResult callResult)
    (occurrence : DeclarationOccurrence (sourceFuel + 2) config
      { activation with scopes := (scope, activated.nextScope) :: activation.scopes } localVar (.arrLit ty operands arrayOrigin)
      origin visit.before (some incoming) initial)
    (renewed : liftConstruction arrayOrigin (renewReceivingDestination incoming) initial = .ok current prepared)
    (destinationFound : getDestination current prepared = .ok pending ready)
    (elementFound : elementType pending.capability.logicalType = some element)
    (elementsSupported : ∀ operand ∈ operands, FuelSupport config (sourceFuel + 1)
      (.element { activation with scopes := (scope, activated.nextScope) :: activation.scopes } current element operand)) :
    ∃ elementOutcome elementVisits,
      OperandReplay (fun operand => buildElement (sourceFuel + 1) config
        { activation with scopes := (scope, activated.nextScope) :: activation.scopes } current element operand)
        0 operands [] ready elementOutcome elementVisits ∧
      elementVisits.map Invocation.operand = operands.take elementVisits.length ∧
      (elementVisits.map Invocation.ordinal).Nodup ∧
      ∀ elementVisit ∈ elementVisits,
        ElementVisitClassification config { activation with scopes := (scope, activated.nextScope) :: activation.scopes }
          current element sourceFuel (path ++ [0]) elementVisit
          (Goose.Proofs.Exit.stepState (runModule (fuel + 3) config moduleBefore)) := by
  obtain ⟨elementOutcome, elementVisits, elementReplay, ordered, once, children⟩ :=
    array_elementClassifications sourceFuel config
      { activation with scopes := (scope, activated.nextScope) :: activation.scopes } path localVar incoming current ty operands arrayOrigin origin
      visit.before initial prepared ready pending element occurrence renewed destinationFound elementFound elementsSupported
  have actual := statementVisit_executes replay visit member
  rw [visitFuel, visitStatement] at actual
  have modulePrefix := moduleEntry_tail_visitPrefix fuel config activation implementation scope statements tail activated moduleBefore
    channels callResult outcome visits visit found body replay member supported call moduleResult
  rw [← actual] at modulePrefix
  refine ⟨elementOutcome, elementVisits, elementReplay, ordered, once, ?_⟩
  intro elementVisit elementMember
  rcases children elementVisit elementMember with ⟨destination, sourceReady, elementOccurrence, unique, child⟩ | terminal
  · left
    refine ⟨destination, sourceReady, elementOccurrence, unique, ?_⟩
    cases destination <;> exact ⟨child.1, eventPrefix_trans _ _ _ child.2 modulePrefix⟩
  · exact Or.inr terminal

#print axioms moduleEntry_arrayElementClassifications
end Goose.Proofs.ConstructionGhostModuleArrayClassification
