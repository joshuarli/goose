import Goose.Proofs.ConstructionGhostDeclarationSelection
import Goose.Proofs.ConstructionGhostDeclaration

namespace Goose.Proofs.ConstructionGhostDeclarationReplay
open Goose.Construct Goose.Proofs.ConstructionGhostStatements Goose.Proofs.ConstructionGhostDeclaration
open Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel
open Goose.Proofs.ConstructionGhostDeclarationOnce Goose.Proofs.ConstructionGhostDeclarationSelection
open Goose.Proofs.ConstructionGhostDeclarationFallback Goose.Proofs.ConstructionGhostSyntaxFuel

theorem declaration_visit_classification
    {config : EvalConfig} {environment : RuntimeActivation} {fuel offset : Nat} {statements : List Stmt}
    {before : ExecutionState} {outcome : ExecutionStep Flow} {visits : List StatementInvocation}
    (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (visit : StatementInvocation) (member : visit ∈ visits)
    (sourceFuel : Nat) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (visitFuel : visit.fuel = sourceFuel + 1) (visitStatement : visit.statement = .letS localVar expression origin)
    (closed : ClosedModuleWithTails config) (derivation : StatementSyntax config visit.statement) :
    (∃ destination ready, DeclarationOccurrence sourceFuel config environment localVar expression origin visit.before destination ready ∧
      (∀ other otherReady, DeclarationOccurrence sourceFuel config environment localVar expression origin visit.before other otherReady →
        destination = other ∧ ready = otherReady) ∧
      match destination with
      | none => SourceHistory config sourceFuel [environment.act, visit.ordinal, 0] (.value environment expression) ready
          (evalValue sourceFuel config environment expression ready) ∧
          Goose.Proofs.ConstructionExecution.EventPrefix
            (Goose.Proofs.Exit.stepState (evalValue sourceFuel config environment expression ready)).construction.events
            (Goose.Proofs.Exit.stepState visit.outcome).construction.events
      | some destination => SourceHistory config sourceFuel [environment.act, visit.ordinal, 0] (.builder environment destination expression) ready
          (buildExpr sourceFuel config environment destination expression ready) ∧
          Goose.Proofs.ConstructionExecution.EventPrefix
            (Goose.Proofs.Exit.stepState (buildExpr sourceFuel config environment destination expression ready)).construction.events
            (Goose.Proofs.Exit.stepState visit.outcome).construction.events) ∨
    ((∃ terminal : DeclarationTerminal, visit.outcome = terminal.step) ∧
      ¬ ∃ destination ready, DeclarationOccurrence sourceFuel config environment localVar expression origin visit.before destination ready) := by
  have supported := (syntaxFuel_existsWithTails visit.fuel config closed).statement environment visit.statement derivation
  have actual := statementVisit_executes replay visit member
  have history := fuelHistory_exists visit.fuel config (.statement environment visit.statement)
    [environment.act, visit.ordinal] visit.before supported
  rw [visitFuel, visitStatement] at history actual
  change SourceHistory config (sourceFuel + 1) [environment.act, visit.ordinal]
    (.statement environment (.letS localVar expression origin)) visit.before
    (execStmt (sourceFuel + 1) config environment (.letS localVar expression origin) visit.before) at history
  have classification := declaration_history_or_earlyTerminal sourceFuel config environment localVar expression origin visit.before
    [environment.act, visit.ordinal] history
  rw [actual] at classification
  rcases classification with ⟨destination, ready, occurrence, unique, child⟩ | early
  · left
    refine ⟨destination, ready, occurrence, unique, ?_⟩
    cases destination <;> exact child
  · exact Or.inr early

#print axioms declaration_visit_classification
end Goose.Proofs.ConstructionGhostDeclarationReplay
