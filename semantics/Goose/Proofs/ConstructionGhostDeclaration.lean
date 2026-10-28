import Goose.Proofs.ConstructionGhostInvocation
import Goose.Proofs.ConstructionGhostStatements

namespace Goose.Proofs.ConstructionGhostDeclaration
open Goose.Construct Goose.Proofs.ConstructionGhostInvocation Goose.Proofs.ConstructionGhostStatements

def fixedDeclarationContinuation (root : Goose.Core.RootInst) (source : ExecutionStep Value) : ExecutionStep Flow :=
  match source with
  | .ok value state => (do
      bindRoot root value
      pure (Flow.normal .unit)) state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem fixedDeclaration_initializer_ghost (fuel : Nat) (config : EvalConfig)
    (environment : RuntimeActivation) (path : List Nat) (localVar : Goose.Core.VarId)
    (expression : Expr) (origin : Goose.Core.OriginId) (before ready : ExecutionState)
    (descriptor : LocalVar) (root : Goose.Core.RootInst)
    (found : environment.vars[localVar]? = some descriptor)
    (fixed : descriptor.ty.nonfixed = false)
    (rootResult : rootOf environment localVar before = .ok root ready) :
    EvaluationTree config environment fuel (path ++ [0]) expression ready
      (evalValue fuel config environment expression ready) ∧
    execStmt (fuel + 1) config environment (.letS localVar expression origin) before =
      fixedDeclarationContinuation root (evalValue fuel config environment expression ready) := by
  refine ⟨evaluationTree_exists fuel config environment _ _ _, ?_⟩
  simp only [execStmt, found, bind, rootResult, fixed, Bool.false_eq_true, ↓reduceIte,
    fixedDeclarationContinuation]
  cases evalValue fuel config environment expression ready <;> rfl

theorem statementVisit_executes {config : EvalConfig} {environment : RuntimeActivation}
    {fuel offset : Nat} {statements : List Stmt} {before : ExecutionState}
    {outcome : ExecutionStep Flow} {visits : List StatementInvocation}
    (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (visit : StatementInvocation) (member : visit ∈ visits) :
    execStmt visit.fuel config environment visit.statement visit.before = visit.outcome := by
  induction replay with
  | timeout | done => simp at member
  | next head tail ih =>
    simp only [List.mem_cons] at member
    rcases member with same | later
    · subst visit; exact head
    · exact ih later
  | breaking head | continuing head | stopped head | escaped head | jumped head =>
    simp only [List.mem_singleton] at member
    subst visit
    exact head

theorem fixedDeclaration_visit_ghost {config : EvalConfig} {environment : RuntimeActivation}
    {fuel offset : Nat} {statements : List Stmt} {before : ExecutionState}
    {outcome : ExecutionStep Flow} {visits : List StatementInvocation}
    (replay : StatementReplay config environment fuel offset statements before outcome visits)
    (visit : StatementInvocation) (member : visit ∈ visits)
    (sourceFuel : Nat) (localVar : Goose.Core.VarId) (expression : Expr) (origin : Goose.Core.OriginId)
    (descriptor : LocalVar) (root : Goose.Core.RootInst) (ready : ExecutionState)
    (visitFuel : visit.fuel = sourceFuel + 1)
    (visitStatement : visit.statement = .letS localVar expression origin)
    (found : environment.vars[localVar]? = some descriptor)
    (fixed : descriptor.ty.nonfixed = false)
    (rootResult : rootOf environment localVar visit.before = .ok root ready) :
    EvaluationTree config environment sourceFuel [environment.act, visit.ordinal, 0] expression ready
      (evalValue sourceFuel config environment expression ready) ∧
    visit.outcome = fixedDeclarationContinuation root (evalValue sourceFuel config environment expression ready) := by
  obtain ⟨tree, execution⟩ := fixedDeclaration_initializer_ghost sourceFuel config environment
    [environment.act, visit.ordinal] localVar expression origin visit.before ready descriptor root found fixed rootResult
  refine ⟨tree, ?_⟩
  have actual := statementVisit_executes replay visit member
  rw [visitFuel, visitStatement, execution] at actual
  exact actual.symm

#print axioms fixedDeclaration_visit_ghost
private def witnessConfig : EvalConfig := ⟨.release, ⟨#[], #[], #[], #[], #[], 0, #[], #[], #[]⟩⟩
private def witnessEnvironment : RuntimeActivation := ⟨0, 4,
  #[⟨"x", .int .i64, .immutable, 0, 0⟩], [(0, 1)], []⟩
private def witnessStatement : Stmt := .letS 0
  (.blockE (.mk 1 [.print [.text "once"] 0] (some (.lit .i64 7))) 0) 0
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

theorem declarationWitness_sideEffect :
    ∃ state, execStmt 40 witnessConfig witnessEnvironment witnessStatement .initial =
      .ok (.normal .unit) state ∧
      state.construction.stdout.data.toList = [111, 110, 99, 101, 10] ∧
      state.objects = [(Goose.Core.RootInst.local 4 1 0, .int .i64 7)] := by
  refine ⟨stepState (execStmt 40 witnessConfig witnessEnvironment witnessStatement .initial), ?_, ?_, ?_⟩ <;>
    unfold witnessConfig witnessEnvironment witnessStatement stepState <;> cbv

#print axioms declarationWitness_sideEffect
#print axioms fixedDeclaration_initializer_ghost
end Goose.Proofs.ConstructionGhostDeclaration
