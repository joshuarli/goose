import Goose.Proofs.ConstructionAcceptedNestedCursor
import Goose.Proofs.ConstructionAcceptedGlobalAssignRuntime

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

def NestedValueOutcome (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop) (ty : Ty)
    (outcome : ExecutionStep Value) : Prop :=
  let after := Goose.Proofs.Exit.stepState outcome
  AcceptedWorld config frame.initialized after ambient types live [] [] ∧ AcceptedFrame config accepted frame after types ∧
    (match outcome with | .ok value _ => ValueRepresentation ty value ∧ PointerTypedValue types ty value | .stop .. => True | _ => False)

def NestedBlockOutcome (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop) (ty : Ty)
    (outcome : ExecutionStep Flow) : Prop :=
  let after := Goose.Proofs.Exit.stepState outcome
  AcceptedWorld config frame.initialized after ambient types live [] [] ∧ AcceptedFrame config accepted frame after types ∧
    (match outcome with | .ok (.normal value) _ => ValueRepresentation ty value ∧ PointerTypedValue types ty value | .stop .. => True | _ => False)

theorem nestedValueConditional_compose (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (ty : Ty) (condition : Expr) (yes no : Block) (origin : Nat) (before : ExecutionState)
    (conditionSafe : NestedValueOutcome config accepted frame ambient types live .bool
      (evalValue fuel config frame.interpretation.environment condition before))
    (yesSafe : ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
      AcceptedFrame config accepted frame state types →
      NestedBlockOutcome config accepted frame ambient types live ty (execBlock fuel config frame.interpretation.environment [] [] yes state))
    (noSafe : ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
      AcceptedFrame config accepted frame state types →
      NestedBlockOutcome config accepted frame ambient types live ty (execBlock fuel config frame.interpretation.environment [] [] no state)) :
    NestedValueOutcome config accepted frame ambient types live ty
      (evalValue (fuel + 1) config frame.interpretation.environment (.ifE condition yes no origin) before) := by
  cases conditionRun : evalValue fuel config frame.interpretation.environment condition before with
  | stop reason after =>
    simp only [NestedValueOutcome, conditionRun, Goose.Proofs.Exit.stepState] at conditionSafe
    have stopped := evalValue_conditional_conditionStop fuel config frame.interpretation.environment condition yes no origin before after reason conditionRun
    simpa only [NestedValueOutcome, stopped, Goose.Proofs.Exit.stepState] using conditionSafe
  | escape address carriers after | jump target kind after =>
    simp only [NestedValueOutcome, conditionRun] at conditionSafe
    exact conditionSafe.2.2.elim
  | ok value middle =>
    simp only [NestedValueOutcome, conditionRun, Goose.Proofs.Exit.stepState] at conditionSafe
    have boolean : ∃ choice, value = .bool choice := by
      cases value <;> cases conditionSafe.2.2.1 <;> simp_all [Ty.nonfixed]
    obtain ⟨choice, rfl⟩ := boolean
    cases choice with
    | false =>
      have branchSafe := noSafe middle conditionSafe.1 conditionSafe.2.1
      cases branchRun : execBlock fuel config frame.interpretation.environment [] [] no middle with
      | stop reason after =>
        simp only [NestedBlockOutcome, branchRun, Goose.Proofs.Exit.stepState] at branchSafe
        have stopped := evalValue_conditional_branchStop fuel config frame.interpretation.environment condition yes no origin
          before middle after false reason conditionRun (by simpa using branchRun)
        simpa only [NestedValueOutcome, stopped, Goose.Proofs.Exit.stepState] using branchSafe
      | escape address carriers after | jump target kind after =>
        simp only [NestedBlockOutcome, branchRun] at branchSafe
        exact branchSafe.2.2.elim
      | ok flow after =>
        cases flow with
        | normal result =>
          simp only [NestedBlockOutcome, branchRun, Goose.Proofs.Exit.stepState] at branchSafe
          have done := evalValue_conditional_branchNormal fuel config frame.interpretation.environment condition yes no origin
            before middle after false result conditionRun (by simpa using branchRun)
          simpa only [NestedValueOutcome, done, Goose.Proofs.Exit.stepState] using branchSafe
        | breaking value | continuing =>
          simp only [NestedBlockOutcome, branchRun] at branchSafe
          exact branchSafe.2.2.elim
    | true =>
      have branchSafe := yesSafe middle conditionSafe.1 conditionSafe.2.1
      cases branchRun : execBlock fuel config frame.interpretation.environment [] [] yes middle with
      | stop reason after =>
        simp only [NestedBlockOutcome, branchRun, Goose.Proofs.Exit.stepState] at branchSafe
        have stopped := evalValue_conditional_branchStop fuel config frame.interpretation.environment condition yes no origin
          before middle after true reason conditionRun (by simpa using branchRun)
        simpa only [NestedValueOutcome, stopped, Goose.Proofs.Exit.stepState] using branchSafe
      | escape address carriers after | jump target kind after =>
        simp only [NestedBlockOutcome, branchRun] at branchSafe
        exact branchSafe.2.2.elim
      | ok flow after =>
        cases flow with
        | normal result =>
          simp only [NestedBlockOutcome, branchRun, Goose.Proofs.Exit.stepState] at branchSafe
          have done := evalValue_conditional_branchNormal fuel config frame.interpretation.environment condition yes no origin
            before middle after true result conditionRun (by simpa using branchRun)
          simpa only [NestedValueOutcome, done, Goose.Proofs.Exit.stepState] using branchSafe
        | breaking value | continuing =>
          simp only [NestedBlockOutcome, branchRun] at branchSafe
          exact branchSafe.2.2.elim

theorem nestedValue_scalar (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (ty : Ty) (expression : Expr) (form : AcceptedBinaryExpression expression) (before : ExecutionState)
    (world : AcceptedWorld config frame.initialized before ambient types live [] [])
    (source : AcceptedFrame config accepted frame before types) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    NestedValueOutcome config accepted frame ambient types live ty (evalValue fuel config frame.interpretation.environment expression before) := by
  have result := evalValue_checked_binary_recursive form fuel config accepted frame before ambient types live [] [] world source
    ty roots typingAfter rootsAfter checked
  cases execution : evalValue fuel config frame.interpretation.environment expression before with
  | stop reason after =>
    simp only [execution, Goose.Proofs.Exit.stepState] at result
    simp only [NestedValueOutcome, Goose.Proofs.Exit.stepState]
    exact ⟨result.2.2.1, result.2.2.2, trivial⟩
  | escape address carriers after =>
    exact ((evalValue_scalar_controlFree form fuel config frame.interpretation.environment).1 before address carriers after execution).elim
  | jump target kind after =>
    exact ((evalValue_scalar_controlFree form fuel config frame.interpretation.environment).2 before target kind after execution).elim
  | ok value after =>
    have valid := result.2.1 value after execution
    simp only [execution, Goose.Proofs.Exit.stepState] at result
    simp only [NestedValueOutcome, Goose.Proofs.Exit.stepState]
    exact ⟨result.2.2.1, result.2.2.2, valid.represented, valid.pointers⟩

def NestedStatementsOutcome (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (outcome : ExecutionStep Flow) : Prop :=
  let after := Goose.Proofs.Exit.stepState outcome
  AcceptedWorld config frame.initialized after ambient types live [] [] ∧ AcceptedFrame config accepted frame after types ∧
    (match outcome with | .ok flow _ => flow = .normal .unit | .stop .. => True | _ => False)

theorem nestedStatements_cons_compose (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (head : Stmt) (tail : List Stmt) (before : ExecutionState)
    (headSafe : NestedStatementsOutcome config accepted frame ambient types live
      (execStmt fuel config frame.interpretation.environment head before))
    (tailSafe : ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
      AcceptedFrame config accepted frame state types →
      NestedStatementsOutcome config accepted frame ambient types live (execStmts fuel config frame.interpretation.environment tail state)) :
    NestedStatementsOutcome config accepted frame ambient types live
      (execStmts (fuel + 1) config frame.interpretation.environment (head :: tail) before) := by
  cases headRun : execStmt fuel config frame.interpretation.environment head before with
  | stop reason after =>
    simp only [NestedStatementsOutcome, headRun, Goose.Proofs.Exit.stepState] at headSafe
    simpa only [execStmts, bind, headRun, NestedStatementsOutcome, Goose.Proofs.Exit.stepState] using headSafe
  | escape address carriers after | jump target kind after =>
    simp only [NestedStatementsOutcome, headRun] at headSafe
    exact headSafe.2.2.elim
  | ok flow middle =>
    simp only [NestedStatementsOutcome, headRun, Goose.Proofs.Exit.stepState] at headSafe
    obtain ⟨middleWorld, middleFrame, sameFlow⟩ := headSafe
    subst flow
    have remaining := tailSafe middle middleWorld middleFrame
    simpa only [execStmts, bind, headRun] using remaining

theorem nestedBlock_compose (fuel checkFuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (ty : Ty) (scope : Nat) (statements : List Stmt) (tail : Expr) (before : ExecutionState)
    (source : AcceptedFrame config accepted frame before types) (empty : frame.interpretation.environment.vars = #[])
    (statementsSafe : let child := emptyChildScopeFrame frame scope before.nextScope checkFuel
      let entered := { before with nextScope := before.nextScope + 1 }
      NestedStatementsOutcome config accepted child ambient types live
        (execStmts fuel config child.interpretation.environment statements entered))
    (tailSafe : let child := emptyChildScopeFrame frame scope before.nextScope checkFuel
      ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
      AcceptedFrame config accepted child state types →
      NestedValueOutcome config accepted child ambient types live ty (evalValue fuel config child.interpretation.environment tail state)) :
    NestedBlockOutcome config accepted frame ambient types live ty
      (execBlock (fuel + 1) config frame.interpretation.environment [] [] ⟨scope, statements, some tail⟩ before) := by
  let environment := frame.interpretation.environment
  let child := emptyChildScopeFrame frame scope before.nextScope checkFuel
  let entered := { before with nextScope := before.nextScope + 1 }
  change NestedBlockOutcome config accepted frame ambient types live ty
    (execBlock (fuel + 1) config environment [] [] ⟨scope, statements, some tail⟩ before)
  change NestedStatementsOutcome config accepted child ambient types live
    (execStmts fuel config child.interpretation.environment statements entered) at statementsSafe
  change ∀ state, AcceptedWorld config frame.initialized state ambient types live [] [] →
    AcceptedFrame config accepted child state types →
    NestedValueOutcome config accepted child ambient types live ty (evalValue fuel config child.interpretation.environment tail state) at tailSafe
  cases statementsRun : execStmts fuel config child.interpretation.environment statements entered with
  | escape address carriers after | jump target kind after =>
    simp only [NestedStatementsOutcome, statementsRun] at statementsSafe
    exact statementsSafe.2.2.elim
  | stop reason after =>
    simp only [NestedStatementsOutcome, statementsRun, Goose.Proofs.Exit.stepState] at statementsSafe
    have parentFrame := source.leaveEmptyChild empty scope before.nextScope checkFuel statementsSafe.2.1
    have stopped : execBlock (fuel + 1) config environment [] [] ⟨scope, statements, some tail⟩ before = .stop reason after := by
      change execStmts fuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements entered = .stop reason after at statementsRun
      simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, statementsRun, entered]
    simp only [NestedBlockOutcome, stopped, Goose.Proofs.Exit.stepState]
    exact ⟨statementsSafe.1, parentFrame, trivial⟩
  | ok flow middle =>
    simp only [NestedStatementsOutcome, statementsRun, Goose.Proofs.Exit.stepState] at statementsSafe
    obtain ⟨middleWorld, middleFrame, sameFlow⟩ := statementsSafe
    subst flow
    have tailResult := tailSafe middle middleWorld middleFrame
    cases tailRun : evalValue fuel config child.interpretation.environment tail middle with
    | escape address carriers after | jump target kind after =>
      simp only [NestedValueOutcome, tailRun] at tailResult
      exact tailResult.2.2.elim
    | stop reason after =>
      simp only [NestedValueOutcome, tailRun, Goose.Proofs.Exit.stepState] at tailResult
      have parentFrame := source.leaveEmptyChild empty scope before.nextScope checkFuel tailResult.2.1
      have stopped : execBlock (fuel + 1) config environment [] [] ⟨scope, statements, some tail⟩ before = .stop reason after := by
        change execStmts fuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements entered = .ok (.normal .unit) middle at statementsRun
        change evalValue fuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } tail middle = .stop reason after at tailRun
        simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, statementsRun, tailRun, entered]
      simp only [NestedBlockOutcome, stopped, Goose.Proofs.Exit.stepState]
      exact ⟨tailResult.1, parentFrame, trivial⟩
    | ok value after =>
      simp only [NestedValueOutcome, tailRun, Goose.Proofs.Exit.stepState] at tailResult
      have parentFrame := source.leaveEmptyChild empty scope before.nextScope checkFuel tailResult.2.1
      let released := releaseScopeState environment scope before.nextScope after
      have releasedWorld := tailResult.1.releaseEmptyScope config frame.initialized after ambient types live [] [] environment empty scope before.nextScope
      have releasedFrame := parentFrame.releaseEmptyScope empty environment empty scope before.nextScope
      have done : execBlock (fuel + 1) config environment [] [] ⟨scope, statements, some tail⟩ before = .ok (.normal value) released := by
        change execStmts fuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements entered = .ok (.normal .unit) middle at statementsRun
        change evalValue fuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } tail middle = .ok value after at tailRun
        simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, statementsRun, tailRun,
          releaseScope, released, entered]
      simp only [NestedBlockOutcome, done, Goose.Proofs.Exit.stepState]
      exact ⟨releasedWorld, releasedFrame, tailResult.2.2⟩

theorem nestedExpressionStatement_compose (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (ty : Ty) (expression : Expr) (origin : Nat) (before : ExecutionState)
    (safe : NestedValueOutcome config accepted frame ambient types live ty
      (evalValue fuel config frame.interpretation.environment expression before)) :
    NestedStatementsOutcome config accepted frame ambient types live
      (execStmt (fuel + 1) config frame.interpretation.environment (.expr expression origin) before) := by
  cases execution : evalValue fuel config frame.interpretation.environment expression before with
  | stop reason after =>
    simp only [NestedValueOutcome, execution, Goose.Proofs.Exit.stepState] at safe
    simpa [execStmt, execution, bind, NestedStatementsOutcome, Goose.Proofs.Exit.stepState] using safe
  | escape address carriers after | jump target kind after =>
    simp only [NestedValueOutcome, execution] at safe
    exact safe.2.2.elim
  | ok value after =>
    simp only [NestedValueOutcome, execution, Goose.Proofs.Exit.stepState] at safe
    simp only [execStmt, execution, bind, pure, NestedStatementsOutcome, Goose.Proofs.Exit.stepState]
    exact ⟨safe.1, safe.2.1, trivial⟩

theorem nestedGlobalAssign_compose (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (id : Nat) (descriptor : Global) (expression : Expr) (origin : Nat) (before : ExecutionState)
    (available : id < frame.initialized) (declared : config.module.globals[id]? = some descriptor)
    (scalarTy : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (safe : NestedValueOutcome config accepted frame ambient types live descriptor.ty
      (evalValue (fuel + 1) config frame.interpretation.environment expression before)) :
    NestedStatementsOutcome config accepted frame ambient types live
      (execStmt (fuel + 2) config frame.interpretation.environment (.assign (.global id) expression origin) before) := by
  cases execution : evalValue (fuel + 1) config frame.interpretation.environment expression before with
  | stop reason after =>
    simp only [NestedValueOutcome, execution, Goose.Proofs.Exit.stepState] at safe
    simpa [execStmt, evalPlace, execution, bind, pure, NestedStatementsOutcome, Goose.Proofs.Exit.stepState] using safe
  | escape address carriers after | jump target kind after =>
    simp only [NestedValueOutcome, execution] at safe
    exact safe.2.2.elim
  | ok value middle =>
    simp only [NestedValueOutcome, execution, Goose.Proofs.Exit.stepState] at safe
    have scalarValue : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean := by
      rcases scalarTy with ⟨intTy, same⟩ | same <;> rw [same] at safe <;>
        cases value <;> cases safe.2.2.1 <;> simp_all [Ty.nonfixed]
    have retained := safe.1.globalLive id available
    have rootType := safe.1.globalTypes id descriptor declared
    obtain ⟨other, old, otherDeclared, found, represented⟩ := safe.1.globals.2 id available
    have same : other = descriptor := Option.some.inj (otherDeclared.symm.trans declared)
    subst other
    have writeSafe := writeLoc_scalar_prefix_complete (fuel + 1) config accepted frame middle ambient types live [] []
      (.global id) descriptor.ty old value safe.1 safe.2.1 (by intro later future within equal; cases equal; omega)
      rootType retained found scalarValue safe.2.2.1 safe.2.2.2
    cases write : writeLoc (fuel + 1) config.layout ⟨.global id, []⟩ value middle with
    | stop reason after =>
      simp only [write, Goose.Proofs.Exit.stepState] at writeSafe
      simp only [execStmt, evalPlace, pure, bind, execution, write, NestedStatementsOutcome, Goose.Proofs.Exit.stepState]
      exact ⟨writeSafe.1, writeSafe.2.1, trivial⟩
    | escape address carriers after | jump target kind after =>
      simp only [write] at writeSafe
      exact writeSafe.2.2.elim
    | ok result after =>
      cases result
      simp only [write, Goose.Proofs.Exit.stepState] at writeSafe
      simp only [execStmt, evalPlace, execution, bind, write, pure, NestedStatementsOutcome, Goose.Proofs.Exit.stepState]
      exact ⟨writeSafe.1, writeSafe.2.1, trivial⟩

theorem NestedValueOutcome.retarget (config : EvalConfig) (accepted : AcceptedModule config)
    (frame other : ConstructionSourceFrame) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (ty : Ty) (before : ExecutionState) (outcome : ExecutionStep Value)
    (source : AcceptedFrame config accepted frame before types) (empty : frame.interpretation.environment.vars = #[])
    (sameInterpretation : other.interpretation = frame.interpretation) (sameInitialized : other.initialized = frame.initialized)
    (safe : NestedValueOutcome config accepted other ambient types live ty outcome) :
    NestedValueOutcome config accepted frame ambient types live ty outcome := by
  obtain ⟨world, otherSource, flow⟩ := safe
  refine ⟨?_, source.retargetEmptyVariables empty other sameInterpretation sameInitialized otherSource, flow⟩
  simpa [sameInitialized] using world

theorem NestedBlockOutcome.retarget (config : EvalConfig) (accepted : AcceptedModule config)
    (frame other : ConstructionSourceFrame) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (ty : Ty) (before : ExecutionState) (outcome : ExecutionStep Flow)
    (source : AcceptedFrame config accepted frame before types) (empty : frame.interpretation.environment.vars = #[])
    (sameInterpretation : other.interpretation = frame.interpretation) (sameInitialized : other.initialized = frame.initialized)
    (safe : NestedBlockOutcome config accepted other ambient types live ty outcome) :
    NestedBlockOutcome config accepted frame ambient types live ty outcome := by
  obtain ⟨world, otherSource, flow⟩ := safe
  refine ⟨?_, source.retargetEmptyVariables empty other sameInterpretation sameInitialized otherSource, flow⟩
  simpa [sameInitialized] using world

theorem NestedStatementsOutcome.retarget (config : EvalConfig) (accepted : AcceptedModule config)
    (frame other : ConstructionSourceFrame) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (before : ExecutionState) (outcome : ExecutionStep Flow)
    (source : AcceptedFrame config accepted frame before types) (empty : frame.interpretation.environment.vars = #[])
    (sameInterpretation : other.interpretation = frame.interpretation) (sameInitialized : other.initialized = frame.initialized)
    (safe : NestedStatementsOutcome config accepted other ambient types live outcome) :
    NestedStatementsOutcome config accepted frame ambient types live outcome := by
  obtain ⟨world, otherSource, flow⟩ := safe
  refine ⟨?_, source.retargetEmptyVariables empty other sameInterpretation sameInitialized otherSource, flow⟩
  simpa [sameInitialized] using world

#print axioms NestedValueOutcome.retarget
#print axioms NestedBlockOutcome.retarget
#print axioms NestedStatementsOutcome.retarget
#print axioms nestedExpressionStatement_compose
#print axioms nestedGlobalAssign_compose
#print axioms nestedBlock_compose
#print axioms nestedStatements_cons_compose
#print axioms nestedValue_scalar
#print axioms nestedValueConditional_compose
end Goose.Proofs.ConstructionAcceptedExecution
