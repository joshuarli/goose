import Goose.Proofs.ConstructionAcceptedRecursiveGlobalModule
import Goose.Proofs.ConstructionAcceptedScopeWorld

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

inductive ScalarLiteral : Expr → Value → Prop
  | integer (ty : Goose.Core.IntTy) (number : Int) : ScalarLiteral (.lit ty number) (.int ty number)
  | boolean (value : Bool) : ScalarLiteral (.bool value) (.bool value)

theorem execBlock_scalarLiteral_transition (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (scope : Nat) (expression : Expr) (value : Value) (literal : ScalarLiteral expression value) (before : ExecutionState) :
    execBlock (fuel + 2) config environment [] [] ⟨scope, [], some expression⟩ before =
      .ok (.normal value) (releaseScopeState environment scope before.nextScope { before with nextScope := before.nextScope + 1 }) := by
  cases literal <;>
    simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, execStmts,
      evalValue, releaseScope, releaseScopeState]

theorem execBlock_scalarLiteral_world (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (scope : Nat) (expression : Expr) (value : Value) (literal : ScalarLiteral expression value)
    (initialized : Nat) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending) :
    ∃ nextLive,
      let outcome := execBlock fuel config environment [] [] ⟨scope, [], some expression⟩ before
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) ambient types nextLive regions pending ∧
      (match outcome with | .ok flow _ => flow = .normal value | .stop .. => True | .escape .. | .jump .. => False) := by
  cases fuel with
  | zero =>
    simp only [execBlock, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨live, world, trivial⟩
  | succ fuel =>
    let activated := { before with nextScope := before.nextScope + 1 }
    have activeWorld := (freshScope_acceptedWorld config initialized before ambient types live world).2
    cases fuel with
    | zero =>
      have stopped : execBlock 1 config environment [] [] ⟨scope, [], some expression⟩ before = .stop .timeout activated := by
        simp [execBlock, freshScope, EvalM.get, EvalM.set, bind, pure, withScope, bindAll, execStmts, timeout, EvalM.stop, activated]
      simp only [stopped, Goose.Proofs.Exit.stepState]
      exact ⟨live, activeWorld, trivial⟩
    | succ fuel =>
      have done := execBlock_scalarLiteral_transition fuel config environment scope expression value literal before
      have released := activeWorld.releaseScope config initialized activated ambient types live regions pending environment scope before.nextScope
      simp only [done, Goose.Proofs.Exit.stepState]
      exact ⟨_, released, trivial⟩

theorem evalValue_scalarLiteralIf_transition (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (condition : Bool) (yesScope noScope : Nat) (yes no : Expr) (yesValue noValue : Value)
    (yesLiteral : ScalarLiteral yes yesValue) (noLiteral : ScalarLiteral no noValue) (origin : Goose.Core.OriginId)
    (before : ExecutionState) :
    evalValue (fuel + 3) config environment
      (.ifE (.bool condition) ⟨yesScope, [], some yes⟩ ⟨noScope, [], some no⟩ origin) before =
      .ok (if condition then yesValue else noValue)
        (releaseScopeState environment (if condition then yesScope else noScope) before.nextScope
          { before with nextScope := before.nextScope + 1 }) := by
  cases condition <;>
    simp only [evalValue, expectBool, bind, pure, Bool.false_eq_true, ↓reduceIte]
  · rw [execBlock_scalarLiteral_transition fuel config environment noScope no noValue noLiteral before]
  · rw [execBlock_scalarLiteral_transition fuel config environment yesScope yes yesValue yesLiteral before]

#print axioms evalValue_scalarLiteralIf_transition
theorem evalValue_scalarLiteralIf_world (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (condition : Bool) (yesScope noScope : Nat) (yes no : Expr) (yesValue noValue : Value)
    (yesLiteral : ScalarLiteral yes yesValue) (noLiteral : ScalarLiteral no noValue) (origin : Goose.Core.OriginId)
    (initialized : Nat) (before : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized before ambient types live regions pending) :
    ∃ nextLive,
      let outcome := evalValue fuel config environment
        (.ifE (.bool condition) ⟨yesScope, [], some yes⟩ ⟨noScope, [], some no⟩ origin) before
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState outcome) ambient types nextLive regions pending ∧
      (match outcome with
       | .ok result _ => result = (if condition then yesValue else noValue)
       | .stop .. => True
       | .escape .. | .jump .. => False) := by
  cases fuel with
  | zero =>
    simp only [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState]
    exact ⟨live, world, trivial⟩
  | succ fuel =>
    cases fuel with
    | zero =>
      simp only [evalValue, timeout, EvalM.stop, bind, Goose.Proofs.Exit.stepState]
      exact ⟨live, world, trivial⟩
    | succ fuel =>
      cases condition <;>
        simp only [evalValue, expectBool, bind, pure, Bool.false_eq_true, ↓reduceIte]
      · obtain ⟨nextLive, nextWorld, flow⟩ := execBlock_scalarLiteral_world (fuel + 1) config environment noScope no noValue
          noLiteral initialized before ambient types live regions pending world
        cases execution : execBlock (fuel + 1) config environment [] [] ⟨noScope, [], some no⟩ before with
        | stop reason after =>
          simp only [execution, Goose.Proofs.Exit.stepState] at nextWorld flow ⊢
          exact ⟨nextLive, nextWorld, by simp⟩
        | escape address carriers after | jump target kind after => simp only [execution] at flow
        | ok result after =>
          simp only [execution] at flow
          subst result
          simp only [execution, Goose.Proofs.Exit.stepState] at nextWorld
          exact ⟨nextLive, nextWorld, by simp⟩
      · obtain ⟨nextLive, nextWorld, flow⟩ := execBlock_scalarLiteral_world (fuel + 1) config environment yesScope yes yesValue
          yesLiteral initialized before ambient types live regions pending world
        cases execution : execBlock (fuel + 1) config environment [] [] ⟨yesScope, [], some yes⟩ before with
        | stop reason after =>
          simp only [execution, Goose.Proofs.Exit.stepState] at nextWorld flow ⊢
          exact ⟨nextLive, nextWorld, by simp⟩
        | escape address carriers after | jump target kind after => simp only [execution] at flow
        | ok result after =>
          simp only [execution] at flow
          subst result
          simp only [execution, Goose.Proofs.Exit.stepState] at nextWorld
          exact ⟨nextLive, nextWorld, by simp⟩

theorem evalValue_scalarLiteralIf_futureGlobals (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (condition : Bool) (yesScope noScope : Nat) (yes no : Expr) (yesValue noValue : Value)
    (yesLiteral : ScalarLiteral yes yesValue) (noLiteral : ScalarLiteral no noValue) (origin : Goose.Core.OriginId)
    (initialized : Nat) (before : ExecutionState) (empty : environment.vars = #[])
    (clear : FutureGlobalsClear config initialized before) :
    FutureGlobalsClear config initialized (Goose.Proofs.Exit.stepState (evalValue fuel config environment
      (.ifE (.bool condition) ⟨yesScope, [], some yes⟩ ⟨noScope, [], some no⟩ origin) before)) := by
  cases fuel with
  | zero => simpa [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState] using clear
  | succ fuel =>
    cases fuel with
    | zero => simpa [evalValue, bind, timeout, EvalM.stop, Goose.Proofs.Exit.stepState] using clear
    | succ fuel =>
      cases fuel with
      | zero =>
        have nextClear : FutureGlobalsClear config initialized { before with nextScope := before.nextScope + 1 } := clear
        cases condition <;>
          simpa [evalValue, expectBool, bind, pure, execBlock, freshScope, EvalM.get, EvalM.set, withScope,
            bindAll, execStmts, timeout, EvalM.stop, Goose.Proofs.Exit.stepState] using nextClear
      | succ fuel =>
        rw [evalValue_scalarLiteralIf_transition fuel config environment condition yesScope noScope yes no yesValue noValue
          yesLiteral noLiteral origin before]
        simp only [Goose.Proofs.Exit.stepState]
        intro id future inside
        simpa [releaseScopeState, empty] using clear id future inside

#print axioms evalValue_scalarLiteralIf_futureGlobals
#print axioms evalValue_scalarLiteralIf_world
#print axioms execBlock_scalarLiteral_transition
#print axioms execBlock_scalarLiteral_world
end Goose.Proofs.ConstructionAcceptedExecution
