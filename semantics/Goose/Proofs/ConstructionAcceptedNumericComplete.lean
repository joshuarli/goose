import Goose.Proofs.ConstructionAcceptedNotComplete

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem typeExpr_un_operand (fuel : Nat) (environment : TypingEnv) (operation : Goose.Core.UnOp)
    (expression : Expr) (origin : Goose.Core.OriginId) (before after : Nat) (ty : Ty)
    (checked : typeExpr (fuel + 1) environment (.un operation expression origin) before = .ok ([ty], after)) :
    ∃ integer, ty = .int integer ∧ typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] }
      expression before = .ok ([.int integer], after) := by
  simp only [typeExpr, bind, StateT.bind] at checked
  change (Except.bind (typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] } expression before) _) =
    .ok ([ty], after) at checked
  generalize operand : typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] } expression before = result at checked
  cases result with
  | error failure => simp only [Except.bind] at checked; cases checked
  | ok result =>
    obtain ⟨types, next⟩ := result
    cases types with
    | nil => change Except.error _ = Except.ok _ at checked; cases checked
    | cons head tail =>
      cases tail with
      | cons second rest => change Except.error _ = Except.ok _ at checked; cases checked
      | nil =>
        cases head <;> try (change Except.error _ = Except.ok _ at checked; cases checked)
        case int integer =>
          cases operation with
          | bitnot =>
            change Except.ok ([Ty.int integer], next) = Except.ok ([ty], after) at checked
            cases checked
            exact ⟨integer, rfl, rfl⟩
          | neg =>
            cases integer <;> first
              | change Except.error _ = Except.ok _ at checked; cases checked
              | change Except.ok _ = Except.ok _ at checked; cases checked; exact ⟨_, rfl, rfl⟩

theorem checkedValue_un_operand (frame : ConstructionSourceFrame) (fuel : Nat)
    (operation : Goose.Core.UnOp) (expression : Expr) (origin : Goose.Core.OriginId) (ty : Ty)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (fuelAt : frame.typingFuel = fuel + 1)
    (checked : CheckedValue frame (.un operation expression origin) ty roots typingAfter rootsAfter) :
    ∃ integer operandRoots operandAfter, ty = .int integer ∧ roots = [] ∧
      CheckedValue (ordinaryOperandFrame frame fuel) expression (.int integer) operandRoots typingAfter operandAfter := by
  have typing := checked.typing
  rw [fuelAt] at typing
  obtain ⟨integer, sameTy, operandTyping⟩ := typeExpr_un_operand fuel frame.typing operation expression origin
    frame.typingCounter typingAfter ty typing
  have provenance := checked.provenance
  change (Except.bind (rpExpr frame.source expression frame.rootCursor) _) = .ok (roots, rootsAfter) at provenance
  cases operand : rpExpr frame.source expression frame.rootCursor with
  | error failure => simp only [operand, Except.bind] at provenance; cases provenance
  | ok result =>
    obtain ⟨operandRoots, operandAfter⟩ := result
    simp only [operand, Except.bind] at provenance
    cases operation with
    | bitnot =>
      change Except.ok ([], operandAfter) = Except.ok (roots, rootsAfter) at provenance
      cases provenance
      exact ⟨integer, operandRoots, _, sameTy, rfl, operandTyping, operand, checked.available⟩
    | neg =>
      change Except.ok ([], { operandAfter with eff := { operandAfter.eff with aborts := true } }) =
        Except.ok (roots, rootsAfter) at provenance
      cases provenance
      refine ⟨integer, operandRoots, operandAfter, sameTy, rfl, operandTyping, operand, ?_⟩
      simpa [GlobalEffectsAvailable, ordinaryOperandFrame] using checked.available

theorem typeExpr_conv_operand (fuel : Nat) (environment : TypingEnv) (kind : Goose.Core.ConvKind)
    (target : Ty) (expression : Expr) (origin : Goose.Core.OriginId) (before after : Nat) (ty : Ty)
    (checked : typeExpr (fuel + 1) environment (.conv kind target expression origin) before = .ok ([ty], after)) :
    ∃ source targetInt, target = .int targetInt ∧ ty = .int targetInt ∧ typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] }
      expression before = .ok ([.int source], after) := by
  simp only [typeExpr, bind, StateT.bind] at checked
  change (Except.bind (typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] } expression before) _) =
    .ok ([ty], after) at checked
  generalize operand : typeExpr fuel
      { environment with use := .ordinary, request := .value, resultRequests := [] } expression before = result at checked
  cases result with
  | error failure => simp only [Except.bind] at checked; cases checked
  | ok result =>
    obtain ⟨types, next⟩ := result
    cases types with
    | nil => change Except.error _ = Except.ok _ at checked; cases checked
    | cons head tail =>
      cases tail with
      | cons second rest => change Except.error _ = Except.ok _ at checked; cases checked
      | nil =>
        cases target <;> try (change Except.error _ = Except.ok _ at checked; cases checked)
        case int targetInt =>
          cases head <;> try (change Except.error _ = Except.ok _ at checked; cases checked)
          case int source =>
            cases kind with
            | as | asUnchecked =>
              change Except.ok ([Ty.int targetInt], next) = Except.ok ([ty], after) at checked
              cases checked
              exact ⟨source, targetInt, rfl, rfl, rfl⟩
            | widen =>
              cases source <;> cases targetInt <;> first
                | change Except.error _ = Except.ok _ at checked; cases checked
                | change Except.ok _ = Except.ok _ at checked; cases checked; exact ⟨_, _, rfl, rfl, rfl⟩

theorem checkedValue_conv_operand (frame : ConstructionSourceFrame) (fuel : Nat)
    (kind : Goose.Core.ConvKind) (target : Ty) (expression : Expr) (origin : Goose.Core.OriginId) (ty : Ty)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (fuelAt : frame.typingFuel = fuel + 1)
    (checked : CheckedValue frame (.conv kind target expression origin) ty roots typingAfter rootsAfter) :
    ∃ source targetInt operandRoots operandAfter, target = .int targetInt ∧ ty = .int targetInt ∧ roots = [] ∧
      CheckedValue (ordinaryOperandFrame frame fuel) expression (.int source) operandRoots typingAfter operandAfter := by
  have typing := checked.typing
  rw [fuelAt] at typing
  obtain ⟨source, targetInt, sameTarget, sameTy, operandTyping⟩ := typeExpr_conv_operand fuel frame.typing kind target expression origin
    frame.typingCounter typingAfter ty typing
  have provenance := checked.provenance
  change (Except.bind (rpExpr frame.source expression frame.rootCursor) _) = .ok (roots, rootsAfter) at provenance
  cases operand : rpExpr frame.source expression frame.rootCursor with
  | error failure => simp only [operand, Except.bind] at provenance; cases provenance
  | ok result =>
    obtain ⟨operandRoots, operandAfter⟩ := result
    simp only [operand, Except.bind] at provenance
    cases kind with
    | widen | asUnchecked =>
      change Except.ok ([], operandAfter) = Except.ok (roots, rootsAfter) at provenance
      cases provenance
      exact ⟨source, targetInt, operandRoots, _, sameTarget, sameTy, rfl, operandTyping, operand, checked.available⟩
    | as =>
      change Except.ok ([], { operandAfter with eff := { operandAfter.eff with aborts := true } }) =
        Except.ok (roots, rootsAfter) at provenance
      cases provenance
      refine ⟨source, targetInt, operandRoots, operandAfter, sameTarget, sameTy, rfl, operandTyping, operand, ?_⟩
      simpa [GlobalEffectsAvailable, ordinaryOperandFrame] using checked.available

#print axioms typeExpr_conv_operand
#print axioms checkedValue_conv_operand
inductive AcceptedNumericExpression : Expr → Prop
  | scalar {expression : Expr} : AcceptedNotExpression expression → AcceptedNumericExpression expression
  | unary {expression : Expr} (operation : Goose.Core.UnOp) (origin : Goose.Core.OriginId) :
      AcceptedNumericExpression expression → AcceptedNumericExpression (.un operation expression origin)
  | conversion {expression : Expr} (kind : Goose.Core.ConvKind) (target : Ty) (origin : Goose.Core.OriginId) :
      AcceptedNumericExpression expression → AcceptedNumericExpression (.conv kind target expression origin)

theorem evalValue_checked_numeric_complete {expression : Expr} (form : AcceptedNumericExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) (checked : CheckedValue frame expression ty roots typingAfter rootsAfter) :
    let outcome := evalValue fuel config frame.interpretation.environment expression state
    Goose.Proofs.Exit.stepState outcome = state ∧
      (∀ value after, outcome = .ok value after → AcceptedValue config.layout types frame.interpretation after ty roots value) ∧
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState outcome) ambient types live regions pending ∧
      AcceptedFrame config accepted frame (Goose.Proofs.Exit.stepState outcome) types := by
  induction form generalizing fuel frame ty roots typingAfter rootsAfter with
  | scalar form =>
    exact evalValue_checked_not_complete form fuel config accepted frame state ambient types live regions pending world source
      ty roots typingAfter rootsAfter checked
  | @unary expression operation origin form ih =>
    cases typingFuel : frame.typingFuel with
    | zero =>
      have typing := checked.typing
      rw [typingFuel] at typing
      change Except.error _ = Except.ok _ at typing
      cases typing
    | succ n =>
      obtain ⟨integer, operandRoots, operandAfter, sameTy, sameRoots, operandChecked⟩ :=
        checkedValue_un_operand frame n operation expression origin ty roots typingAfter rootsAfter typingFuel checked
      subst ty roots
      let child := ordinaryOperandFrame frame n
      have childSource := ordinaryOperandFrame_accepted accepted frame n state types source
      cases fuel with
      | zero => simp [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
      | succ fuel =>
        have childResult := ih fuel child world childSource (.int integer) operandRoots typingAfter operandAfter operandChecked
        change Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment expression state) = state ∧
          (∀ value after, evalValue fuel config frame.interpretation.environment expression state = .ok value after →
            AcceptedValue config.layout types frame.interpretation after (.int integer) operandRoots value) ∧ _ at childResult
        cases evaluated : evalValue fuel config frame.interpretation.environment expression state with
        | stop reason after | escape reason carriers after | jump reason kind after =>
          simp only [evaluated, Goose.Proofs.Exit.stepState] at childResult
          have same := childResult.1
          subst after
          simp only [evalValue, evaluated, bind, Goose.Proofs.Exit.stepState, reduceCtorEq, true_and]
          exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
        | ok value after =>
          have childAccepted := childResult.2.1 value after evaluated
          simp only [evaluated, Goose.Proofs.Exit.stepState] at childResult
          have same := childResult.1
          subst after
          cases represented : childAccepted.represented with
          | integer _ number =>
            cases result : Goose.Core.evalUn config.profile operation integer number with
            | error reason =>
              simp only [evalValue, evaluated, bind, expectInt, pure, result, abortAt, EvalM.stop,
                Goose.Proofs.Exit.stepState, reduceCtorEq, true_and]
              exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
            | ok number =>
              simp only [evalValue, evaluated, bind, expectInt, pure, result, Goose.Proofs.Exit.stepState,
                ExecutionStep.ok.injEq, true_and]
              refine ⟨?_, world, source⟩
              intro output after same
              obtain ⟨rfl, rfl⟩ := same
              exact acceptedValue_integer config.layout types frame.interpretation state integer number
          | stored => contradiction

  | @conversion expression kind target origin form ih =>
    cases typingFuel : frame.typingFuel with
    | zero =>
      have typing := checked.typing
      rw [typingFuel] at typing
      change Except.error _ = Except.ok _ at typing
      cases typing
    | succ n =>
      obtain ⟨integer, targetInt, operandRoots, operandAfter, sameTarget, sameTy, sameRoots, operandChecked⟩ :=
        checkedValue_conv_operand frame n kind target expression origin ty roots typingAfter rootsAfter typingFuel checked
      subst target ty roots
      let child := ordinaryOperandFrame frame n
      have childSource := ordinaryOperandFrame_accepted accepted frame n state types source
      cases fuel with
      | zero => simp [evalValue, timeout, EvalM.stop, Goose.Proofs.Exit.stepState, world, source]
      | succ fuel =>
        have childResult := ih fuel child world childSource (.int integer) operandRoots typingAfter operandAfter operandChecked
        change Goose.Proofs.Exit.stepState (evalValue fuel config frame.interpretation.environment expression state) = state ∧
          (∀ value after, evalValue fuel config frame.interpretation.environment expression state = .ok value after →
            AcceptedValue config.layout types frame.interpretation after (.int integer) operandRoots value) ∧ _ at childResult
        cases evaluated : evalValue fuel config frame.interpretation.environment expression state with
        | stop reason after | escape reason carriers after | jump reason kind after =>
          simp only [evaluated, Goose.Proofs.Exit.stepState] at childResult
          have same := childResult.1
          subst after
          simp only [evalValue, evaluated, bind, Goose.Proofs.Exit.stepState, reduceCtorEq, true_and]
          exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
        | ok value after =>
          have childAccepted := childResult.2.1 value after evaluated
          simp only [evaluated, Goose.Proofs.Exit.stepState] at childResult
          have same := childResult.1
          subst after
          cases represented : childAccepted.represented with
          | integer _ number =>
            cases result : Goose.Core.evalConv config.profile kind integer targetInt number with
            | error reason =>
              simp only [evalValue, evaluated, bind, expectInt, pure, result, abortAt, EvalM.stop,
                Goose.Proofs.Exit.stepState, reduceCtorEq, true_and]
              exact ⟨fun _ _ impossible => False.elim impossible, world, source⟩
            | ok number =>
              simp only [evalValue, evaluated, bind, expectInt, pure, result, Goose.Proofs.Exit.stepState,
                ExecutionStep.ok.injEq, true_and]
              refine ⟨?_, world, source⟩
              intro output after same
              obtain ⟨rfl, rfl⟩ := same
              exact acceptedValue_integer config.layout types frame.interpretation state targetInt number
          | stored => contradiction

#print axioms evalValue_checked_numeric_complete
#print axioms checkedValue_un_operand
#print axioms typeExpr_un_operand
end Goose.Proofs.ConstructionAcceptedExecution
