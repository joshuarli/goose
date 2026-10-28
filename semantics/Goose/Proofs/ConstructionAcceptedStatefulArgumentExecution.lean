import Goose.Proofs.ConstructionAcceptedStatefulCallArguments

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem evalArguments_statefulScalar_world {config : EvalConfig} {accepted : AcceptedModule config}
    (fuel checkFuel : Nat) (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId callOrigin : Nat) (context : Context) (callee : Impl) (first second : Param)
    (firstDescriptor secondDescriptor : LocalVar) (scope id origin blockOrigin : Nat) (expression : Expr)
    (intTy : Goose.Core.IntTy) (literal : Int) (right : Expr) (form : AcceptedBinaryExpression expression)
    (rightForm : AcceptedBinaryExpression right)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[first, second])
    (firstMode : first.mode = .byValue) (secondMode : second.mode = .byValue)
    (firstDeclared : callee.vars[first.var]? = some firstDescriptor)
    (secondDeclared : callee.vars[second.var]? = some secondDescriptor)
    (firstScalar : (∃ t, firstDescriptor.ty = .int t) ∨ firstDescriptor.ty = .bool)
    (secondScalar : (∃ t, secondDescriptor.ty = .int t) ∨ secondDescriptor.ty = .bool)
    (initialized : frame.initialized = config.module.globals.size)
    (fresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ scope)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (nesting : frame.typingFuel = checkFuel + 6)
    (position : SourcePosition accepted frame (.expression (.call contextId
      [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] callOrigin)))
    (globalScalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool) :
    ∃ rightFrame : ConstructionSourceFrame,
      rightFrame.interpretation = frame.interpretation ∧ rightFrame.initialized = frame.initialized ∧
      let step := evalArguments fuel config frame.interpretation.environment callee.vars [first, second]
        [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] state
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState step) ambient types live regions pending ∧
      AcceptedFrame config accepted rightFrame (Goose.Proofs.Exit.stepState step) types ∧
      match step with
      | .ok values after => ∃ leftValue rightValue, values = [leftValue, rightValue] ∧
          AcceptedValue config.layout types frame.interpretation after (.int intTy) [] leftValue ∧
          AcceptedValue config.layout types frame.interpretation after secondDescriptor.ty [] rightValue
      | .stop .. => True
      | _ => False := by
  obtain ⟨leftAfter, rightRoots, rightTypingAfter, rightAfter, rootEq, firstPosition, rightChecked⟩ :=
    checkedStatefulCallArguments frame state types checkFuel contextId callOrigin context callee first second
      firstDescriptor secondDescriptor scope id origin blockOrigin expression intTy literal right form rightForm
      source contextAt calleeAt parameters firstMode secondMode firstDeclared secondDeclared firstScalar secondScalar
      initialized fresh absent nesting position
  let firstFrame := ordinaryOperandFrame frame (checkFuel + 4)
  let rightFrame := secondStatefulArgumentFrame frame (checkFuel + 3) leftAfter
  have firstSource := ordinaryOperandFrame_accepted accepted frame (checkFuel + 4) state types source
  have rightSource : AcceptedFrame config accepted rightFrame state types := by
    have next := (ordinaryOperandFrame_accepted accepted frame (checkFuel + 3) state types source).withRootCursor
      { leftAfter with eff := {} } (by simpa [ordinaryOperandFrame] using rootEq)
    simpa [rightFrame, secondStatefulArgumentFrame] using next
  have firstSafe (runtimeFuel : Nat) : FirstArgumentOutcome config accepted rightFrame ambient types live regions pending (.int intTy) []
      (evalValue runtimeFuel config frame.interpretation.environment (.blockE
        ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) state) := by
    have actual := evalValue_globalAssign_integerTail_world runtimeFuel checkFuel config accepted firstFrame state ambient types live regions pending
      scope id expression origin blockOrigin intTy literal form world firstSource initialized fresh absent firstPosition rfl globalScalar
    cases evaluated : evalValue runtimeFuel config frame.interpretation.environment (.blockE
        ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) state with
    | escape address carriers after | jump target kind after =>
      simp [firstFrame, ordinaryOperandFrame, evaluated, FirstArgumentOutcome] at actual
    | stop reason after =>
      simp only [firstFrame, ordinaryOperandFrame, evaluated, FirstArgumentOutcome, Goose.Proofs.Exit.stepState] at actual
      have retargeted := (actual.2.1.withTypingFuel (checkFuel + 3)).withRootCursor { leftAfter with eff := {} } rootEq
      simpa [rightFrame, secondStatefulArgumentFrame, ordinaryOperandFrame, evaluated, FirstArgumentOutcome, Goose.Proofs.Exit.stepState] using
        And.intro actual.1 (And.intro retargeted True.intro)
    | ok value after =>
      simp only [firstFrame, ordinaryOperandFrame, evaluated, FirstArgumentOutcome, Goose.Proofs.Exit.stepState] at actual
      have retargeted := (actual.2.1.withTypingFuel (checkFuel + 3)).withRootCursor { leftAfter with eff := {} } rootEq
      simpa [rightFrame, secondStatefulArgumentFrame, ordinaryOperandFrame, evaluated, FirstArgumentOutcome, Goose.Proofs.Exit.stepState] using
        And.intro actual.1 (And.intro retargeted actual.2.2)
  have outcome := evalArguments_two_scalarOutcome rightForm fuel config accepted rightFrame state ambient types live regions pending
    callee.vars first second world rightSource (.int intTy) secondDescriptor.ty [] rightRoots rightTypingAfter rightAfter rightChecked firstSafe
  refine ⟨rightFrame, rfl, rfl, ?_⟩
  cases step : evalArguments fuel config frame.interpretation.environment callee.vars [first, second]
      [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] state with
  | stop reason after => simpa [rightFrame, secondStatefulArgumentFrame, ordinaryOperandFrame, step] using outcome
  | escape address carriers after | jump target kind after => simp [rightFrame, secondStatefulArgumentFrame, ordinaryOperandFrame, step] at outcome
  | ok values after =>
    simp only [rightFrame, secondStatefulArgumentFrame, ordinaryOperandFrame, step, Goose.Proofs.Exit.stepState] at outcome ⊢
    obtain ⟨finalWorld, finalSource, leftValue, rightValue, sameValues, leftValid, rightValid⟩ := outcome
    have rightDirect : DirectValueRooted frame.interpretation [] rightValue := by
      rcases secondScalar with ⟨ty, same⟩ | same
      · rw [same] at rightValid
        cases rightValid.represented with
        | integer ty number => intro location reference; cases reference
        | stored ty value nonfixed => simp [Ty.nonfixed] at nonfixed
      · rw [same] at rightValid
        cases rightValid.represented with
        | boolean boolean => intro location reference; cases reference
        | stored ty value nonfixed => simp [Ty.nonfixed] at nonfixed
    exact ⟨finalWorld, finalSource, leftValue, rightValue, sameValues, leftValid, { rightValid with direct := rightDirect }⟩

#print axioms evalArguments_statefulScalar_world
end Goose.Proofs.ConstructionAcceptedExecution
