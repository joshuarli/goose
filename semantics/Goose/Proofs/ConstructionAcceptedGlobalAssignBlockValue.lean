import Goose.Proofs.ConstructionAcceptedGlobalAssignBlockProduce
import Goose.Proofs.ConstructionAcceptedBlockExpressionFrame
import Goose.Proofs.ConstructionAcceptedTwoArgumentExecution

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem evalValue_globalAssign_integerTail_world (fuel checkFuel : Nat)
    (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame) (scope id : Nat) (expression : Expr)
    (origin blockOrigin : Nat) (intTy : Goose.Core.IntTy) (literal : Int) (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (initialized : frame.initialized = config.module.globals.size)
    (fresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ scope)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (position : SourcePosition accepted frame (.expression (.blockE
      ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin)))
    (nesting : frame.typingFuel = checkFuel + 4)
    (scalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool) :
    FirstArgumentOutcome config accepted frame ambient types live regions pending (.int intTy) []
      (evalValue fuel config frame.interpretation.environment (.blockE
        ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) state) := by
  cases fuel with
  | zero => simp [evalValue, timeout, EvalM.stop, FirstArgumentOutcome, Goose.Proofs.Exit.stepState, world, source]
  | succ fuel =>
    obtain ⟨expected, bodyPosition⟩ := position.valueBlockExpression accepted frame scope (checkFuel + 3) blockOrigin
      [.assign (.global id) expression origin] (.lit intTy literal) (by simpa [Nat.add_assoc] using nesting)
    let bodyFrame := valueBlockExpressionFrame frame scope (checkFuel + 3) expected
    have bodySource : AcceptedFrame config accepted bodyFrame state types := source.valueBlockExpression scope (checkFuel + 3) expected
    have safe := evalProduce_globalAssign_integerTail_world fuel checkFuel config accepted bodyFrame state ambient types live regions pending
      scope id expression origin blockOrigin intTy literal form world bodySource initialized fresh absent bodyPosition rfl scalar
    cases produced : evalProduce fuel config frame.interpretation.environment [.register (.int intTy)]
        (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin) state with
    | escape address carriers after | jump target kind after =>
      simp [bodyFrame, valueBlockExpressionFrame, produced, RegisterBreakActionOutcome] at safe
    | stop reason after =>
      simp only [bodyFrame, valueBlockExpressionFrame, produced, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] at safe
      have evaluated := evalValue_integerBlock_of_produceStop fuel config frame.interpretation.environment scope
        [.assign (.global id) expression origin] intTy literal blockOrigin state after reason produced
      have finalSource := source.leaveValueBlockExpression scope (checkFuel + 3) expected safe.1.2.1
      simpa [evaluated, FirstArgumentOutcome, Goose.Proofs.Exit.stepState] using And.intro safe.1.1 (And.intro finalSource True.intro)
    | ok carriers after =>
      simp only [bodyFrame, valueBlockExpressionFrame, produced, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] at safe
      have carrierShape := safe.2
      subst carriers
      have evaluated := evalValue_integerBlock_of_produce fuel config frame.interpretation.environment scope
        [.assign (.global id) expression origin] intTy literal blockOrigin state after (.int intTy literal) produced
      have finalSource := source.leaveValueBlockExpression scope (checkFuel + 3) expected safe.1.2.1
      have value : AcceptedValue config.layout types frame.interpretation after (.int intTy) [] (.int intTy literal) :=
        ⟨.integer intTy literal, .integer intTy literal, .integer intTy literal, by intro location reference; cases reference⟩
      simpa [evaluated, FirstArgumentOutcome, Goose.Proofs.Exit.stepState] using And.intro safe.1.1 (And.intro finalSource value)

#print axioms evalValue_globalAssign_integerTail_world
end Goose.Proofs.ConstructionAcceptedExecution
