import Goose.Proofs.ConstructionAcceptedStatefulArgumentList

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem evalValue_checkedScalar_argumentOutcome {expression : Expr} (form : AcceptedBinaryExpression expression)
    (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState) (checked : CheckedValue frame expression ty roots typingAfter rootsAfter)
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool) :
    FirstArgumentOutcome config accepted frame ambient types live regions pending ty []
      (evalValue fuel config frame.interpretation.environment expression state) := by
  have outcome := evalValue_checked_binary_recursive form fuel config accepted frame state ambient types live regions pending
    world source ty roots typingAfter rootsAfter checked
  have control := evalValue_scalar_controlFree form fuel config frame.interpretation.environment
  cases evaluated : evalValue fuel config frame.interpretation.environment expression state with
  | escape address carriers after => exact False.elim (control.1 state address carriers after evaluated)
  | jump target kind after => exact False.elim (control.2 state target kind after evaluated)
  | stop reason after =>
    simp only [evaluated, Goose.Proofs.Exit.stepState] at outcome
    have same := outcome.1
    subst after
    simp [evaluated, FirstArgumentOutcome, Goose.Proofs.Exit.stepState, world, source]
  | ok value after =>
    have valid := outcome.2.1 value after evaluated
    simp only [evaluated, Goose.Proofs.Exit.stepState] at outcome
    have same := outcome.1
    subst after
    have direct : DirectValueRooted frame.interpretation [] value := by
      rcases scalar with ⟨intTy, same⟩ | same
      · rw [same] at valid
        cases valid.represented with
        | integer intTy number => intro location reference; cases reference
        | stored ty value nonfixed => simp [Ty.nonfixed] at nonfixed
      · rw [same] at valid
        cases valid.represented with
        | boolean boolean => intro location reference; cases reference
        | stored ty value nonfixed => simp [Ty.nonfixed] at nonfixed
    exact ⟨world, source, { valid with direct := direct }⟩

#print axioms evalValue_checkedScalar_argumentOutcome
end Goose.Proofs.ConstructionAcceptedExecution
