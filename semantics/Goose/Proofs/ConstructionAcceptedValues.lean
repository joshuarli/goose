import Goose.Proofs.ConstructionAcceptedState

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

theorem acceptedValue_integer (layout : LayoutEnv) (types : RootTypes)
    (interpretation : RootInterpretation) (state : ExecutionState)
    (ty : Goose.Core.IntTy) (value : Int) :
    AcceptedValue layout types interpretation state (.int ty) [] (.int ty value) := by
  refine ⟨.integer ty value, .integer ty value, .integer ty value, ?_⟩
  intro location reference
  cases reference

theorem acceptedValue_boolean (layout : LayoutEnv) (types : RootTypes)
    (interpretation : RootInterpretation) (state : ExecutionState) (value : Bool) :
    AcceptedValue layout types interpretation state .bool [] (.bool value) := by
  refine ⟨.boolean value, .boolean value, .boolean value, ?_⟩
  intro location reference
  cases reference

theorem evalValue_checked_integer (fuel : Nat) (config : EvalConfig)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
    (integerType : Goose.Core.IntTy) (value : Int) (ty : Ty) (roots : List RootRef)
    (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.lit integerType value) ty roots typingAfter rootsAfter) :
    evalValue (fuel + 1) config frame.interpretation.environment (.lit integerType value) state =
        .ok (.int integerType value) state ∧
      AcceptedValue config.layout types frame.interpretation state ty roots (.int integerType value) := by
  have typing := checked.typing
  have provenance := checked.provenance
  cases h : frame.typingFuel with
  | zero =>
    rw [h] at typing
    change Except.error _ = Except.ok _ at typing
    cases typing
  | succ typeFuel =>
    simp only [h, typeExpr, pure, Except.ok.injEq, Prod.mk.injEq, List.cons.injEq] at typing
    simp only [rpExpr, pure, StateT.run, Except.ok.injEq, Prod.mk.injEq] at provenance
    obtain ⟨rfl, _⟩ := provenance
    obtain ⟨⟨rfl, _⟩, _⟩ := typing
    exact ⟨by simp only [evalValue, pure],
      acceptedValue_integer config.layout types frame.interpretation state integerType value⟩

theorem evalValue_checked_boolean (fuel : Nat) (config : EvalConfig)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
    (value : Bool) (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.bool value) ty roots typingAfter rootsAfter) :
    evalValue (fuel + 1) config frame.interpretation.environment (.bool value) state = .ok (.bool value) state ∧
      AcceptedValue config.layout types frame.interpretation state ty roots (.bool value) := by
  have typing := checked.typing
  have provenance := checked.provenance
  cases h : frame.typingFuel with
  | zero =>
    rw [h] at typing
    change Except.error _ = Except.ok _ at typing
    cases typing
  | succ typeFuel =>
    simp only [h, typeExpr, pure, Except.ok.injEq, Prod.mk.injEq, List.cons.injEq] at typing
    simp only [rpExpr, pure, StateT.run, Except.ok.injEq, Prod.mk.injEq] at provenance
    obtain ⟨rfl, _⟩ := provenance
    obtain ⟨⟨rfl, _⟩, _⟩ := typing
    exact ⟨by simp only [evalValue, pure],
      acceptedValue_boolean config.layout types frame.interpretation state value⟩

#print axioms evalValue_checked_integer
#print axioms evalValue_checked_boolean

end Goose.Proofs.ConstructionAcceptedExecution
