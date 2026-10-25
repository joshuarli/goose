import Goose.Proofs.ConstructionAcceptedState

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionExecutionOwnership

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

theorem evalValue_globalReference (fuel : Nat) (config : EvalConfig)
    (interpretation : RootInterpretation) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state ambient types liveRoots regions pending)
    (globals : interpretation.globalCount = config.module.globals.size)
    (id : Nat) (descriptor : Global) (declared : config.module.globals[id]? = some descriptor)
    (mutability : Goose.Core.Mutability) :
    evalValue (fuel + 2) config interpretation.environment (.ref mutability (.global id)) state =
        .ok (.ref ⟨.global id, []⟩) state ∧
      AcceptedValue config.layout types interpretation state (.ref mutability descriptor.ty)
        [.global id] (.ref ⟨.global id, []⟩) := by
  refine ⟨by simp only [evalValue, evalPlace, pure, bind],
    .reference mutability descriptor.ty _, .reference mutability descriptor.ty _ ?_, .reference _, ?_⟩
  · exact ⟨descriptor.ty, world.globalTypes id descriptor declared, .root descriptor.ty⟩
  · intro location reference
    cases reference
    exact ⟨.global id, List.mem_cons_self, .global id (by
      rw [globals]
      exact (Array.getElem?_eq_some_iff.mp declared).1)⟩

theorem evalValue_initializedGlobal (fuel : Nat) (config : EvalConfig)
    (interpretation : RootInterpretation) (initialized : Nat) (state : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (liveRoots : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (world : AcceptedWorld config initialized state ambient types liveRoots regions pending)
    (id : Nat) (available : id < initialized) :
    ∃ descriptor value, config.module.globals[id]? = some descriptor ∧
      evalValue (fuel + 2) config interpretation.environment (.read (.global id)) state = .ok value state ∧
      Goose.Proofs.ConstructionRepresentation.ValueRepresentation descriptor.ty value ∧
      PointerTypedValue types descriptor.ty value ∧
      Goose.Proofs.ConstructionRepresentation.ValueStorageBacked config.layout state value := by
  obtain ⟨descriptor, value, declared, found, represented⟩ := world.globals.2 id available
  refine ⟨descriptor, value, declared, ?_, represented,
    (world.heap _ _ _ (world.globalTypes id descriptor declared) found).2,
    world.backing.values (.global id) (world.globalLive id available) value found⟩
  simp only [evalValue, evalPlace, bind, pure, readLoc, EvalM.get, found, readValuePath]

#print axioms evalValue_checked_integer
#print axioms evalValue_checked_boolean
#print axioms evalValue_globalReference
#print axioms evalValue_initializedGlobal

end Goose.Proofs.ConstructionAcceptedExecution
