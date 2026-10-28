import Goose.Proofs.ConstructionAcceptedScalarParameter

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

inductive FreshScalarParameterPlan (scope : Nat) :
    ConstructionSourceFrame → RootTypes → (Goose.Core.RootInst → Prop) → List (Nat × Value) →
      ConstructionSourceFrame → RootTypes → (Goose.Core.RootInst → Prop) → Prop
  | nil (frame : ConstructionSourceFrame) (types : RootTypes) (live : Goose.Core.RootInst → Prop) :
      FreshScalarParameterPlan scope frame types live [] frame types live
  | cons {frame : ConstructionSourceFrame} {types : RootTypes} {live : Goose.Core.RootInst → Prop}
      {id : Nat} {descriptor : LocalVar} {value : Value} {rest : List (Nat × Value)}
      {finalFrame : ConstructionSourceFrame} {finalTypes : RootTypes} {finalLive : Goose.Core.RootInst → Prop}
      (rootOrder : id = frame.rootCursor.nextVar) (typingOrder : id = frame.typingCounter)
      (declared : frame.typing.variables[id]? = some descriptor)
      (resolved : ∀ state, rootOf frame.interpretation.environment id state =
        .ok (.local frame.interpretation.environment.act scope id) state)
      (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
      (represented : ValueRepresentation descriptor.ty value) (pointers : PointerTypedValue types descriptor.ty value)
      (tail : FreshScalarParameterPlan scope (advanceLocalFrame frame id)
        (registerRootType types (.local frame.interpretation.environment.act scope id) descriptor.ty)
        (fun other => other = .local frame.interpretation.environment.act scope id ∨ live other)
        rest finalFrame finalTypes finalLive) :
      FreshScalarParameterPlan scope frame types live ((id, value) :: rest) finalFrame finalTypes finalLive

theorem bindAll_cons_of_single (act scope id : Nat) (value : Value) (rest : List (Nat × Value))
    (before middle after : ExecutionState)
    (first : bindAll act scope [(id, value)] before = .ok () middle)
    (tail : bindAll act scope rest middle = .ok () after) :
    bindAll act scope ((id, value) :: rest) before = .ok () after := by
  cases firstStep : bindRoot (.local act scope id) value before with
  | stop reason state | escape address carriers state | jump target kind state =>
    simp [bindAll, List.forIn_cons, bind, pure, firstStep] at first
  | ok result state =>
    cases result
    have same : state = middle := by simpa [bindAll, List.forIn_cons, bind, pure, firstStep] using first
    subst state
    simpa [bindAll, List.forIn_cons, bind, pure, firstStep] using tail

theorem bindAll_freshScalarList_accepted {config : EvalConfig} {accepted : AcceptedModule config}
    {scope : Nat} {frame : ConstructionSourceFrame} {types : RootTypes} {live : Goose.Core.RootInst → Prop}
    {values : List (Nat × Value)} {finalFrame : ConstructionSourceFrame} {finalTypes : RootTypes} {finalLive : Goose.Core.RootInst → Prop}
    (plan : FreshScalarParameterPlan scope frame types live values finalFrame finalTypes finalLive) :
    ∀ (before : ExecutionState) (ambient : OwnershipAmbient) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame),
      AcceptedWorld config frame.initialized before ambient types live regions pending →
      AcceptedFrame config accepted frame before types →
      ∃ after, bindAll frame.interpretation.environment.act scope values before = .ok () after ∧
        RootTypesExtend types finalTypes ∧
        AcceptedWorld config frame.initialized after ambient finalTypes finalLive regions pending ∧
        AcceptedFrame config accepted finalFrame after finalTypes := by
  induction plan with
  | nil frame types live =>
    intro before ambient regions pending world source
    exact ⟨before, by simp [bindAll, bind, pure], (fun _ _ found => found), world, source⟩
  | @cons frame types live id descriptor value rest finalFrame finalTypes finalLive rootOrder typingOrder declared resolved scalar represented pointers tail ih =>
    intro before ambient regions pending world source
    obtain ⟨middle, first, extended, middleWorld, middleSource⟩ := bindAll_freshScalar_accepted world source
      id descriptor scope value rootOrder typingOrder declared (resolved before) scalar represented pointers
    obtain ⟨after, remaining, extendedTail, finalWorld, finalSource⟩ := ih middle ambient regions pending middleWorld middleSource
    refine ⟨after, ?_, ?_, ?_, finalSource⟩
    · apply bindAll_cons_of_single _ _ _ _ _ _ middle _ first
      simpa [advanceLocalFrame] using remaining
    · intro root ty present
      exact extendedTail root ty (extended root ty present)
    · simpa [advanceLocalFrame] using finalWorld

#print axioms bindAll_cons_of_single
#print axioms bindAll_freshScalarList_accepted
end Goose.Proofs.ConstructionAcceptedExecution
