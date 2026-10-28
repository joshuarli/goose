import Goose.Proofs.ConstructionAcceptedScalarParameter
import Goose.Proofs.ConstructionRootCorrespondenceScopes

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem bindAll_two_of_single (act scope first second : Nat) (firstValue secondValue : Value)
    (before middle after : ExecutionState)
    (firstBound : bindAll act scope [(first, firstValue)] before = .ok () middle)
    (secondBound : bindAll act scope [(second, secondValue)] middle = .ok () after) :
    bindAll act scope [(first, firstValue), (second, secondValue)] before = .ok () after := by
  cases firstStep : bindRoot (.local act scope first) firstValue before with
  | stop reason state | escape reason carriers state | jump target kind state =>
    simp [bindAll, List.forIn_cons, bind, pure, firstStep] at firstBound
  | ok result state =>
    cases result
    have same : state = middle := by simpa [bindAll, List.forIn_cons, bind, pure, firstStep] using firstBound
    subst state
    simpa [bindAll, List.forIn_cons, bind, pure, firstStep] using secondBound

theorem bindAll_two_freshScalars_accepted {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {before : ExecutionState} {types : RootTypes}
    {ambient : OwnershipAmbient} {live : Goose.Core.RootInst → Prop}
    {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (first second : Nat) (firstDescriptor secondDescriptor : LocalVar) (scope : Nat)
    (firstValue secondValue : Value)
    (firstRootOrder : first = frame.rootCursor.nextVar) (firstTypingOrder : first = frame.typingCounter)
    (firstDeclared : frame.typing.variables[first]? = some firstDescriptor)
    (firstResolved : rootOf frame.interpretation.environment first before =
      .ok (.local frame.interpretation.environment.act scope first) before)
    (firstScalar : (∃ intTy, firstDescriptor.ty = .int intTy) ∨ firstDescriptor.ty = .bool)
    (firstRepresented : ValueRepresentation firstDescriptor.ty firstValue)
    (firstPointers : PointerTypedValue types firstDescriptor.ty firstValue)
    (secondRootOrder : second = (advanceLocalFrame frame first).rootCursor.nextVar)
    (secondTypingOrder : second = (advanceLocalFrame frame first).typingCounter)
    (secondDeclared : (advanceLocalFrame frame first).typing.variables[second]? = some secondDescriptor)
    (secondResolved : rootOf frame.interpretation.environment second before =
      .ok (.local frame.interpretation.environment.act scope second) before)
    (secondScalar : (∃ intTy, secondDescriptor.ty = .int intTy) ∨ secondDescriptor.ty = .bool)
    (secondRepresented : ValueRepresentation secondDescriptor.ty secondValue)
    (secondPointers : PointerTypedValue types secondDescriptor.ty secondValue) :
    ∃ after,
      bindAll frame.interpretation.environment.act scope [(first, firstValue), (second, secondValue)] before = .ok () after ∧
      AcceptedWorld config frame.initialized after ambient
        (registerRootType (registerRootType types (.local frame.interpretation.environment.act scope first) firstDescriptor.ty)
          (.local frame.interpretation.environment.act scope second) secondDescriptor.ty)
        (fun other => other = .local frame.interpretation.environment.act scope second ∨
          other = .local frame.interpretation.environment.act scope first ∨ live other) regions pending ∧
      AcceptedFrame config accepted (advanceLocalFrame (advanceLocalFrame frame first) second) after
        (registerRootType (registerRootType types (.local frame.interpretation.environment.act scope first) firstDescriptor.ty)
          (.local frame.interpretation.environment.act scope second) secondDescriptor.ty) := by
  obtain ⟨middle, firstBound, extended, middleWorld, middleSource⟩ := bindAll_freshScalar_accepted world source
    first firstDescriptor scope firstValue firstRootOrder firstTypingOrder firstDeclared firstResolved
    firstScalar firstRepresented firstPointers
  have nextPointers := secondPointers.types_extend types _ extended secondDescriptor.ty secondValue
  have secondAtMiddle := rootOf_transfer frame.interpretation second before middle
    (.local frame.interpretation.environment.act scope second) secondResolved
  obtain ⟨after, secondBound, _, afterWorld, afterSource⟩ := bindAll_freshScalar_accepted (frame := advanceLocalFrame frame first) middleWorld middleSource
    second secondDescriptor scope secondValue secondRootOrder secondTypingOrder secondDeclared
    (by simpa [advanceLocalFrame] using secondAtMiddle) secondScalar secondRepresented nextPointers
  refine ⟨after, ?_, ?_, ?_⟩
  · apply bindAll_two_of_single _ _ _ _ _ _ _ middle _ firstBound
    simpa [advanceLocalFrame] using secondBound
  · simpa [advanceLocalFrame] using afterWorld
  · simpa [advanceLocalFrame] using afterSource

#print axioms bindAll_two_freshScalars_accepted
#print axioms bindAll_two_of_single
end Goose.Proofs.ConstructionAcceptedExecution
