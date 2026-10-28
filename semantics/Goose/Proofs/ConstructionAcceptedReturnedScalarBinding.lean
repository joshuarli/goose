import Goose.Proofs.ConstructionAcceptedRegisterCallerFrame
import Goose.Proofs.ConstructionAcceptedScalarParameter

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionRootCorrespondence

theorem AcceptedFrame.bindReturnedScalar
    {config : EvalConfig} {accepted : AcceptedModule config} {frame : ConstructionSourceFrame}
    {before : ExecutionState} {types : RootTypes} {ambient : OwnershipAmbient}
    {live : Goose.Core.RootInst → Prop} {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (source : AcceptedFrame config accepted frame before types)
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (id scope : Nat) (descriptor : LocalVar) (value : Value)
    (rootOrder : id = frame.rootCursor.nextVar) (typingOrder : id = frame.typingCounter)
    (declared : frame.typing.variables[id]? = some descriptor)
    (resolved : rootOf frame.interpretation.environment id before =
      .ok (.local frame.interpretation.environment.act scope id) before)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (represented : ValueRepresentation descriptor.ty value) :
    ∃ after, bindRoot (.local frame.interpretation.environment.act scope id) value before = .ok () after ∧
      RootTypesExtend types (registerRootType types (.local frame.interpretation.environment.act scope id) descriptor.ty) ∧
      AcceptedWorld config frame.initialized after ambient
        (registerRootType types (.local frame.interpretation.environment.act scope id) descriptor.ty)
        (fun other => other = .local frame.interpretation.environment.act scope id ∨ live other) regions pending ∧
      AcceptedFrame config accepted (advanceLocalFrame frame id) after
        (registerRootType types (.local frame.interpretation.environment.act scope id) descriptor.ty) := by
  have scalarValue : (∃ intTy number, value = .int intTy number) ∨ ∃ boolean, value = .bool boolean := by
    rcases scalar with ⟨intTy, same⟩ | same
    · rw [same] at represented
      cases represented with
      | integer intTy number => exact Or.inl ⟨intTy, number, rfl⟩
      | stored ty stored nonfixed logical => simp [Ty.nonfixed] at nonfixed
    · rw [same] at represented
      cases represented with
      | boolean boolean => exact Or.inr ⟨boolean, rfl⟩
      | stored ty stored nonfixed logical => simp [Ty.nonfixed] at nonfixed
  have pointers : PointerTypedValue types descriptor.ty value := by
    rcases scalar with ⟨intTy, same⟩ | same
    · rw [same] at represented ⊢
      cases represented with
      | integer intTy number => exact .integer intTy number
      | stored ty stored nonfixed logical => simp [Ty.nonfixed] at nonfixed
    · rw [same] at represented ⊢
      cases represented with
      | boolean boolean => exact .boolean boolean
      | stored ty stored nonfixed logical => simp [Ty.nonfixed] at nonfixed
  have uninitialized : frame.rootCursor.nextVar ≤ id ∨ id ∈ frame.source.initializing := Or.inl (by rw [rootOrder]; exact Nat.le_refl _)
  obtain ⟨fresh, frontier, synthetic⟩ := source.uninitializedLocal_fresh id _ uninitialized resolved
  have compatible : RootTypeCompatible types (.local frame.interpretation.environment.act scope id) descriptor.ty := by
    intro previous present
    rw [source.uninitializedTypes id uninitialized _ resolved] at present
    cases present
  have conforms : LayoutConforms config.layout descriptor.ty := by
    rcases scalar with ⟨intTy, same⟩ | same <;> simp [same, LayoutConforms]
  obtain ⟨after, bound, extended, finalWorld⟩ := bindRoot_freshScalar_world config frame.initialized before ambient types live
    (.local frame.interpretation.environment.act scope id) descriptor.ty value regions pending world scalarValue fresh
    compatible conforms represented pointers frontier synthetic
  exact ⟨after, bound, extended, finalWorld,
    source.bindFreshScalar_advance world id descriptor _ value scalarValue rootOrder typingOrder declared represented resolved bound⟩

#print axioms AcceptedFrame.bindReturnedScalar
end Goose.Proofs.ConstructionAcceptedExecution
