import Goose.Proofs.ConstructionAcceptedScalarBinding

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem bindAll_freshScalar_accepted {config : EvalConfig} {accepted : AcceptedModule config}
    {frame : ConstructionSourceFrame} {before : ExecutionState} {types : RootTypes}
    {ambient : OwnershipAmbient} {live : Goose.Core.RootInst → Prop}
    {regions : List ReceivingRegion} {pending : List PendingCarrierFrame}
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (id : Nat) (descriptor : LocalVar) (scope : Nat) (value : Value)
    (rootOrder : id = frame.rootCursor.nextVar) (typingOrder : id = frame.typingCounter)
    (declared : frame.typing.variables[id]? = some descriptor)
    (resolved : rootOf frame.interpretation.environment id before =
      .ok (.local frame.interpretation.environment.act scope id) before)
    (scalar : (∃ intTy, descriptor.ty = .int intTy) ∨ descriptor.ty = .bool)
    (represented : ValueRepresentation descriptor.ty value)
    (pointers : PointerTypedValue types descriptor.ty value) :
    ∃ after, bindAll frame.interpretation.environment.act scope [(id, value)] before = .ok () after ∧
      RootTypesExtend types (registerRootType types (.local frame.interpretation.environment.act scope id) descriptor.ty) ∧
      AcceptedWorld config frame.initialized after ambient
        (registerRootType types (.local frame.interpretation.environment.act scope id) descriptor.ty)
        (fun other => other = .local frame.interpretation.environment.act scope id ∨ live other) regions pending ∧
      AcceptedFrame config accepted (advanceLocalFrame frame id) after
        (registerRootType types (.local frame.interpretation.environment.act scope id) descriptor.ty) := by
  have uninitialized : frame.rootCursor.nextVar ≤ id ∨ id ∈ frame.source.initializing :=
    Or.inl (by rw [rootOrder]; exact Nat.le_refl _)
  have fresh := (source.uninitializedLocals id uninitialized _ resolved).2
  have freshType := source.uninitializedTypes id uninitialized _ resolved
  have compatible : RootTypeCompatible types (.local frame.interpretation.environment.act scope id) descriptor.ty := by
    intro prior present
    rw [freshType] at present
    cases present
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
  have conform : LayoutConforms config.layout descriptor.ty := by
    rcases scalar with ⟨intTy, same⟩ | same <;> simp [same, LayoutConforms]
  obtain ⟨_, frontier, synthetic⟩ := source.uninitializedLocal_fresh id _ uninitialized resolved
  obtain ⟨after, bound, extended, afterWorld⟩ := bindRoot_freshScalar_world config frame.initialized before ambient types live
    (.local frame.interpretation.environment.act scope id) descriptor.ty value regions pending world scalarValue fresh
    compatible conform represented pointers frontier synthetic
  have afterSource := source.bindFreshScalar_advance world id descriptor _ value scalarValue rootOrder typingOrder declared represented resolved bound
  refine ⟨after, ?_, extended, afterWorld, afterSource⟩
  simp [bindAll, List.forIn_cons, bind, pure, bound]

#print axioms bindAll_freshScalar_accepted
end Goose.Proofs.ConstructionAcceptedExecution
