import Goose.Lower.Validation.AdmittedSourceStores
import Goose.Lower.Validation.InterfaceTypes
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceStores
import Goose.Lower.Validation.SourceStatementTypingStorage
import Goose.Lower.Validation.DereferenceTyping
import Goose.Lower.Validation.SourceStorage
import Goose.Lower.Validation.SummaryPreservationVariableShape
import Goose.Core.Sound.Invert

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR ReplacementContentFlowSource

theorem tyStmt_assign_reference_target {env output : TEnv} {place : Place} {expr : Expr}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assign place expr origin) start = .ok (output, finish)) :
    ∃ info next, Core.tyPlace env place start = .ok (info, next) ∧
      Core.tyExpr env expr next = .ok (info.ty, finish) ∧
      (info.ty.isRefLike = false ∨ ∃ variableId, place = .deref (.read (.var variableId)) ∧
        info.ty.isSlice = true) := by
  obtain ⟨info, next, placeSource, valueSource, copyable, _, _⟩ := tyStmt_assign_children source
  refine ⟨info, next, placeSource, valueSource, ?_⟩
  cases reference : info.ty.isRefLike with
  | false => exact Or.inl rfl
  | true =>
    have notFlat : info.ty.flat = false := by
      cases type : info.ty <;> simp_all [Ty.isRefLike, Ty.flat]
    have slice : info.ty.isSlice = true ∧ place.derefVar?.isSome = true := by
      simpa only [notFlat, Bool.false_or, Bool.and_eq_true] using copyable
    cases variableAt : place.derefVar? with
    | none => simp [variableAt] at slice
    | some variableId =>
      exact Or.inr ⟨variableId, Core.Sound.derefVar_eq variableAt, slice.1⟩

theorem tyPlace_slice_deref_variable {env : TEnv} {variableId : VarId} {info : PlaceInfo}
    {start finish : Nat}
    (source : Core.tyPlace env (.deref (.read (.var variableId))) start = .ok (info, finish))
    (slice : info.ty.isSlice = true) :
    (env.vars[variableId]?).any (fun localVar => localVar.ty.isRefSlice) = true := by
  by_cases reference : (env.vars[variableId]?).any (fun localVar => localVar.ty.isRefSlice) = true
  · exact reference
  · have ordinary : Core.sliceRefTy env (.read (.var variableId)) = none := by
      simp only [Core.sliceRefTy]
      split
      · cases variableAt : env.vars[variableId]? <;> simp_all
      · rfl
    obtain ⟨mode, next, child⟩ := tyPlace_deref_child ordinary source
    obtain ⟨childInfo, childNext, childPlace, shape, readable⟩ := tyExpr_read_storage child
    rw [← shape] at readable
    cases type : info.ty <;> simp_all [Ty.isSlice, Ty.readable, Ty.refTarget]

theorem ReplacementContentFlowSource.AssignmentStoreOccurrence.admitted_refSlice
    {module : Core.Module} {context : Context} {impl : Impl} {implIndex : ImplId}
    (accepted : Core.validate module = .ok ()) (implAt : module.impls[implIndex]? = some impl)
    {env : PEnv} {root : DemandNode} {upper provenance : Prov}
    {address value : ValueId} {origin : Option OriginId}
    (occurrence : AssignmentStoreOccurrence env root (lowerContextAt module context impl)
      upper address value origin)
    (access : env.access = ⟨module, impl, context⟩)
    {index : Nat} {parameter : Param} (parameterAt : impl.params[index]? = some parameter)
    (shape : occurrence.place = .deref (.read (.var parameter.var)))
    (reference : occurrence.localEnv.isRefSliceVar parameter.var = true)
    (below : ∀ value, rootsAt provenance.vals value ⊆ rootsAt upper.vals value)
    (types : Array (Option VTy)) :
    (lowerContextAt module context impl).admittedInstruction (lower module) types provenance
      (.eff (.store address value origin)) = true := by
  have aligned : parameter.var = index :=
    ((Core.Sound.validate_modOk module accepted).impl implIndex impl implAt |>.params
      index parameter parameterAt).1
  have contextEq : occurrence.localEnv.ctx = context :=
    congrArg AccessEnv.ctx (occurrence.access.trans access)
  apply lowerContextAt_admitted_store_of_source contextEq parameterAt
    (by rw [← shape]; exact occurrence.checked) reference
  · intro actual member
    have singleton := occurrence.formalAddress parameter.var shape reference (below address member)
    simpa only [List.mem_singleton, aligned] using singleton
  · intro actual member
    exact occurrence.valueRefined actual (below value member)

theorem ReplacementContentFlowSource.AssignmentStoreOccurrence.admitted
    {module : Core.Module} {context : Context} {impl : Impl} {implIndex : ImplId}
    (accepted : Core.validate module = .ok ()) (implAt : module.impls[implIndex]? = some impl)
    {env : PEnv} {root : DemandNode} {upper provenance : Prov}
    {address value : ValueId} {origin : Option OriginId}
    (occurrence : AssignmentStoreOccurrence env root (lowerContextAt module context impl)
      upper address value origin)
    (access : env.access = ⟨module, impl, context⟩)
    (below : ∀ value, rootsAt provenance.vals value ⊆ rootsAt upper.vals value)
    (types : Array (Option VTy)) :
    (lowerContextAt module context impl).admittedInstruction (lower module) types provenance
      (.eff (.store address value origin)) = true := by
  obtain ⟨varId, shape, reference⟩ := occurrence.referenceTarget
  have sameImpl : occurrence.localEnv.impl = impl :=
    congrArg AccessEnv.impl (occurrence.access.trans access)
  have sourceReference := reference
  simp only [PEnv.isRefSliceVar, sameImpl] at sourceReference
  cases variableAt : impl.vars[varId]? with
  | none => simp [variableAt] at sourceReference
  | some localVar =>
    have referenceType : localVar.ty.isRefSlice = true := by
      simpa only [variableAt] using sourceReference
    obtain ⟨parameter, parameterAt, aligned, _⟩ :=
      SummaryPreservation.accepted_refSlice_parameter accepted implAt variableAt referenceType
    apply occurrence.admitted_refSlice accepted implAt access parameterAt
    · simpa only [aligned] using shape
    · simpa only [aligned] using reference
    · exact below

theorem ReplacementContentFlowSource.RebindStoreOccurrence.admitted
    {module : GIR.Module} {func : Func} {env : PEnv} {root : DemandNode}
    {upper provenance : Prov} {address value : ValueId} {origin : Option OriginId}
    (occurrence : RebindStoreOccurrence env root func upper address value origin)
    (below : rootsAt provenance.vals address ⊆ rootsAt upper.vals address)
    (types : Array (Option VTy)) :
    func.admittedInstruction module types provenance (.eff (.store address value origin)) = true := by
  simp only [Func.admittedInstruction, Bool.or_eq_true]
  apply Or.inr
  apply List.all_eq_true.mpr
  intro actual member
  have singleton := below member
  rw [occurrence.addressRoots] at singleton
  have same := List.mem_singleton.mp singleton
  rw [same]

theorem ReplacementContentFlowSource.StoreOccurrence.admitted_context
    {module : Core.Module} {context : Context} {impl : Impl} {implIndex : ImplId}
    (accepted : Core.validate module = .ok ()) (implAt : module.impls[implIndex]? = some impl)
    {env : PEnv} {root : DemandNode} {upper provenance : Prov}
    {address value : ValueId} {origin : Option OriginId}
    (occurrence : StoreOccurrence env root (lowerContextAt module context impl) upper address value origin)
    (access : env.access = ⟨module, impl, context⟩)
    (below : ∀ value, rootsAt provenance.vals value ⊆ rootsAt upper.vals value)
    (types : Array (Option VTy)) :
    (lowerContextAt module context impl).admittedInstruction (lower module) types provenance
      (.eff (.store address value origin)) = true := by
  rcases occurrence with assigned | rebound
  · obtain ⟨assigned⟩ := assigned
    exact assigned.admitted accepted implAt access below types
  · obtain ⟨rebound⟩ := rebound
    exact rebound.admitted (below address) types

theorem ReplacementContentFlowSource.StoreOccurrence.admitted_global
    {module : Core.Module} {global : Core.Global}
    {env : PEnv} {root : DemandNode} {upper provenance : Prov}
    {address value : ValueId} {origin : Option OriginId}
    (occurrence : StoreOccurrence env root (lowerGlobal module global).init upper address value origin)
    (access : env.access = ⟨module, initImpl, initContext⟩)
    (below : ∀ value, rootsAt provenance.vals value ⊆ rootsAt upper.vals value)
    (types : Array (Option VTy)) :
    (lowerGlobal module global).init.admittedInstruction (lower module) types provenance
      (.eff (.store address value origin)) = true := by
  rcases occurrence with assigned | rebound
  · obtain ⟨assigned⟩ := assigned
    obtain ⟨varId, _, reference⟩ := assigned.referenceTarget
    have sameImpl : assigned.localEnv.impl = initImpl :=
      congrArg AccessEnv.impl (assigned.access.trans access)
    simp [PEnv.isRefSliceVar, sameImpl, initImpl] at reference
  · obtain ⟨rebound⟩ := rebound
    exact rebound.admitted (below address) types

#print axioms ReplacementContentFlowSource.AssignmentStoreOccurrence.admitted_refSlice
#print axioms ReplacementContentFlowSource.AssignmentStoreOccurrence.admitted
#print axioms ReplacementContentFlowSource.RebindStoreOccurrence.admitted
#print axioms ReplacementContentFlowSource.StoreOccurrence.admitted_context
#print axioms ReplacementContentFlowSource.StoreOccurrence.admitted_global
#print axioms tyStmt_assign_reference_target
#print axioms tyPlace_slice_deref_variable

end Goose.Lower.Validation
