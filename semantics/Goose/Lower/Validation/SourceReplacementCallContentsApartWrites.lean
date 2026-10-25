import Goose.Lower.Validation.SourceReplacementCallContentsApartMemory
import Goose.GIR.ReplacementContentFlowProofsScopedContentWrites

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR SummaryPreservation ReplacementContentFlowSource
open Goose.GIR.ReplacementContentFlow.Model

theorem rhs_inactive_slice_holder_native {module : Core.Module} {context : Context} {implementation : Impl}
    {rhs : Expr} {active : List VarId} {slot : Nat}
    (holder : RhsInactiveSliceHolder implementation rhs active slot) :
    ∃ storage, (lowerContextAt module context implementation).slots[slot]? = some storage ∧
      storage.ty.isSlice = true := by
  obtain ⟨localVar, row, slice, _, _⟩ := holder
  refine ⟨⟨localVar.ty, localVar.kind, localVar.scope, slot⟩, ?_, slice⟩
  simp [lowerContextAt, lowerImpl, lowerImplFromState, lowerEnv, Array.getElem?_mapIdx, row]

theorem slice_source_scoped_origin {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {lower upperBound source : Nat} {type : Ty}
    (typed : types[source]? = some (some (.data type))) (slice : type.isSlice = true)
    (bounded : lower ≤ source ∧ source < upperBound) :
    ScopedOrigin env root func types upper lower upperBound source := by
  cases type <;> simp [Ty.isSlice] at slice
  case slice mutability element =>
    exact ⟨bounded.1, bounded.2, .inl ⟨.data (.slice mutability element), typed, .slice mutability element⟩⟩

#print axioms rhs_inactive_slice_holder_native
#print axioms slice_source_scoped_origin

end Goose.Lower.Validation
