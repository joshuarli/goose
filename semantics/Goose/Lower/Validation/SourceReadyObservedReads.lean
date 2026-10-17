import Goose.Lower.Validation.SourceReadyInductionPlaces
import Goose.Lower.Validation.SourceReadyObservationAccess

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFunction.read_with_observations (facts : SourceReadyFunction) {typingEnv : TEnv}
    {place : Place} {type : Ty} {startOffset finishOffset : Nat} {results : List Ty} {before : LS}
    (tables : SourceRootTables typingEnv facts.source)
    (typed : Core.tyExpr typingEnv (.read place) startOffset = .ok (type, finishOffset))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows facts.types
      (lowerExpr (.read place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (visible : VisibleSlotsReady typingEnv facts.state)
    (extension : (lowerExpr (.read place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext facts.completed)
    (allocated : (lowerExpr (.read place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ facts.completed.vals.size)
    (child : ∀ info finish, Core.tyPlace typingEnv place startOffset = .ok (info, finish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows facts.types
        (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext facts.completed →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ facts.completed.vals.size →
      VisibleSlotsReady typingEnv facts.state →
      ValueReadyAt facts.state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
        EmitsOnly (ReadyCallObservations (lower facts.source.mod) facts.func facts.state) before
          (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2) :
    ValueReadyAt facts.state (lowerExpr (.read place)) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations (lower facts.source.mod) facts.func facts.state) before
        (lowerExpr (.read place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let loaded := Lower.emitDef (.load address.1) env address.2
  have actual : lowerExpr (.read place) env before = loaded := typedRead_run typed results before
  have advance : address.2.Adv loaded.2 := adv_emitDef
    (show Lower.emitDef (.load address.1) env address.2 = loaded from rfl)
  have childNative : SummaryPreservation.NativeRows facts.types address.2 := by
    apply native.of_prefix
    rw [actual]
    exact types_emitDef (.load address.1) env address.2 _ _ rfl
  have childExtension : address.2.Ext facts.completed := advance.ext.trans (by
    change loaded.2.Ext facts.completed
    rw [← actual]
    exact extension)
  have childAllocated : address.2.vals.size ≤ facts.completed.vals.size := Nat.le_trans advance.vals (by
    change loaded.2.vals.size ≤ facts.completed.vals.size
    rw [← actual]
    exact allocated)
  obtain ⟨info, childFinish, childSource⟩ := tyExpr_read_place typed
  have pair := child info childFinish childSource.1 generated childNative childExtension childAllocated visible
  refine ⟨facts.read tables typed generated native visible extension allocated ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _
    exact pair.1
  · exact ReadyCallObservations.read place pair.2

theorem SourceReadyFunction.dereference_with_observations (facts : SourceReadyFunction)
    {typingEnv : TEnv} {expression : Expr} {info : PlaceInfo} {start finish : Nat}
    {results : List Ty} {before : LS}
    (source : Core.tyPlace typingEnv (.deref expression) start = .ok (info, finish))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows facts.types
      (lowerPlace (.deref expression) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (extension : (lowerPlace (.deref expression) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext facts.completed)
    (allocated : (lowerPlace (.deref expression) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ facts.completed.vals.size)
    (visible : VisibleSlotsReady typingEnv facts.state)
    (child : ∀ childType childStart childFinish,
      Core.tyExpr typingEnv expression childStart = .ok (childType, childFinish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows facts.types
        (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext facts.completed →
      (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ facts.completed.vals.size →
      VisibleSlotsReady typingEnv facts.state →
      ValueReadyAt facts.state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
        EmitsOnly (ReadyCallObservations (lower facts.source.mod) facts.func facts.state) before
          (lowerExpr expression (lowerEnv typingEnv.mod typingEnv.vars results) before).2) :
    ValueReadyAt facts.state (lowerPlace (.deref expression)) (lowerEnv typingEnv.mod typingEnv.vars results) before ∧
      EmitsOnly (ReadyCallObservations (lower facts.source.mod) facts.func facts.state) before
        (lowerPlace (.deref expression) (lowerEnv typingEnv.mod typingEnv.vars results) before).2 := by
  cases special : Core.sliceRefTy typingEnv expression with
  | none =>
    obtain ⟨mutability, childFinish, childSource⟩ := tyPlace_deref_child special source
    have pair := child (.ref mutability info.ty) start childFinish childSource generated native extension allocated visible
    exact ⟨pair.1, ReadyCallObservations.placeDeref expression pair.2⟩
  | some target =>
    have shape : ∃ variableId, expression = .read (.var variableId) := by
      cases expression <;> try (simp [Core.sliceRefTy] at special)
      rename_i place
      cases place <;> try (simp [Core.sliceRefTy] at special)
      exact ⟨_, rfl⟩
    obtain ⟨variableId, rfl⟩ := shape
    refine ⟨facts.frame.sourceSliceReferencePlace facts.canonical facts.native.valuesSize
      facts.native.definitions facts.native.quiet facts.growth facts.occurrences facts.below
      special generated native visible extension allocated, ?_⟩
    exact ReadyCallObservations.placeDeref (.read (.var variableId))
      (ReadyCallObservations.read (.var variableId) (ReadyCallObservations.placeVariable variableId))

#print axioms SourceReadyFunction.dereference_with_observations
#print axioms SourceReadyFunction.read_with_observations

end Goose.Lower.Validation.ReplacementContentFlowSource
