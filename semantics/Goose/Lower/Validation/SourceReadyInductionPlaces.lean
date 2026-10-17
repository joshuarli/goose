import Goose.Lower.Validation.SourceReadyInductionFacts
import Goose.Lower.Validation.SourceReadyTypedPlaces
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyHolderSource

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFunction.dereference (facts : SourceReadyFunction)
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
      ValueReadyAt facts.state (lowerExpr expression) (lowerEnv typingEnv.mod typingEnv.vars results) before) :
    ValueReadyAt facts.state (lowerPlace (.deref expression)) (lowerEnv typingEnv.mod typingEnv.vars results) before := by
  cases special : Core.sliceRefTy typingEnv expression with
  | none => exact typed_ready_dereference special source generated native extension allocated visible child
  | some target =>
    have shape : ∃ variableId, expression = .read (.var variableId) := by
      cases expression <;> try (simp [Core.sliceRefTy] at special)
      rename_i place
      cases place <;> try (simp [Core.sliceRefTy] at special)
      exact ⟨_, rfl⟩
    obtain ⟨variableId, rfl⟩ := shape
    exact facts.frame.sourceSliceReferencePlace facts.canonical facts.native.valuesSize
      facts.native.definitions facts.native.quiet facts.growth facts.occurrences facts.below
      special generated native visible extension allocated

#print axioms SourceReadyFunction.dereference

end Goose.Lower.Validation.ReplacementContentFlowSource
