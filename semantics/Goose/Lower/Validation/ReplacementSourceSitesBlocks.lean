import Goose.Lower.Validation.ReplacementSourceSitesHeaders

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ReplacementSitesAt.block_generated {le : LEnv} {before : LS} (loop : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (want : Bool) (scope : ScopeId)
    (statements : List Stmt) (value : Option Expr)
    (generated : GeneratedBuilderState before) (bounds : LoopBuilderTargets loop before)
    (statementsStorage : ∀ state, GeneratedBuilderState state → LoopBuilderTargets loop state →
      ReplacementSitesAt le state (lowerStmts loop statements))
    (valueStorage : ∀ state, GeneratedBuilderState state → ReplacementSitesAt le state (lowerBlockValue want value)) :
    ReplacementSitesAt le before (lowerBlock loop pre want (.mk scope statements value)) := by
  let entered := Goose.Lower.emitEffect (.enter scope) le before
  let pushed := Goose.Lower.pushScope scope le entered.2
  let initialized := Goose.Lower.initSlots pre le pushed.2
  let ended := lowerStmts loop statements le initialized.2
  have enteredGenerated := generated.emitEffect (.enter scope)
    (show Goose.Lower.emitEffect _ le before = entered from rfl)
  have pushedGenerated : GeneratedBuilderState pushed.2 :=
    ⟨enteredGenerated.dense, enteredGenerated.live, enteredGenerated.targets⟩
  have initializedGenerated := pushedGenerated.initSlots pre
    (show Goose.Lower.initSlots pre le pushed.2 = initialized from rfl)
  have initialBlocks : before.blocks.size ≤ initialized.2.blocks.size := by
    have first := (dense_emitEffect (.enter scope) le before entered.1 entered.2 rfl generated.dense generated.live).2.2
    have second := (dense_pushScope scope le entered.2 pushed.1 pushed.2 rfl enteredGenerated.dense enteredGenerated.live).2.2
    have third := (dense_initSlots pre le pushed.2 initialized.1 initialized.2 rfl pushedGenerated.dense pushedGenerated.live).2.2
    exact Nat.le_trans first (Nat.le_trans second third)
  have initializedBounds := bounds.mono initialBlocks
  have endedGenerated := initializedGenerated.lowerStmts loop statements initializedBounds
    (show lowerStmts loop statements le initialized.2 = ended from rfl)
  unfold Goose.Lower.lowerBlock Goose.Lower.inScope
  apply (ReplacementSitesAt.emitEffect _ (by intros; trivial)).bind
  apply (ReplacementSitesAt.pushScope _ _ _).bind
  apply ReplacementSitesAt.bind
  · apply (ReplacementSitesAt.initSlots _ _ _).bind
    apply (statementsStorage initialized.2 initializedGenerated initializedBounds).bind
    apply (valueStorage ended.2 endedGenerated).bind
    exact (ReplacementSitesAt.emitEffect _ (by intros; trivial)).bind (ReplacementSitesAt.pure _ _ _)
  · exact (ReplacementSitesAt.popScope _ _).bind (ReplacementSitesAt.pure _ _ _)

end Goose.Lower.Validation
