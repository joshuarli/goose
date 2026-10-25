import Goose.Lower.Validation.SourceReplacementLexicalWritersStoreAssignments
import Goose.Lower.Validation.SourceReplacementLexicalWritersStoreRebinds
import Goose.Lower.Validation.SourceReplacementLexicalWritersStoreOperations
import Goose.Lower.Validation.SourceReplacementWriterLedgerShapes
import Goose.Lower.Validation.SourceReplacementWriterTypingAccepted
import Goose.Lower.Validation.SummaryPreservationLowerAssignOp

namespace Goose.Lower.Validation.SourceReplacementLexicalWriters

open Goose.Core Goose.Core.Sound Goose.GIR ReplacementContentFlowSource SummaryPreservation
open SourceReplacementWriterLedger SourceReplacementWriterTyping

theorem store_emission_tracked_visible (facts : SourceReadyFunction)
    {typing : TEnv} (tables : SourceRootTables typing facts.source)
    {fragment : Fragment} (typed : NodeTyped typing fragment.node)
    {results : List Ty} {before : LS} (generated : GeneratedBuilderState before)
    (native : NativeRows facts.types (fragment.finish (lowerEnv typing.mod typing.vars results) before))
    (continuation : NativeBuilderContinuation facts.func (fragment.finish (lowerEnv typing.mod typing.vars results) before))
    {event : Emission} (member : event ∈ fragment.emissions (lowerEnv typing.mod typing.vars results) before)
    {address value : ValueId} {origin : Option OriginId} (same : event.instruction = .eff (.store address value origin))
    (reference : valRefLike facts.types value = true) {tracked : VarId}
    (upper : rootsAt facts.upper.vals address = [.local tracked]) : tracked ∈ typing.visible := by
  let env := lowerEnv typing.mod typing.vars results
  rcases Fragment.store_emission_shape member same with assignment | operation | rebind
  · obtain ⟨loop, place, expression, sourceOrigin, rfl, originEq⟩ := assignment
    obtain ⟨scope, output, start, finish, active, source⟩ := typed.statement_typing
    let addressed := lowerPlace place env before
    let lowered := lowerExpr expression env addressed.2
    obtain ⟨identity, live⟩ := effectEmission_eq member
    have equal : addressed.1 = address ∧ lowered.1 = value ∧ some sourceOrigin = origin := by
      simpa only [identity, Emission.instruction, Inst.eff.injEq, Effect.store.injEq] using same
    rw [← equal.1] at upper
    rw [← equal.2.1] at reference
    exact False.elim (assignment_store_tracked_local_impossible facts tables source generated native continuation live reference upper)
  · obtain ⟨loop, operation, place, expression, sourceOrigin, rfl, originEq⟩ := operation
    let addressed := lowerPlace place env before
    let loaded := emitDef (.load addressed.1) env addressed.2
    let lowered := lowerExpr expression env loaded.2
    obtain ⟨integer, integerAt⟩ := integer_type_state loaded.1 env lowered.2
    let combined := emitDef (.bin operation integer loaded.1 lowered.1 (some sourceOrigin)) env lowered.2
    have member' : event ∈ effectEmission env combined.2 (.store addressed.1 combined.1 (some sourceOrigin)) := by
      change event ∈ effectEmission env
        (emitDef (.bin operation (intTyOf loaded.1 env lowered.2).1 loaded.1 lowered.1 (some sourceOrigin))
          env (intTyOf loaded.1 env lowered.2).2).2
        (.store addressed.1
          (emitDef (.bin operation (intTyOf loaded.1 env lowered.2).1 loaded.1 lowered.1 (some sourceOrigin))
            env (intTyOf loaded.1 env lowered.2).2).1 (some sourceOrigin)) at member
      rw [integerAt] at member
      exact member
    obtain ⟨identity, live⟩ := effectEmission_eq member'
    have equal : addressed.1 = address ∧ combined.1 = value ∧ some sourceOrigin = origin := by
      simpa only [identity, Emission.instruction, Inst.eff.injEq, Effect.store.injEq] using same
    have addressedGenerated : GeneratedBuilderState addressed.2 := generated.lowerPlace place (env := env) rfl
    have loadedGenerated : GeneratedBuilderState loaded.2 := addressedGenerated.emitDef (.load addressed.1) (env := env) rfl
    have loweredGenerated : GeneratedBuilderState lowered.2 := loadedGenerated.lowerExpr expression (env := env) rfl
    have whole := lowerStmt_assignOp_after_rhs (op := operation) (org := sourceOrigin) loop
      (rfl : lowerPlace place env before = addressed)
      (rfl : emitDef (.load addressed.1) env addressed.2 = loaded)
      (rfl : lowerExpr expression env loaded.2 = lowered) integerAt
    have continuation' : NativeBuilderContinuation facts.func
        (emitEffect (.store addressed.1 combined.1 (some sourceOrigin)) env combined.2).2 := by
      change NativeBuilderContinuation facts.func (lowerStmt loop (.assignOp operation place expression sourceOrigin) env before).2 at continuation
      rw [whole] at continuation
      exact continuation
    have combinedContinuation : NativeBuilderContinuation facts.func combined.2 :=
      continuation'.of_advance (advB_emitEffect (.store addressed.1 combined.1 (some sourceOrigin)) env combined.2 _ _ rfl)
    have scalar := emitted_binary_nonref facts loweredGenerated.live (rfl : emitDef _ env lowered.2 = combined) live combinedContinuation
    change valRefLike facts.types combined.1 = false at scalar
    rw [equal.2.1, reference] at scalar
    cases scalar
  · obtain ⟨loop, slot, expression, sourceOrigin, rfl, originEq⟩ := rebind
    obtain ⟨scope, output, start, finish, active, source⟩ := typed.statement_typing
    let lowered := lowerExpr expression env before
    let coerced := coerceSlot slot lowered.1 sourceOrigin env lowered.2
    let addressed := emitDef (.slotAddr slot) env coerced.2
    obtain ⟨identity, live⟩ := effectEmission_eq member
    have equal : addressed.1 = address ∧ coerced.1 = value ∧ some sourceOrigin = origin := by
      simpa only [identity, Emission.instruction, Inst.eff.injEq, Effect.store.injEq] using same
    rw [← equal.1] at upper
    exact rebind_store_tracked_visible facts source generated continuation live upper

#print axioms store_emission_tracked_visible

end Goose.Lower.Validation.SourceReplacementLexicalWriters
