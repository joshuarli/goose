import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalContracts
import Goose.Lower.Validation.SourceReplacementWriterLedgerCanonicalTransport
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsConsumed
import Goose.Lower.Validation.SummaryPreservationReplayConversion
import Goose.Lower.Validation.ExpressionTypingScalarOps
import Goose.Lower.Validation.SourceSymbolRefs
import Goose.Lower.Validation.SourceRootShapeReads

namespace Goose.Lower.Validation.SourceReplacementWriterLedger

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation ReplacementContentFlowSource

variable {ownerRoot : Fragment} {ownerInitial baseline : LS}

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {initial : LS} {upper : Prov}

theorem canonical_globalExpressionOccurrence_conversion {operand : Expr} (kind : ConvKind) (destination : Ty) (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (child : CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets operand initial upper) :
    CanonicalGlobalExpressionOccurrenceReplayAt ownerRoot ownerInitial baseline typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.conv kind destination operand origin) initial upper := by
  intro rooted cursor type start finish before after roots typed replay ceiling ready sites targetBounds generated native metadata continuation
  have originBound : origin < env.mod.origins.size := by
    simpa only [← tables.moduleEq] using Core.tyExpr_conv_success_origin_bound typed
  obtain ⟨src, dst, childStart, childFinish, childTyped, rfl, rfl, _⟩ := tyExpr_conversion_child typed
  obtain ⟨childRoots, childAfter, childReplay, _⟩ := (st_bind_ok _ _ _ _).mp replay
  have exactReplay := rpExpr_conv_after_operand childReplay (kind := kind) (targetTy := .int dst) (origin := origin)
  rw [exactReplay] at replay
  cases replay
  have childEffect : EffectRefinement func childAfter.eff target := by
    cases kind with
    | widen | asUnchecked => exact ceiling
    | as => exact ⟨ceiling.reads, ceiling.writes, ceiling.grows, ceiling.shrinks, ceiling.rebinds,
        fun _ => ceiling.aborts rfl, ceiling.outputs, ceiling.unknown⟩
  let le := lowerEnv env.mod env.impl.vars returnTypes
  let lowered := lowerExpr operand le initial
  have tailTypes : TypeRun (do
      let integer ← intTyOf lowered.1
      Goose.Lower.emitDef (.conv kind integer dst lowered.1 (some origin))) :=
    TypeRun.bind (types_intTyOf _) fun _ => types_emitDef _
  have tailAdvance : AdvB (do
      let integer ← intTyOf lowered.1
      Goose.Lower.emitDef (.conv kind integer dst lowered.1 (some origin))) :=
    AdvB.bind (advB_intTyOf _) fun _ => advB_emitDef _
  have childNative := native.of_prefix (tailTypes le lowered.2 _ _ rfl)
  have childMetadata := metadata.of_advance (tailAdvance le lowered.2 _ _ rfl)
  have childContinuation := continuation.of_advance (tailAdvance le lowered.2 _ _ rfl)
  have childAtSite : ∃ path, DemandNodeAt siteRoot path (.expression operand) := by
    obtain ⟨path, atSite⟩ := rooted
    exact ⟨path ++ [0], atSite.snoc 0 (by simp [DemandNode.child?, DemandNode.children])⟩
  obtain ⟨middle, middleReady, middleValue, middleRoots, middleLedger, middleSites⟩ := child childAtSite
      (by obtain ⟨path,located⟩ := cursor; exact ⟨path ++ [0],located.child rfl⟩) (.int src) childStart childFinish before childAfter
    childRoots childTyped childReplay childEffect ready sites targetBounds generated childNative childMetadata childContinuation
  obtain ⟨next, nextReady, nextValue, nextRoots⟩ := middleReady.conversion childReplay exactReplay ceiling
    (initial := initial) rfl (Prod.ext rfl (intTyOf_state lowered.1 le lowered.2))
    (fun live => (middleValue live).bound) originBound
  have typeRun : intTyOf lowered.1 le lowered.2 = ((intTyOf lowered.1 le lowered.2).1, lowered.2) :=
    Prod.ext rfl (intTyOf_state lowered.1 le lowered.2)
  have whole : lowerExpr (.conv kind (.int dst) operand origin) le initial =
      Goose.Lower.emitDef (.conv kind (intTyOf lowered.1 le lowered.2).1 dst lowered.1 (some origin)) le lowered.2 := by
    simp only [lowerExpr, bind_run, show lowerExpr operand le initial = lowered from rfl]
    rw [typeRun]
  have childPath : DemandNodeAt (.expression (.conv kind (.int dst) operand origin)) [0] (.expression operand) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  refine ⟨next, nextReady, nextValue, ?_, ?_⟩
  · intro old bound
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, middleReady.roots.valueSize]
      exact (advB_lowerExpr operand le initial lowered.1 lowered.2 rfl).vals
    exact (nextRoots old (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots old bound)
  · apply (middleLedger.underRoot childPath).emitDef_canonicalSites middleSites middleReady nextReady (by rw [whole]) nextRoots
    · intro live value member
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
      subst value
      exact expression_operand_occurrence childPath childReplay middleReady (middleValue live)
    · intro address same; cases same
    · intro callee arguments org same; cases same
    · intro live value member mutability payload reference
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
      subst value
      have row := sourceExpressionNative tables childNative generated childTyped (rfl : lowerExpr operand le initial = lowered) live
      exact False.elim (nativeFlat_not_reference row (by rfl) mutability payload reference)

#print axioms canonical_globalExpressionOccurrence_conversion

end Goose.Lower.Validation.SourceReplacementWriterLedger
