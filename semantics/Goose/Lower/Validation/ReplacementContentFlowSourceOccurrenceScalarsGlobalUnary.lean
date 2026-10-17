import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceGlobalContracts
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsConsumed
import Goose.Lower.Validation.SummaryPreservationReplayUnary
import Goose.Lower.Validation.ScalarTyping
import Goose.Lower.Validation.SourceSymbolRefs
import Goose.Lower.Validation.SourceRootShapeReads

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.Core.Sound Goose.GIR SummaryPreservation

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {siteRoot : DemandNode} {siteTargets : List BlockId} {initial : LS} {upper : Prov}

private theorem before_aborts {func : Func} {before target : Core.Eff}
    (bound : EffectRefinement func { before with aborts := true } target) :
    EffectRefinement func before target :=
  ⟨bound.reads, bound.writes, bound.grows, bound.shrinks, bound.rebinds,
    fun _ => bound.aborts rfl, bound.outputs, bound.unknown⟩

theorem globalExpressionOccurrence_unary {operand : Expr} (op : UnOp) (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (child : GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets operand initial upper) :
    GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.un op operand origin) initial upper := by
  intro rooted type start finish before after sourceRoots source replayed wholeEffect ready sites targetBounds generated native metadata continuation
  let le := lowerEnv env.mod env.impl.vars returnTypes
  have originBound : origin < le.mod.origins.size := by
    simpa only [le, lowerEnv, ← tables.moduleEq] using Core.tyExpr_un_success_origin_bound source
  obtain ⟨childStart, childFinish, integer, typed, shape, _⟩ := tyExpr_un_child source
  subst type
  obtain ⟨roots, sourceAfter, operandReplay, _⟩ := (st_bind_ok _ _ _ _).mp replayed
  have exactReplay := rpExpr_un_after_operand operandReplay (op := op) (origin := origin)
  rw [exactReplay] at replayed
  cases replayed
  have childEffect : EffectRefinement func sourceAfter.eff target := by
    cases op with
    | neg => exact before_aborts wholeEffect
    | bitnot => exact wholeEffect
  let lowered := lowerExpr operand le initial
  have tailTypes : TypeRun (do
      let ty ← intTyOf lowered.1
      Goose.Lower.emitDef (.un op ty lowered.1 (some origin))) :=
    TypeRun.bind (types_intTyOf _) fun _ => types_emitDef _
  have tailAdvance : AdvB (do
      let ty ← intTyOf lowered.1
      Goose.Lower.emitDef (.un op ty lowered.1 (some origin))) :=
    AdvB.bind (advB_intTyOf _) fun _ => advB_emitDef _
  have childNative := native.of_prefix (tailTypes le lowered.2 _ _ rfl)
  have childMetadata := metadata.of_advance (tailAdvance le lowered.2 _ _ rfl)
  have childContinuation := continuation.of_advance (tailAdvance le lowered.2 _ _ rfl)
  have childAtSite : ∃ path, DemandNodeAt siteRoot path (.expression operand) := by
    obtain ⟨path, atSite⟩ := rooted
    exact ⟨path ++ [0], atSite.snoc 0 (by simp [DemandNode.child?, DemandNode.children])⟩
  obtain ⟨middle, middleReady, middleValue, middleRoots, middleLedger, middleSites⟩ :=
    child childAtSite (.int integer) childStart childFinish before sourceAfter roots typed operandReplay childEffect ready sites targetBounds generated childNative childMetadata childContinuation
  have typeRun : intTyOf lowered.1 le lowered.2 = ((intTyOf lowered.1 le lowered.2).1, lowered.2) :=
    Prod.ext rfl (intTyOf_state lowered.1 le lowered.2)
  obtain ⟨next, nextReady, nextValue, nextRoots⟩ := middleReady.unary operandReplay exactReplay wholeEffect
    (initial := initial) rfl typeRun (fun live => (middleValue live).bound) originBound
  have whole : lowerExpr (.un op operand origin) le initial =
      Goose.Lower.emitDef (.un op (intTyOf lowered.1 le lowered.2).1 lowered.1 (some origin)) le lowered.2 := by
    exact lowerExpr_un_after_operand rfl typeRun
  have childPath : DemandNodeAt (.expression (.un op operand origin)) [0] (.expression operand) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  refine ⟨next, nextReady, ?_, ?_, ?_⟩
  · intro live
    have value := nextValue live
    exact ⟨value.bound, value.refined, fun _ => value.scalar rfl⟩
  · intro index bound
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, middleReady.roots.valueSize]
      exact (advB_lowerExpr operand le initial lowered.1 lowered.2 rfl).vals
    exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)
  · apply (middleLedger.underRoot childPath).emitDef_sites middleSites middleReady nextReady (by rw [whole]) nextRoots
    · intro live value member
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
      subst value
      exact expression_operand_occurrence childPath operandReplay middleReady (middleValue live)
    · intro address same; cases same
    · intro callee arguments org same; cases same
    · intro live value member mutability payload reference
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
      subst value
      have row := sourceExpressionNative tables childNative generated typed (rfl : lowerExpr operand le initial = lowered) live
      exact False.elim (nativeFlat_not_reference row (by rfl) mutability payload reference)

theorem globalExpressionOccurrence_not {operand : Expr}
    (tables : SourceRootTables typingEnv env)
    (child : GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets operand initial upper) :
    GlobalExpressionOccurrenceReplayAt typingEnv env results vt func returnTypes slots target scopeCount siteRoot siteTargets (.not operand) initial upper := by
  intro rooted type start finish before after sourceRoots source replayed wholeEffect ready sites targetBounds generated native metadata continuation
  let le := lowerEnv env.mod env.impl.vars returnTypes
  obtain ⟨childFinish, typed, shape⟩ := tyExpr_not_child source
  subst type
  obtain ⟨roots, sourceAfter, operandReplay, tail⟩ := (st_bind_ok _ _ _ _).mp replayed
  have afterEq : after = sourceAfter := congrArg Prod.snd ((st_pure_ok _ _ _).mp tail)
  subst after
  let lowered := lowerExpr operand le initial
  have childNative := native.of_prefix (types_emitDef (.boolNot lowered.1) le lowered.2 _ _ rfl)
  have childMetadata := metadata.of_advance (advB_emitDef (.boolNot lowered.1) le lowered.2 _ _ rfl)
  have childContinuation := continuation.of_advance (advB_emitDef (.boolNot lowered.1) le lowered.2 _ _ rfl)
  have childAtSite : ∃ path, DemandNodeAt siteRoot path (.expression operand) := by
    obtain ⟨path, atSite⟩ := rooted
    exact ⟨path ++ [0], atSite.snoc 0 (by simp [DemandNode.child?, DemandNode.children])⟩
  obtain ⟨middle, middleReady, middleValue, middleRoots, middleLedger, middleSites⟩ :=
    child childAtSite .bool start childFinish before sourceAfter roots typed operandReplay wholeEffect ready sites targetBounds generated childNative childMetadata childContinuation
  obtain ⟨next, nextReady, nextValue, nextRoots⟩ := middleReady.logicalNot operandReplay
    (show rpExpr env (.not operand) before = .ok (sourceRoots, sourceAfter) from by
      simpa only [rpExpr, operandReplay, bind, pure, Except.bind, Except.pure, StateT.bind, StateT.pure] using tail)
    (initial := initial) rfl (fun live => (middleValue live).bound)
  have childPath : DemandNodeAt (.expression (.not operand)) [0] (.expression operand) :=
    .child (by simp [DemandNode.child?, DemandNode.children]) (.here _)
  refine ⟨next, nextReady, nextValue, ?_, ?_⟩
  · intro index bound
    have growth : upper.vals.size ≤ middle.vals.size := by
      rw [ready.roots.valueSize, middleReady.roots.valueSize]
      exact (advB_lowerExpr operand le initial lowered.1 lowered.2 rfl).vals
    exact (nextRoots index (Nat.lt_of_lt_of_le bound growth)).trans (middleRoots index bound)
  · apply (middleLedger.underRoot childPath).emitDef_sites middleSites middleReady nextReady rfl nextRoots
    · intro live value member
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
      subst value
      exact expression_operand_occurrence childPath operandReplay middleReady (middleValue live)
    · intro address same; cases same
    · intro callee arguments org same; cases same
    · intro live value member mutability payload reference
      simp only [GIR.ReplacementContentFlow.Model.accessOperands, Inst.uses, Op.uses, List.mem_singleton] at member
      subst value
      have row := sourceExpressionNative tables childNative generated typed (rfl : lowerExpr operand le initial = lowered) live
      exact False.elim (nativeFlat_not_reference row (by rfl) mutability payload reference)

#print axioms globalExpressionOccurrence_unary
#print axioms globalExpressionOccurrence_not

end Goose.Lower.Validation.ReplacementContentFlowSource
