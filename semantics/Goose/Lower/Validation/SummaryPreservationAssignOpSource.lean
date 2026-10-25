import Goose.Lower.Validation.SummaryPreservationAssignSource
import Goose.Lower.Validation.SummaryPreservationScalarSource

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rpStmt_assignOp_after_operands {env : PEnv} {op : BinOp}
    {place : Place} {expression : Expr} {org : OriginId}
    {placeRoots valueRoots : List RootRef} {initial placeState before : RState}
    (placeReplay : rpPlace env place initial = .ok (placeRoots, placeState))
    (valueReplay : rpExpr env expression placeState = .ok (valueRoots, before)) :
    rpStmt env (.assignOp op place expression org) initial =
      .ok ((), { before with eff := {
        before.eff with
        reads := addTargets before.eff.reads (rootsTargets placeRoots)
        writes := addTargets before.eff.writes (rootsTargets placeRoots)
        aborts := if op.mayAbort then true else before.eff.aborts } }) := by
  cases aborts : op.mayAbort <;>
    simp [rpStmt, placeReplay, valueReplay, addReads, addWrites, addRoots, aborts,
      bind, pure, noteAborts, modify, Except.bind, Except.pure, StateT.modifyGet,
      StateT.bind, StateT.pure, modifyGet, MonadStateOf.modifyGet] <;> rfl

theorem effectRefinement_assignOp_reads {func : Func} {source : Core.Eff}
    {roots : List RootRef} {op : BinOp} :
    EffectRefinement func { source with reads := addTargets source.reads (rootsTargets roots) }
      { source with
        reads := addTargets source.reads (rootsTargets roots)
        writes := addTargets source.writes (rootsTargets roots)
        aborts := if op.mayAbort then true else source.aborts } := by
  refine ⟨fun _ h => h, storageTargets_mono (fun t h => addTargets_left _ _ t h),
    fun _ h => h, fun _ h => h, fun _ h => h, ?_, fun h => h, fun h => h⟩
  intro h
  cases op.mayAbort <;> simp_all

theorem effectRefinement_assignOp_writes {func : Func} {source : Core.Eff}
    {roots : List RootRef} {op : BinOp} :
    EffectRefinement func { source with writes := addTargets source.writes (rootsTargets roots) }
      { source with
        reads := addTargets source.reads (rootsTargets roots)
        writes := addTargets source.writes (rootsTargets roots)
        aborts := if op.mayAbort then true else source.aborts } := by
  refine ⟨storageTargets_mono (fun t h => addTargets_left _ _ t h), fun _ h => h,
    fun _ h => h, fun _ h => h, fun _ h => h, ?_, fun h => h, fun h => h⟩
  intro h
  cases op.mayAbort <;> simp_all

theorem effectRefinement_assignOp_bin {func : Func} {source : Core.Eff}
    {roots : List RootRef} {op : BinOp} :
    EffectRefinement func (if op.mayAbort then { source with aborts := true } else source)
      { source with
        reads := addTargets source.reads (rootsTargets roots)
        writes := addTargets source.writes (rootsTargets roots)
        aborts := if op.mayAbort then true else source.aborts } := by
  cases op.mayAbort <;>
    exact ⟨storageTargets_mono (fun t h => addTargets_left _ _ t h),
      storageTargets_mono (fun t h => addTargets_left _ _ t h), fun _ h => h,
      fun _ h => h, fun _ h => h, fun h => h, fun h => h, fun h => h⟩

end Goose.Lower.Validation.SummaryPreservation
