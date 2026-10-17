import Goose.Lower.Validation.SummaryPreservationReplayBuilder
import Goose.Lower.Validation.SummaryPreservationDefFrame

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem emitDef (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (op : Op) (sourceRoots : List RootRef)
    (uses : ∀ value ∈ op.uses, value < ls.vals.size)
    (origin : ∀ candidate, op.origin = some candidate → candidate < le.mod.origins.size)
    (references : Op.SymbolRefsValid le op)
    (delta : EffectRefinement func (func.effectStep module vt upper {} (.def ls.vals.size op)) target)
    (roots : RootsRefine func (rootsOfDef results vt func upper ls.vals.size op) sourceRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (Goose.Lower.emitDef op le ls).2 next ∧
      ((Goose.Lower.emitDef op le ls).2.cur.isSome = true →
        (Goose.Lower.emitDef op le ls).1 < (Goose.Lower.emitDef op le ls).2.vals.size ∧
        rootsAt next.vals (Goose.Lower.emitDef op le ls).1 =
          rootsOfDef results vt func upper ls.vals.size op ∧
        RootsRefine func (rootsAt next.vals (Goose.Lower.emitDef op le ls).1) sourceRoots) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases current : ls.cur with
  | none =>
    rw [emitDef_none _ _ current]
    exact ⟨upper, ready, by simp [current], fun _ _ => rfl⟩
  | some block =>
    obtain ⟨next, nextRoots, effects, returned, nextSlots, symbols, nextCurrent,
      blockBound, valueBound, growth⟩ := emitDef_refined_frame_growth op ready.symbols current
        (ready.current block current) ready.roots ready.effects uses origin references delta
    refine ⟨next, ⟨nextRoots, effects, symbols, ?_, nextSlots.trans ready.slotsEq⟩, ?_, growth⟩
    · intro candidate candidateRow
      rw [nextCurrent] at candidateRow
      cases candidateRow
      exact blockBound
    · intro _
      refine ⟨valueBound, ?_, ?_⟩
      · simpa only [emitDef_run op le current] using returned
      rw [returned]
      simpa only [emitDef_run op le current] using roots

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
