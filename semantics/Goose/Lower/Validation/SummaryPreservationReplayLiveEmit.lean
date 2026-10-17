import Goose.Lower.Validation.SummaryPreservationReplayValue
import Goose.Lower.Validation.SummaryPreservationReplayStopped

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem emitTypedDef_live (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (op : Op) (sourceRoots : List RootRef) (ty : VTy)
    (uses : ls.cur.isSome = true → ∀ value ∈ op.uses, value < ls.vals.size)
    (origin : ∀ candidate, op.origin = some candidate → candidate < le.mod.origins.size)
    (references : Op.SymbolRefsValid le op)
    (delta : ls.cur.isSome = true →
      EffectRefinement func (func.effectStep module vt upper {} (.def ls.vals.size op)) target)
    (roots : ls.cur.isSome = true →
      RootsRefine func (rootsOfDef results vt func upper ls.vals.size op) sourceRoots)
    (scalar : ls.cur.isSome = true → ty.refLike = false → rootsOfDef results vt func upper ls.vals.size op = []) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (Goose.Lower.emitDef op le ls).2 next ∧
      ((Goose.Lower.emitDef op le ls).2.cur.isSome = true →
        ReplayValue func next (Goose.Lower.emitDef op le ls).2 (Goose.Lower.emitDef op le ls).1 sourceRoots ty) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases current : ls.cur with
  | none =>
    have generated : ReplayBuilder module results vt func target le scopeCount slots
        (Goose.Lower.emitDef op le ls).2 upper := ready.stopped (stopped_emitDef op) current rfl
    rw [emitDef_none _ _ current] at generated ⊢
    exact ⟨upper, generated, by simp [current], fun _ _ => rfl⟩
  | some block =>
    have live : ls.cur.isSome = true := by simp [current]
    exact ready.emitTypedDef op sourceRoots ty (uses live) origin references (delta live) (roots live) (scalar live)

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
