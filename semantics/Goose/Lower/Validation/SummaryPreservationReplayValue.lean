import Goose.Lower.Validation.SummaryPreservationReplayEmit

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

structure ReplayValue (func : Func) (upper : Prov) (ls : LS) (value : ValueId)
    (sourceRoots : List RootRef) (ty : VTy) : Prop where
  bound : value < ls.vals.size
  refined : RootsRefine func (rootsAt upper.vals value) sourceRoots
  scalar : ty.refLike = false → rootsAt upper.vals value = []

namespace ReplayBuilder

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem emitTypedDef (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (op : Op) (sourceRoots : List RootRef) (ty : VTy)
    (uses : ∀ value ∈ op.uses, value < ls.vals.size)
    (origin : ∀ candidate, op.origin = some candidate → candidate < le.mod.origins.size)
    (references : Op.SymbolRefsValid le op)
    (delta : EffectRefinement func (func.effectStep module vt upper {} (.def ls.vals.size op)) target)
    (roots : RootsRefine func (rootsOfDef results vt func upper ls.vals.size op) sourceRoots)
    (scalar : ty.refLike = false → rootsOfDef results vt func upper ls.vals.size op = []) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (Goose.Lower.emitDef op le ls).2 next ∧
      ((Goose.Lower.emitDef op le ls).2.cur.isSome = true →
        ReplayValue func next (Goose.Lower.emitDef op le ls).2 (Goose.Lower.emitDef op le ls).1 sourceRoots ty) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  obtain ⟨next, generated, value, retained⟩ := ready.emitDef op sourceRoots uses origin references delta roots
  refine ⟨next, generated, ?_, retained⟩
  intro live
  obtain ⟨bound, exactRoots, refined⟩ := value live
  exact ⟨bound, refined, fun nonref => exactRoots.trans (scalar nonref)⟩

end ReplayBuilder

end Goose.Lower.Validation.SummaryPreservation
