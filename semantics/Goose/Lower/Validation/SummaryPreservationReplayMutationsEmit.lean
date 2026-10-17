import Goose.Lower.Validation.SummaryPreservationReplayLiveEmit

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem emitEffect_live (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (effect : Effect)
    (symbols : ls.cur.isSome = true → Inst.SymbolsWithin le scopeCount ls.vals.size ls.blocks.size (.eff effect))
    (roots : ls.cur.isSome = true →
      InstructionRootsClosed results vt { func with blocks := finishBlocks ls.blocks } upper (.eff effect))
    (delta : ls.cur.isSome = true →
      EffectRefinement func (func.effectStep module vt upper {} (.eff effect)) target) :
    ReplayBuilder module results vt func target le scopeCount slots (Goose.Lower.emitEffect effect le ls).2 upper := by
  cases current : ls.cur with
  | none => rw [emitEffect_none _ _ current]; exact ready
  | some block =>
    have live : ls.cur.isSome = true := by simp [current]
    exact ready.emitEffect effect (symbols live) (roots live) (delta live)

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
