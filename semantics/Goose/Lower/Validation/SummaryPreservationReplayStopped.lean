import Goose.Lower.Validation.SummaryPreservationReplayBuilder
import Goose.Lower.Validation.SummaryPreservationStoppedGraph

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls final : LS} {upper : Prov}

theorem stopped {action : B α} {result : α}
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (stable : StoppedGraph action) (dead : ls.cur = none)
    (run : action le ls = (result, final)) :
    ReplayBuilder module results vt func target le scopeCount slots final upper := by
  obtain ⟨afterDead, blocks, values, recipes⟩ := stable le ls result final run dead
  have instructions : final.insts = ls.insts := by simp only [LS.insts, blocks]
  refine ⟨⟨ready.roots.valueSize.trans (congrArg Array.size values).symm, ?_⟩, ?_, ?_, ?_, ready.slotsEq, ready.recipes.same recipes⟩
  · intro inst member
    rw [instructions] at member
    simpa only [blocks] using ready.roots.instructions inst member
  · intro inst member
    exact ready.effects inst (instructions ▸ member)
  · constructor
    · simpa only [LS.DenseDefinitions, LS.defs, blocks, values] using ready.symbols.definitions
    · simpa only [instructions, values, blocks] using ready.symbols.instructions
  · intro block current
    rw [afterDead] at current
    cases current

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
