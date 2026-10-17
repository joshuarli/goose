import Goose.Lower.Validation.SummaryPreservationEntrySeeds
import Goose.Lower.Validation.CfgBuilderFunctions
import Goose.Lower.Frag

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem cfg_global_entry_parameters (module : Core.Module) (global : Core.Global) :
    ∀ block, (lowerGlobal module global).init.blocks[0]? = some block → block.params = [] := by
  let le := lowerEnv module #[] [global.ty]
  let entry := entryReplayState [] le
  let value := lowerExpr global.init le entry
  have whole : cfg_globalState module global =
      (Goose.Lower.emitTerm (.ret [value.1] (some global.org)) le value.2).2 := by
    simp only [cfg_globalState, cfg_globalAction, bind_run, setCur_run,
      value, entry, entryReplayState, le]
  have advance := (advB_lowerExpr global.init le entry _ _ rfl).ext.trans
    (advB_emitTerm (.ret [value.1] (some global.org)) le value.2 _ _ rfl).ext
  have initialRow : entry.blocks[0]? = some ({params := [], insts := #[]} : BlockB) := by
    simp [entry, entryReplayState, newBlock_run_general, initState, paramIds]
  obtain ⟨finished, finalRow, same, _⟩ := advance.2 0 _ initialRow
  have emittedRow : (Goose.Lower.emitTerm (.ret [value.1] (some global.org)) le value.2).2.blocks[0]? = some finished := finalRow
  intro block row
  rw [cfg_global_blocks, whole] at row
  simp only [finishBlocks, Array.getElem?_map, emittedRow, Option.map_some, Option.some.injEq] at row
  cases row
  exact same

theorem global_provenance_seed (module : Core.Module) (global : Core.Global)
    (vt : Array (Option VTy)) (upper : Prov) :
    ProvenanceBelow (provStart vt (lowerGlobal module global).init) upper := by
  apply provStart_below_of_entry_seeds
  intro block row pair member reference
  rw [cfg_global_entry_parameters module global block row] at member
  cases member

#print axioms cfg_global_entry_parameters
#print axioms global_provenance_seed

end Goose.Lower.Validation.SummaryPreservation
