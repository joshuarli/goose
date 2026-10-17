import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceSites
import Goose.Lower.Validation.SummaryPreservationReplayEntry

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

theorem entryReplayState_emitsOnly (property : Inst → Prop) (types : List VTy) (le : LEnv) :
    EmitsOnly property initState (entryReplayState types le) := by
  apply (EmitsOnly.newBlock initState ((paramIds types #[]).zip types)).trans
  exact EmitsOnly.of_blocks rfl

theorem entryReplayState_occurrenceSites (env : PEnv) (root : DemandNode) (targets : List BlockId)
    (types : List VTy) (le : LEnv) (func : Func) (native : Array (Option VTy)) (upper : Prov) :
    OccurrenceSitesBuilder env root targets le (entryReplayState types le) func native upper := by
  intro block body row position inst lookup
  have member : inst ∈ (entryReplayState types le).insts :=
    List.mem_flatMap.mpr ⟨body, Array.mem_toList_iff.mpr (Array.mem_of_getElem? row),
      Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup)⟩
  rw [entryReplayState_instructions] at member
  cases member

#print axioms entryReplayState_emitsOnly
#print axioms entryReplayState_occurrenceSites

end Goose.Lower.Validation.ReplacementContentFlowSource
