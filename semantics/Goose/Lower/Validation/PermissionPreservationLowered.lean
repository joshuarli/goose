import Goose.Lower.Validation.PermissionPreservationFinal

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem checkPermissions_lowered_function {module : Core.Module} {vars : Array LocalVar}
    {results : List Ty} {state : LS} {func : Func}
    (blocks : func.blocks = finishBlocks state.blocks)
    (slots : func.slots = (lowerEnv module vars results).slots)
    (rules : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      PermissionRule (lower module) func state.vals
        (WritableEvidence (lowerEnv module vars results) state)
        (ContentsEvidence (lowerEnv module vars results) state) instruction) (label : String) :
    checkPermissions (lower module) label func state.vals = .ok () := by
  apply checkPermissions_of_lowered_evidence (le := lowerEnv module vars results)
    (state := state) (func := func) (module := lower module) ?_ slots.symm ?_ rfl rules label
  · exact blocks.symm
  · simp only [lowerEnv, lower, Array.map_map]
    rfl

#print axioms checkPermissions_lowered_function

end Goose.Lower.Validation
