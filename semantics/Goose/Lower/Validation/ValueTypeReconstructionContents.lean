import Goose.Lower.Validation.ValueTypeReconstructionEmitted
import Goose.Lower.Validation.ExpressionTypingContentsEvidence

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem contentsEvidence_final_graph
    {le : LEnv} {before after : LS} {owner : ValueId} {loop : Option LoopCtx}
    {module : GIR.Module} {func : Func}
    (evidence : ContentsEvidence le before owner)
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (types : EmittedTypePrefix before after)
    (frames : LoopBuilderFrames loop before) (framed : TermEdgesFramed loop before after)
    (slots : le.slots = func.slots) (blocks : func.blocks = finishBlocks after.blocks)
    (globals : module.globals.map (·.kind) = le.globals.map (·.2))
    (structs : module.structs = le.mod.structs) :
    ∃ authorized, ContentsClosed (module.globals.map (·.kind)) module.structs
      func after.vals authorized ∧ authorized owner ∧
      ∀ value, authorized value → value < before.vals.size := by
  obtain ⟨authorized, closed, noninteger, member⟩ := evidence
  have bounded : ∀ value, authorized value → value < before.vals.size := by
    intro value allowed
    simpa only [permissionFunc_numValues beforeDense le] using closed.bounded value allowed
  have preserved := closed.ext beforeDense afterDense extension types.size types.typed frames framed noninteger
  have finished := preserved.replace_function slots (show (permissionFunc le after).blocks = func.blocks from blocks.symm)
  refine ⟨authorized, ?_, member, bounded⟩
  simpa only [globals, structs] using finished

theorem snapshotAuthorityRetained_of_contents_frame
    {le : LEnv} {before after : LS} {owner : ValueId} {loop : Option LoopCtx}
    {module : GIR.Module} {func : Func}
    (evidence : ContentsEvidence le before owner)
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (types : EmittedTypePrefix before after)
    (frames : LoopBuilderFrames loop before) (framed : TermEdgesFramed loop before after)
    (slots : le.slots = func.slots) (blocks : func.blocks = finishBlocks after.blocks)
    (globals : module.globals.map (·.kind) = le.globals.map (·.2))
    (structs : module.structs = le.mod.structs) :
    SnapshotAuthorityRetained before module func owner := by
  obtain ⟨authorized, closed, member, bounded⟩ := contentsEvidence_final_graph evidence
    beforeDense afterDense extension types frames framed slots blocks globals structs
  exact snapshotAuthorityRetained_of_graph closed bounded
    (fun value allowed => types.lookup value (bounded value allowed)) member

theorem MutableSnapshotGraphs.replace_function
    {module : GIR.Module} {before after : Func} {state : LS}
    (graphs : MutableSnapshotGraphs module before state)
    (slots : before.slots = after.slots) (blocks : before.blocks = after.blocks) :
    MutableSnapshotGraphs module after state := by
  intro value mode owner definition element expected
  obtain ⟨authorized, closed, member, bounded⟩ := graphs value mode owner definition element expected
  exact ⟨authorized, closed.replace_function slots blocks, member, bounded⟩

end Goose.Lower.Validation
