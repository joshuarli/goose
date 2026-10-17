import Goose.Lower.Validation.ReplacementSourceTyping
import Goose.Lower.Validation.FreshRunReconstructed

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem assignWhole_freshRuns_reconstructed {env output : Core.TEnv} {place : Place} {expr : Expr}
    {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assignWhole place expr origin) start = .ok (output, finish))
    {results : List Ty} {before captured after : LS} {value : ValueId}
    (run : lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, captured))
    (live : captured.cur.isSome = true) (generated : GeneratedBuilderState before)
    {loop : Option LoopCtx} {module : GIR.Module} {func : Func}
    (frames : LoopBuilderFrames loop before) (framed : TermEdgesFramed loop captured after)
    (extension : captured.Ext after) (closed : ∀ body ∈ after.blocks.toList, ClosedBlock body)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initState after)
    (blocks : func.blocks = finishBlocks after.blocks)
    (slots : func.slots = (lowerEnv env.mod env.vars results).slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = (lowerEnv env.mod env.vars results).globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = (lowerEnv env.mod env.vars results).sigs)
    (structs : module.structs = env.mod.structs) (profile : module.profile = env.mod.profile)
    (graphs : MutableSnapshotGraphs module func after) :
    (freshRuns func (func.valueTypes module))[value]? = some true := by
  obtain ⟨info, element, childStart, _, ownerShape, childSource, _, _, _⟩ := tyStmt_assignWhole_children source
  have ownerResult : isLiteralRunType info.ty = true := by
    rcases ownerShape with grow | growshrink <;> simp_all [isLiteralRunType]
  exact lowerExpr_freshOwner_reconstructed childSource (tyStmt_assignWhole_fresh source) ownerResult run
    live generated frames framed extension closed builder blocks (dense_finishBlocks builder.checkpoint.dense blocks)
    slots globals sigs structs profile graphs

end Goose.Lower.Validation
