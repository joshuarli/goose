import Goose.Lower.Validation.ReplacementCurrentRegion
import Goose.Lower.Validation.ReplacementOwnerSource
import Goose.Lower.Validation.FreshRunReconstructed

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem checkReplace_of_source_current {expr : Expr} {env : Core.TEnv} {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env expr start = .ok (ty, finish)) (shape : IndependentOwnerShape expr)
    (fresh : expr.freshOwner = true) (ownerResult : isLiteralRunType ty = true)
    {results : List Ty} {before cleared captured after : LS} {value owner : ValueId}
    {origin clearOrigin : Option OriginId}
    (clearRun : emitEffect (.clear owner clearOrigin) (lowerEnv env.mod env.vars results) before = ((), cleared))
    (run : lowerExpr expr (lowerEnv env.mod env.vars results) cleared = (value, captured))
    (live : LiveBound before) (generated : GeneratedBuilderState cleared)
    {loop : Option LoopCtx} {module : GIR.Module} {func : Func}
    (frames : LoopBuilderFrames loop cleared) (framed : TermEdgesFramed loop captured after)
    (extension : captured.Ext after) (closed : ∀ body ∈ after.blocks.toList, ClosedBlock body)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initState after)
    (blocks : func.blocks = finishBlocks after.blocks)
    (slots : func.slots = (lowerEnv env.mod env.vars results).slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = (lowerEnv env.mod env.vars results).globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = (lowerEnv env.mod env.vars results).sigs)
    (structs : module.structs = env.mod.structs) (profile : module.profile = env.mod.profile)
    (graphs : MutableSnapshotGraphs module func after)
    {queries : ReplacementQueries} {index : BlockId} {body : BlockB}
    (current : captured.cur = some index) (row : captured.blocks[index]? = some body)
    (ownerType : ∃ element, ownerTy (func.valueTypes module) owner = some (.grow element) ∨
      ownerTy (func.valueTypes module) owner = some (.growshrink element)) (label : String) :
    checkReplace module func (func.valueTypes module) queries (freshRuns func (func.valueTypes module)) label
      (transferEmptyBlock module (func.valueTypes module) queries
        (ReplacementRegionFacts cleared captured owner index) (cfgBlock body))
      (.eff (.replace owner value origin)) = .ok () := by
  have emitted := lowerExpr_owner_shape_apart (queries := queries) (owner := owner)
    builder blocks slots globals sigs structs profile graphs source shape run extension
  have valid := lowerExpr_freshOwner_reconstructed source fresh ownerResult run
    (by simp [current]) generated frames framed extension closed builder blocks
    (dense_finishBlocks builder.checkpoint.dense blocks) slots globals sigs structs profile graphs
  exact checkReplace_after_independent_rhs live clearRun emitted
    (advB_lowerExpr expr _ _ _ _ run) current row ownerType valid label

end Goose.Lower.Validation
