import Goose.Lower.Validation.FreshRunSourceBuilder
import Goose.Lower.Validation.ValueTypeReconstructionLiteralRows

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lowerExpr_freshOwner_reconstructed {expr : Expr} {env : Core.TEnv} {ty : Ty} {start finish : Nat}
    (source : Core.tyExpr env expr start = .ok (ty, finish)) (fresh : expr.freshOwner = true)
    (owner : isLiteralRunType ty = true) {results : List Ty} {before captured after : LS} {value : ValueId}
    (run : lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, captured))
    (live : captured.cur.isSome = true) (generated : GeneratedBuilderState before)
    {module : GIR.Module} {func : Func}
    (framed : IntervalEdgesFramed before captured after)
    (extension : captured.Ext after) (closed : ∀ body ∈ after.blocks.toList, ClosedBlock body)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initState after)
    (blocks : func.blocks = finishBlocks after.blocks)
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues))
    (slots : func.slots = (lowerEnv env.mod env.vars results).slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = (lowerEnv env.mod env.vars results).globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = (lowerEnv env.mod env.vars results).sigs)
    (structs : module.structs = env.mod.structs) (profile : module.profile = env.mod.profile)
    (graphs : MutableSnapshotGraphs module func after) :
    (freshRuns func (func.valueTypes module))[value]? = some true :=
  lowerExpr_freshOwner_freshRuns source fresh owner run live generated framed extension closed blocks dense
    (ownerLiteralRows_of_source_graphs builder blocks slots globals sigs structs profile graphs)

theorem lowerBlock_freshOwner_reconstructed {body : Core.Block} {env : Core.TEnv} {ty : Ty} {start finish : Nat}
    (source : Core.tyBlock env [] body start = .ok (ty, finish)) (fresh : body.freshOwner = true)
    (owner : isLiteralRunType ty = true) {results : List Ty} {before captured after : LS} {value : ValueId}
    (run : lowerBlock none [] true body (lowerEnv env.mod env.vars results) before = (value, captured))
    (live : captured.cur.isSome = true) (generated : GeneratedBuilderState before)
    {module : GIR.Module} {func : Func}
    (framed : IntervalEdgesFramed before captured after)
    (extension : captured.Ext after) (closed : ∀ body ∈ after.blocks.toList, ClosedBlock body)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initState after)
    (blocks : func.blocks = finishBlocks after.blocks)
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues))
    (slots : func.slots = (lowerEnv env.mod env.vars results).slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = (lowerEnv env.mod env.vars results).globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = (lowerEnv env.mod env.vars results).sigs)
    (structs : module.structs = env.mod.structs) (profile : module.profile = env.mod.profile)
    (graphs : MutableSnapshotGraphs module func after) :
    (freshRuns func (func.valueTypes module))[value]? = some true :=
  lowerBlock_freshOwner_freshRuns source fresh owner run live generated framed extension closed blocks dense
    (ownerLiteralRows_of_source_graphs builder blocks slots globals sigs structs profile graphs)

end Goose.Lower.Validation
