import Goose.Lower.Validation.ReplacementSourceCurrent
import Goose.Lower.Validation.ExpressionTyping
import Goose.Lower.Validation.SourceStatementTypingStorage

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem checkReplace_of_source_assignWhole
    {env output : Core.TEnv} {place : Place} {expr : Expr} {origin : OriginId} {scope start finish : Nat}
    (source : Core.tyStmt env scope (.assignWhole place expr origin) start = .ok (output, finish))
    (shape : IndependentOwnerShape expr) (placeSupported : StaticPlace place)
    {results : List Ty} {initial addressed cleared captured after : LS} {owner value : ValueId}
    (ownerRun : lowerPlace place (lowerEnv env.mod env.vars results) initial = (owner, addressed))
    (clearRun : emitEffect (.clear owner (some origin)) (lowerEnv env.mod env.vars results) addressed = ((), cleared))
    (run : lowerExpr expr (lowerEnv env.mod env.vars results) cleared = (value, captured))
    (live : LiveBound addressed) (generated : GeneratedBuilderState cleared)
    {loop : Option LoopCtx} {module : GIR.Module} {func : Func}
    (frames : LoopBuilderFrames loop cleared) (framed : TermEdgesFramed loop captured after)
    (extension : captured.Ext after) (closed : ∀ body ∈ after.blocks.toList, ClosedBlock body)
    (builder : EmittedBuilder (lowerEnv env.mod env.vars results) initState after)
    (blocks : func.blocks = finishBlocks after.blocks)
    (slots : func.slots = (lowerEnv env.mod env.vars results).slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = (lowerEnv env.mod env.vars results).globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = (lowerEnv env.mod env.vars results).sigs)
    (structs : module.structs = env.mod.structs) (profile : module.profile = env.mod.profile)
    (graphs : MutableSnapshotGraphs module func after) (typePrefix : EmittedTypePrefix addressed after)
    {queries : ReplacementQueries} {index : BlockId} {body : BlockB}
    (current : captured.cur = some index) (row : captured.blocks[index]? = some body) (label : String) :
    checkReplace module func (func.valueTypes module) queries (freshRuns func (func.valueTypes module)) label
      (transferEmptyBlock module (func.valueTypes module) queries
        (ReplacementRegionFacts cleared captured owner index) (cfgBlock body))
      (.eff (.replace owner value (some origin))) = .ok () := by
  obtain ⟨info, element, childStart, placeSource, ownerShape, childSource, _, _, _⟩ :=
    tyStmt_assignWhole_children source
  have capturedLive : captured.cur.isSome = true := by simp [current]
  have clearedLive := (dead_lowerExpr expr).live_before run capturedLive
  have addressedLive := (dead_emitEffect (.clear owner (some origin))).live_before clearRun clearedLive
  obtain ⟨mode, ownerRow⟩ := lowerPlace_static_live_typed placeSupported placeSource ownerRun addressedLive
  have finalRow := typePrefix.typed owner (.data (.ref mode info.ty)) ownerRow
  have retained := valueTypes_eq_retained_of_source_graphs builder blocks slots globals sigs structs profile graphs
  have ownerType : ∃ element, ownerTy (func.valueTypes module) owner = some (.grow element) ∨
      ownerTy (func.valueTypes module) owner = some (.growshrink element) := by
    refine ⟨element, ?_⟩
    rcases ownerShape with grow | growshrink
    · exact Or.inl (by simp [ownerTy, retained, finalRow, grow])
    · exact Or.inr (by simp [ownerTy, retained, finalRow, growshrink])
  have ownerResult : isLiteralRunType info.ty = true := by
    rcases ownerShape with grow | growshrink <;> simp_all [isLiteralRunType]
  exact checkReplace_of_source_current childSource shape shape.fresh ownerResult clearRun run live generated
    frames framed extension closed builder blocks slots globals sigs structs profile graphs current row ownerType label

end Goose.Lower.Validation
