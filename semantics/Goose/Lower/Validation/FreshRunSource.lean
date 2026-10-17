import Goose.Lower.Validation.FreshRunFrames
import Goose.Lower.GeneratedBuilder
import Goose.Lower.Validation.DeadFrontier

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem emitted_definition_retained {env : LEnv} {before emitted after : LS}
    {op : Op} {value : ValueId} {block : BlockId}
    (current : before.cur = some block) (bounded : block < before.blocks.size)
    (run : emitDef op env before = (value, emitted)) (extension : emitted.Ext after)
    {func : Func} (blocks : func.blocks = finishBlocks after.blocks) :
    ∃ body ∈ func.blocks.toList, Inst.def value op ∈ body.insts := by
  let old := before.blocks[block]
  have oldAt : before.blocks[block]? = some old := by simp [old, bounded]
  rw [emitDef_run op env current] at run
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  have row : (before.blocks.modify block fun body =>
      { body with insts := body.insts.push (.def before.vals.size op) })[block]? =
      some { old with insts := old.insts.push (.def before.vals.size op) } := by
    simp [Array.getElem?_modify, oldAt]
  obtain ⟨body, bodyAt, _, extra, append⟩ := extension.2 block _ row
  refine ⟨cfgBlock body, ?_, ?_⟩
  · rw [blocks]
    apply Array.mem_toList_iff.mpr
    apply Array.mem_iff_getElem?.mpr
    exact ⟨block, by simp only [finishBlocks, cfgBlock, Array.getElem?_map, bodyAt, Option.map_some]⟩
  · change Inst.def before.vals.size op ∈ body.insts.toList
    rw [append]
    simp

theorem lowerExpr_arrLit_fresh {env : LEnv} {before emitted after : LS}
    {ty : Ty} {exprs : List Expr} {value : ValueId}
    (run : lowerExpr (.arrLit ty exprs) env before = (value, emitted))
    (live : emitted.cur.isSome = true) (generated : GeneratedBuilderState before)
    (extension : emitted.Ext after)
    {func : Func} {types : Array (Option VTy)} (blocks : func.blocks = finishBlocks after.blocks)
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues))
    (runType : isLiteralRunType ty = true) (typed : types[value]? = some (some (.data ty))) :
    FreshLiteralValue func types value := by
  simp only [lowerExpr] at run
  obtain ⟨values, middle, childrenRun, literalRun⟩ := bind_eq.mp run
  have middleLive := (dead_emitDef (.arrLit ty values)).live_before literalRun live
  have middleGenerated := generated.lowerExprs exprs childrenRun
  cases current : middle.cur with
  | none => simp [current] at middleLive
  | some block =>
    have blockBound := middleGenerated.live block current
    obtain ⟨body, bodyMember, definition⟩ := emitted_definition_retained current blockBound
      literalRun extension blocks
    apply FreshLiteralValue.literal bodyMember definition runType typed
    apply List.mem_range.mp
    apply dense.mem_iff.mp
    apply List.mem_flatMap.mpr
    refine ⟨body, bodyMember, ?_⟩
    simp only [GIR.Block.defs, List.mem_append, List.mem_filterMap]
    exact Or.inr ⟨.def value (.arrLit ty values), definition, rfl⟩

end Goose.Lower.Validation
