import Goose.Lower.Validation.ReplacementReconstructed
import Goose.Lower.Validation.ReplacementEmission
import Goose.Lower.Validation.FreshRunSource

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem emitsOnly_scalar_of_source_graphs
    {module : GIR.Module} {func : Func} {le env : LEnv} {state before captured : LS}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks)
    (slots : func.slots = le.slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = le.globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = le.sigs)
    (structs : module.structs = le.mod.structs)
    (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state)
    {queries : ReplacementQueries} {owner value : ValueId} {op : Op} (scalar : ScalarOp op)
    (run : emitDef op env before = (value, captured))
    (live : LiveBound before) (extension : captured.Ext state) :
    EmitsOnly (ReplacementInstApart module (func.valueTypes module) queries owner) before captured := by
  cases current : before.cur with
  | none =>
    rw [emitDef_none _ _ current] at run
    cases run
    exact .refl _ _
  | some index =>
    have resultId : value = before.vals.size := by
      rw [emitDef_run _ _ current] at run
      exact (Prod.mk.inj run).1.symm
    obtain ⟨block, blockMember, definition⟩ := emitted_definition_retained current
      (live index current) run extension blocks
    rw [blocks, finishBlocks, Array.toList_map] at blockMember
    obtain ⟨body, bodyMember, rfl⟩ := List.mem_map.mp blockMember
    have rawDefinition : Inst.def value op ∈ state.insts :=
      List.mem_flatMap.mpr ⟨body, bodyMember, definition⟩
    apply emitsOnly_emitDef run
    rw [← resultId]
    exact replacementScalarApart_of_source_graphs builder blocks slots globals sigs structs profile
      graphs rawDefinition scalar

theorem emitsOnly_literal_of_source_graphs
    {module : GIR.Module} {func : Func} {le env : LEnv} {state before captured : LS}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks)
    (slots : func.slots = le.slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = le.globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = le.sigs)
    (structs : module.structs = le.mod.structs)
    (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state)
    {queries : ReplacementQueries} {owner value : ValueId} {ty : Ty} {operands : List ValueId} {exprs : List Expr}
    {sourceEnv : Core.TEnv} {result : Ty} {start finish : Nat}
    (source : Core.tyExpr sourceEnv (.arrLit ty exprs) start = .ok (result, finish))
    (run : emitDef (.arrLit ty operands) env before = (value, captured))
    (live : LiveBound before) (extension : captured.Ext state) :
    EmitsOnly (ReplacementInstApart module (func.valueTypes module) queries owner) before captured := by
  cases current : before.cur with
  | none =>
    rw [emitDef_none _ _ current] at run
    cases run
    exact .refl _ _
  | some index =>
    have resultId : value = before.vals.size := by
      rw [emitDef_run _ _ current] at run
      exact (Prod.mk.inj run).1.symm
    obtain ⟨block, blockMember, definition⟩ := emitted_definition_retained current
      (live index current) run extension blocks
    rw [blocks, finishBlocks, Array.toList_map] at blockMember
    obtain ⟨body, bodyMember, rfl⟩ := List.mem_map.mp blockMember
    have rawDefinition : Inst.def value (.arrLit ty operands) ∈ state.insts :=
      List.mem_flatMap.mpr ⟨body, bodyMember, definition⟩
    apply emitsOnly_emitDef run
    rw [← resultId]
    exact replacementLiteralApart_of_source_graphs builder blocks slots globals sigs structs profile
      graphs rawDefinition source

inductive ScalarLiteral : Expr → Prop
  | int (type value) : ScalarLiteral (.lit type value)
  | bool (value) : ScalarLiteral (.bool value)

section ScalarLiterals

variable {module : GIR.Module} {func : Func} {le : LEnv} {state : LS}
variable (builder : EmittedBuilder le initState state)
variable (blocks : func.blocks = finishBlocks state.blocks) (slots : func.slots = le.slots)
variable (globals : (module.globals.map fun global => (global.ty, global.kind)) = le.globals)
variable (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = le.sigs)
variable (structs : module.structs = le.mod.structs) (profile : module.profile = le.mod.profile)
variable (graphs : MutableSnapshotGraphs module func state)

include builder blocks slots globals sigs structs profile graphs

theorem lowerExpr_scalar_literal_apart {env : LEnv} {before captured : LS}
    {queries : ReplacementQueries} {owner value : ValueId} {expr : Expr}
    (literal : ScalarLiteral expr) (run : lowerExpr expr env before = (value, captured))
    (live : LiveBound before) (extension : captured.Ext state) :
    EmitsOnly (ReplacementInstApart module (func.valueTypes module) queries owner) before captured := by
  cases literal with
  | int type number =>
    exact emitsOnly_scalar_of_source_graphs builder blocks slots globals sigs structs profile graphs
      (.constInt type number) run live extension
  | bool flag =>
    exact emitsOnly_scalar_of_source_graphs builder blocks slots globals sigs structs profile graphs
      (.constBool flag) run live extension

theorem lowerExprs_scalar_literals_apart {env : LEnv} {before captured : LS}
    {queries : ReplacementQueries} {owner : ValueId} {values : List ValueId} {exprs : List Expr}
    (literals : ∀ expr ∈ exprs, ScalarLiteral expr)
    (run : lowerExprs exprs env before = (values, captured))
    (live : LiveBound before) (extension : captured.Ext state) :
    EmitsOnly (ReplacementInstApart module (func.valueTypes module) queries owner) before captured := by
  induction exprs generalizing before values with
  | nil =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact .refl _ _
  | cons expr exprs ih =>
    change (lowerExpr expr >>= fun value => lowerExprs exprs >>= fun values => pure (value :: values)) env before =
      (values, captured) at run
    obtain ⟨value, middle, first, rest⟩ := bind_eq.mp run
    obtain ⟨tail, finished, next, last⟩ := bind_eq.mp rest
    obtain ⟨_, rfl⟩ := pure_eq.mp last
    have firstApart := lowerExpr_scalar_literal_apart (queries := queries) (owner := owner) builder blocks slots globals sigs structs profile graphs
      (literals expr (by simp)) first live ((advB_lowerExprs exprs _ _ _ _ next).ext.trans extension)
    have middleLive := liveBound_of_adv (advB_lowerExpr expr _ _ _ _ first) live
    exact firstApart.trans (ih (fun item member => literals item (by simp [member])) next middleLive)

theorem lowerExpr_scalar_array_literal_apart {env : LEnv} {before captured : LS}
    {queries : ReplacementQueries} {owner value : ValueId} {ty : Ty} {exprs : List Expr}
    {sourceEnv : Core.TEnv} {result : Ty} {start finish : Nat}
    (source : Core.tyExpr sourceEnv (.arrLit ty exprs) start = .ok (result, finish))
    (literals : ∀ expr ∈ exprs, ScalarLiteral expr)
    (run : lowerExpr (.arrLit ty exprs) env before = (value, captured))
    (live : LiveBound before) (extension : captured.Ext state) :
    EmitsOnly (ReplacementInstApart module (func.valueTypes module) queries owner) before captured := by
  change (lowerExprs exprs >>= fun values => emitDef (.arrLit ty values)) env before = (value, captured) at run
  obtain ⟨values, middle, first, next⟩ := bind_eq.mp run
  have firstApart := lowerExprs_scalar_literals_apart (queries := queries) (owner := owner) builder blocks slots globals sigs structs profile graphs
    literals first live ((adv_emitDef next).ext.trans extension)
  have middleLive := liveBound_of_adv (advB_lowerExprs exprs _ _ _ _ first) live
  exact firstApart.trans (emitsOnly_literal_of_source_graphs builder blocks slots globals sigs structs profile
    graphs source next middleLive extension)

theorem replacementRegion_scalar_literal_closed {env : LEnv} {before cleared captured : LS}
    {queries : ReplacementQueries} {owner value : ValueId} {origin : Option OriginId}
    {ty : Ty} {exprs : List Expr} {sourceEnv : Core.TEnv} {result : Ty} {start finish : Nat}
    (source : Core.tyExpr sourceEnv (.arrLit ty exprs) start = .ok (result, finish))
    (literals : ∀ expr ∈ exprs, ScalarLiteral expr)
    (clearRun : emitEffect (.clear owner origin) env before = ((), cleared))
    (rhsRun : lowerExpr (.arrLit ty exprs) env cleared = (value, captured))
    (live : LiveBound before) (bounded : TargetsBounded cleared)
    {loop : Option LoopCtx} (frames : LoopBuilderFrames loop cleared)
    (framed : TermEdgesFramed loop captured state) (extension : captured.Ext state)
    (shaped : ∀ (index : BlockId) (body : BlockB), captured.blocks[index]? = some body → OpenBlock body ∨ ClosedBlock body)
    (closed : ∀ body ∈ state.blocks.toList, ClosedBlock body) :
    EmptyFactsClosed module func (func.valueTypes module) queries (ReplacementRegionFacts cleared captured owner) := by
  have clearedLive := liveBound_of_adv (adv_emitEffect clearRun) live
  have emitted := lowerExpr_scalar_array_literal_apart (queries := queries) (owner := owner)
    builder blocks slots globals sigs structs profile graphs source literals rhsRun clearedLive extension
  exact replacementRegion_closed_of_emission live clearRun emitted
    (advB_lowerExpr (.arrLit ty exprs) _ _ _ _ rhsRun) bounded frames framed extension shaped closed blocks

end ScalarLiterals

end Goose.Lower.Validation
