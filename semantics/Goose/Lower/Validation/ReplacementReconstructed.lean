import Goose.Lower.Validation.ReplacementPure
import Goose.Lower.Validation.ValueTypeReconstructionLiteralRows

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ReplacementInstApart.scalar_reference_free {module : GIR.Module}
    {types : Array (Option VTy)} {queries : ReplacementQueries} {owner value : ValueId} {op : Op}
    (scalar : ScalarOp op)
    (operands : ∀ operand ∈ op.uses, valRefLike types operand = false) :
    ReplacementInstApart module types queries owner (.def value op) := by
  constructor
  · intro operand member reference
    have uses : emptyFactSourceOperands (.def value op) = op.uses := by cases scalar <;> rfl
    have absent := operands operand (uses ▸ member)
    simp [reference] at absent
  · intro resultValue member reference
    cases scalar <;> simp [ReplacementContentFlow.Model.loadedResults] at member
  · intro resultValue function args origin same
    cases scalar <;> cases same

theorem replacementScalarApart_of_source_graphs
    {module : GIR.Module} {func : Func} {le : LEnv} {state : LS}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks)
    (slots : func.slots = le.slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = le.globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = le.sigs)
    (structs : module.structs = le.mod.structs)
    (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state)
    {queries : ReplacementQueries} {owner value : ValueId} {op : Op}
    (definition : Inst.def value op ∈ state.insts) (scalar : ScalarOp op) :
    ReplacementInstApart module (func.valueTypes module) queries owner (.def value op) := by
  have retained := valueTypes_eq_retained_of_source_graphs builder blocks slots globals sigs structs profile graphs
  have initialPresent : EmittedTypesPresent initState := by
    intro value bound
    exact (Nat.not_lt_zero _ bound).elim
  obtain ⟨site, result, block, trace, checkpoint, extension, live, fresh, typed, recorded, typePrefix⟩ :=
    builder.sites value op definition
  have referenceFree := scalarOp_reference_free scalar typed
  apply ReplacementInstApart.scalar_reference_free scalar
  intro operand member
  have ordered := builder.checkpoint.operands.definitions value op definition operand member
  obtain ⟨operandType, row⟩ := trace.present initialPresent operand (by simpa only [← fresh] using ordered)
  have absent := referenceFree.2 operand member
  change valRefLike site.vals operand = false at absent
  simp only [valRefLike, row, Option.getD_some] at absent
  have finalRow := typePrefix.typed operand operandType row
  simpa only [valRefLike, retained, finalRow, Option.getD_some] using absent

theorem replacementFlatLiteralApart_of_source_graphs
    {module : GIR.Module} {func : Func} {le : LEnv} {state : LS}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks)
    (slots : func.slots = le.slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = le.globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = le.sigs)
    (structs : module.structs = le.mod.structs)
    (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state)
    {queries : ReplacementQueries} {owner value : ValueId} {ty : Ty} {operands : List ValueId}
    (definition : Inst.def value (.arrLit ty operands) ∈ state.insts)
    (flat : ∀ element, arrayElem? ty = some element → element.flat = true) :
    ReplacementInstApart module (func.valueTypes module) queries owner (.def value (.arrLit ty operands)) := by
  have retained := valueTypes_eq_retained_of_source_graphs builder blocks slots globals sigs structs profile graphs
  obtain ⟨site, output, block, trace, checkpoint, extension, live, fresh, typed, recorded, typePrefix⟩ :=
    builder.sites value (.arrLit ty operands) definition
  obtain ⟨element, shape, operandTypes, count, capacity, resultType⟩ := arrLit_metadata typed
  have flat := flat element shape
  have elementNotRef : element.isRefLike = false := by
    cases element <;> simp_all [Ty.flat, Ty.isRefLike]
  constructor
  · intro operand member reference
    have sourceRow := operandTypes operand member
    have finalRow := typePrefix.typed operand (.data element) sourceRow
    simp [valRefLike, retained, finalRow, VTy.refLike, elementNotRef] at reference
  · intro resultValue member reference
    simp [ReplacementContentFlow.Model.loadedResults] at member
  · intro resultValue function args origin same
    cases same

theorem replacementLiteralApart_of_source_graphs
    {module : GIR.Module} {func : Func} {le : LEnv} {state : LS}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks)
    (slots : func.slots = le.slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = le.globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = le.sigs)
    (structs : module.structs = le.mod.structs)
    (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state)
    {queries : ReplacementQueries} {owner value : ValueId} {ty : Ty} {operands : List ValueId}
    (definition : Inst.def value (.arrLit ty operands) ∈ state.insts)
    {sourceEnv : Core.TEnv} {exprs : List Expr} {result : Ty} {start finish : Nat}
    (source : Core.tyExpr sourceEnv (.arrLit ty exprs) start = .ok (result, finish)) :
    ReplacementInstApart module (func.valueTypes module) queries owner (.def value (.arrLit ty operands)) :=
  replacementFlatLiteralApart_of_source_graphs builder blocks slots globals sigs structs profile graphs
    definition (fun _ shape => source_arrLit_element_flat source shape)

end Goose.Lower.Validation
