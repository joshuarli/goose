import Goose.Lower.Validation.ReplacementContentFlowSourceConsumedReferences
import Goose.GIR.ReplacementContentFlowProofsScopedEdges
import Goose.GIR.ReplacementContentFlowProofsScopedQueries

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR Goose.GIR.ReplacementContentFlow.Model

def ScopedTypedBacking (func : Func) (types : Array (Option VTy)) (value : ValueId) : Prop :=
  ∃ source op block, block ∈ func.blocks.toList ∧ Inst.def value op ∈ block.insts ∧
    BackingOp op source ∧ ∃ type, types[source]? = some (some type) ∧ SliceViewType type

def ScopedReferenceUse (func : Func) (first last value : ValueId) : Prop :=
  ∃ consumer op block, block ∈ func.blocks.toList ∧ Inst.def consumer op ∈ block.insts ∧
    first ≤ consumer ∧ consumer < last ∧ value ∈ accessOperands (.def consumer op)

def ScopedOrigin (env : PEnv) (root : DemandNode) (func : Func)
    (types : Array (Option VTy)) (upper : Prov) (first last value : ValueId) : Prop :=
  first ≤ value ∧ value < last ∧
    ((∃ type, types[value]? = some (some type) ∧ SliceViewType type) ∨
      ∃ mutability payload, types[value]? = some (some (.data (.ref mutability payload))) ∧
        ConsumedReferenceOccurrence env root func types upper value ∧ ScopedReferenceUse func first last value)

def ScopedOriginLeaf (env : PEnv) (root : DemandNode) (func : Func)
    (types : Array (Option VTy)) (upper : Prov) (value : ValueId) : Prop :=
  (∃ mutability payload, types[value]? = some (some (.data (.ref mutability payload))) ∧
    ConsumedReferenceOccurrence env root func types upper value ∧ ¬ ScopedTypedBacking func types value) ∨
    (∃ block address, block ∈ func.blocks.toList ∧ Inst.def value (.load address) ∈ block.insts) ∨
    ∃ block callee args origin, block ∈ func.blocks.toList ∧ Inst.def value (.call callee args origin) ∈ block.insts

noncomputable def scopedOriginLeaves (env : PEnv) (root : DemandNode) (func : Func)
    (types : Array (Option VTy)) (upper : Prov) (first last : ValueId) : List ValueId := by
  classical
  exact (List.range last).filter (fun value => ScopedOrigin env root func types upper first last value ∧
    ScopedOriginLeaf env root func types upper value)

theorem mem_scopedOriginLeaves {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {first last value : ValueId} :
    value ∈ scopedOriginLeaves env root func types upper first last ↔
      value < last ∧ ScopedOrigin env root func types upper first last value ∧
        ScopedOriginLeaf env root func types upper value := by
  classical
  simp [scopedOriginLeaves]

theorem ScopedOrigin.reference {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {first last value : ValueId}
    (chosen : ScopedOrigin env root func types upper first last value) : valRefLike types value = true := by
  rcases chosen.2.2 with ⟨type,typeAt,carrier⟩ | ⟨mutability,payload,typeAt,origin,consumed⟩
  · simp only [valRefLike,typeAt]
    exact carrier.reference
  · simp [valRefLike,typeAt,VTy.refLike,Ty.isRefLike]

theorem ScopedOrigin.definitions {module : GIR.Module} {env : PEnv} {root : DemandNode}
    {func : Func} {types : Array (Option VTy)} {upper : Prov} {first last : ValueId}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (values : ValueTypeShapes types)
    (globals : ∀ (index : Nat) (type : Ty) (kind : VarKind), (module.tyEnv func).globals[index]? = some (type,kind) → type.isRefLike = false)
    (fields : ∀ (index : Nat) (descriptor : StructDef), (module.tyEnv func).structs[index]? = some descriptor →
      ∀ (fieldIndex : Nat) (field : StructField), descriptor.fields[fieldIndex]? = some field → field.ty.flat = true)
    (typing : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts, InstructionTyping module func types inst)
    (uses : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      first ≤ value → value < last → ∀ source ∈ (Inst.def value op).uses, first ≤ source ∧ source < last)
    (references : ∀ block ∈ func.blocks.toList, ∀ value op, Inst.def value op ∈ block.insts →
      first ≤ value → value < last → ∀ source ∈ accessOperands (.def value op), ∀ mutability payload,
        types[source]? = some (some (.data (.ref mutability payload))) →
        ConsumedReferenceOccurrence env root func types upper source)
    (block : GIR.Block) (member : block ∈ func.blocks.toList) (value : ValueId) (op : Op)
    (defined : Inst.def value op ∈ block.insts)
    (chosen : ScopedOrigin env root func types upper first last value) :
    ScopedOriginLeaf env root func types upper value ∨
      ∃ source, ScopedOrigin env root func types upper first last source ∧
        (∀ callee args origin, op ≠ .call callee args origin) ∧
        ∀ state, result func types state value op = flowAt state.values source := by
  classical
  have reference := chosen.reference
  rcases chosen with ⟨lower,bounded,carrier | referenceOrigin⟩
  · obtain ⟨type,typeAt,carrier⟩ := carrier
    have actualTyping := typing block member (.def value op) defined
    cases actualTyping with
    | definition value op actual typed canonical =>
        have same : actual = type := by simpa only [typeAt,Option.some.injEq] using canonical.symm
        subst actual
        have classified := SliceDefinition.of_carrier_resultTy (env := {module.tyEnv func with vals := types}) values globals fields op carrier typed
        cases classified with
        | load address => exact .inl (.inr (.inl ⟨block,address,member,defined⟩))
        | call callee args origin => exact .inl (.inr (.inr ⟨block,callee,args,origin,member,defined⟩))
        | backing op source backing accessed sourceReference =>
            have sourceBounds := uses block member value op defined lower bounded source backing.source_used
            refine .inr ⟨source,⟨sourceBounds.1,sourceBounds.2,?_⟩,backing.noncall,backing.result reference⟩
            obtain ⟨sourceType,sourceAt,sourceShape⟩ := valRefLike_type_cases sourceReference
            rcases sourceShape with sourceCarrier | ⟨mutability,payload,same⟩
            · exact .inl ⟨sourceType,sourceAt,sourceCarrier⟩
            · subst sourceType
              exact .inr ⟨mutability,payload,sourceAt,
                references block member value op defined lower bounded source (accessed value) mutability payload sourceAt,
                ⟨value,op,block,member,defined,lower,bounded,accessed value⟩⟩
  · obtain ⟨mutability,payload,typeAt,origin,consumed⟩ := referenceOrigin
    by_cases backed : ScopedTypedBacking func types value
    · obtain ⟨source,actual,actualBlock,actualMember,actualDefined,backing,sourceType,sourceAt,sourceCarrier⟩ := backed
      have same := unique_definition_op unique member defined actualMember actualDefined
      subst actual
      have sourceBounds := uses block member value op defined lower bounded source backing.source_used
      exact .inr ⟨source,⟨sourceBounds.1,sourceBounds.2,.inl ⟨sourceType,sourceAt,sourceCarrier⟩⟩,
        backing.noncall,backing.result reference⟩
    · exact .inl (.inl ⟨mutability,payload,typeAt,origin,backed⟩)

theorem ScopedOrigin.incoming {module : GIR.Module} {env : PEnv} {root : DemandNode}
    {func : Func} {types : Array (Option VTy)} {upper : Prov} {first last value source : ValueId}
    (unique : (func.blocks.toList.flatMap Block.defs).Nodup)
    (typing : ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts, InstructionTyping module func types inst)
    (chosen : ScopedOrigin env root func types upper first last value)
    (notLeaf : ¬ ScopedOriginLeaf env root func types upper value)
    (incoming : source ∈ allIncomingValues func value)
    (sourceBounds : first ≤ source ∧ source < last) :
    ScopedOrigin env root func types upper first last source := by
  classical
  refine ⟨sourceBounds.1,sourceBounds.2,?_⟩
  rcases chosen.2.2 with ⟨type,typeAt,carrier⟩ | ⟨mutability,payload,typeAt,origin,consumed⟩
  · exact .inl ⟨type,(allIncomingValues_type typing incoming).symm.trans typeAt,carrier⟩
  · have backed : ScopedTypedBacking func types value := by
      exact Classical.byContradiction (fun missing => notLeaf (.inl ⟨mutability,payload,typeAt,origin,missing⟩))
    obtain ⟨backingSource,op,block,member,defined,_⟩ := backed
    exact False.elim (allIncomingValues_absent_of_definition unique member defined incoming)

#print axioms mem_scopedOriginLeaves
#print axioms ScopedOrigin.reference
#print axioms ScopedOrigin.definitions
#print axioms ScopedOrigin.incoming

end Goose.Lower.Validation.ReplacementContentFlowSource
