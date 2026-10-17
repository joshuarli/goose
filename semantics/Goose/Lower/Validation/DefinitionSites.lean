import Goose.Lower.Validation.DenseDefinitions

namespace Goose.Lower

open Goose.GIR

inductive DefinitionSite where
  | parameter (block index : Nat) (ty : VTy)
  | instruction (block index : Nat) (op : Op)

def BlockB.definitionSites (block : Nat) (b : BlockB) : List (ValueId × DefinitionSite) :=
  b.params.zipIdx.map (fun (param, index) =>
    (param.1, .parameter block index param.2)) ++
  b.insts.toList.zipIdx.filterMap (fun (inst, index) => match inst with
    | .def value op => some (value, .instruction block index op)
    | _ => none)

def LS.definitionSites (ls : LS) : List (ValueId × DefinitionSite) :=
  ls.blocks.toList.zipIdx.flatMap fun (block, index) => block.definitionSites index

end Goose.Lower

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR Goose.Lower

private theorem parameterSites_ids_scan :
    ∀ (params : List (ValueId × VTy)) (start : Nat),
      (params.zipIdx start).map (fun (param, _) => param.1) = params.map Prod.fst := by
  intro params
  induction params with
  | nil => intro start; rfl
  | cons param rest ih =>
    intro start
    simp [List.zipIdx_cons, ih]

private theorem instructionSites_ids_scan (block : Nat) :
    ∀ (insts : List Inst) (start : Nat),
      (insts.zipIdx start |>.filterMap fun (inst, index) => match inst with
        | .def value op => some (value, DefinitionSite.instruction block index op)
        | _ => none).map Prod.fst = insts.filterMap (fun inst => match inst with
          | .def value _ => some value
          | _ => none) := by
  intro insts
  induction insts with
  | nil => intro start; rfl
  | cons inst rest ih =>
    intro start
    cases inst <;> simp [List.zipIdx_cons, ih]

theorem BlockB.definitionSites_ids (b : BlockB) (block : Nat) :
    (b.definitionSites block).map Prod.fst = b.defs := by
  unfold BlockB.definitionSites BlockB.defs
  simp only [List.map_append, List.map_map]
  congr 1
  · change (b.params.zipIdx).map (fun (param, _) => param.1) = _
    exact parameterSites_ids_scan b.params 0
  · exact instructionSites_ids_scan block b.insts.toList 0

theorem LS.definitionSites_ids (ls : LS) :
    ls.definitionSites.map Prod.fst = ls.defs := by
  simp only [LS.definitionSites, List.map_flatMap]
  have rows : (fun pair : BlockB × Nat =>
      (pair.1.definitionSites pair.2).map Prod.fst) =
      (fun pair : BlockB × Nat => pair.1.defs) := by
    funext pair
    exact BlockB.definitionSites_ids pair.1 pair.2
  rw [rows]
  have indexed := congrArg (List.flatMap BlockB.defs) (List.zipIdx_map_fst 0 ls.blocks.toList)
  simpa only [List.flatMap_map, LS.defs] using indexed

theorem block_parameterSite_mem {b : BlockB} {block index : Nat} {value : ValueId} {ty : VTy}
    (found : b.params[index]? = some (value, ty)) :
    (value, DefinitionSite.parameter block index ty) ∈ b.definitionSites block := by
  simp only [BlockB.definitionSites, List.mem_append]
  left
  apply List.mem_map.mpr
  refine ⟨((value, ty), index), List.mk_mem_zipIdx_iff_getElem?.mpr found, rfl⟩

theorem block_instructionSite_mem {b : BlockB} {block index : Nat} {value : ValueId} {op : Op}
    (found : b.insts.toList[index]? = some (.def value op)) :
    (value, DefinitionSite.instruction block index op) ∈ b.definitionSites block := by
  simp only [BlockB.definitionSites, List.mem_append]
  right
  apply List.mem_filterMap.mpr
  refine ⟨(.def value op, index), List.mk_mem_zipIdx_iff_getElem?.mpr found, rfl⟩

theorem parameterSite_mem {ls : LS} {block index : Nat} {value : ValueId} {ty : VTy}
    {b : BlockB} (blockFound : ls.blocks[block]? = some b)
    (parameterFound : b.params[index]? = some (value, ty)) :
    (value, DefinitionSite.parameter block index ty) ∈ ls.definitionSites := by
  unfold LS.definitionSites
  apply List.mem_flatMap.mpr
  refine ⟨(b, block), ?_, block_parameterSite_mem parameterFound⟩
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  simpa only [Array.getElem?_toList] using blockFound

theorem instructionSite_mem {ls : LS} {block index : Nat} {value : ValueId} {op : Op}
    {b : BlockB} (blockFound : ls.blocks[block]? = some b)
    (instructionFound : b.insts.toList[index]? = some (.def value op)) :
    (value, DefinitionSite.instruction block index op) ∈ ls.definitionSites := by
  unfold LS.definitionSites
  apply List.mem_flatMap.mpr
  refine ⟨(b, block), ?_, block_instructionSite_mem instructionFound⟩
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  simpa only [Array.getElem?_toList] using blockFound

private theorem parameterSite_lookup {ls : LS} {block index : Nat} {value : ValueId} {ty : VTy}
    (member : (value, DefinitionSite.parameter block index ty) ∈ ls.definitionSites) :
    ∃ b : BlockB, ls.blocks[block]? = some b ∧ b.params[index]? = some (value, ty) := by
  unfold LS.definitionSites at member
  obtain ⟨row, rowMember, siteMember⟩ := List.mem_flatMap.mp member
  rcases row with ⟨b, foundBlock⟩
  have rowLookup := List.mk_mem_zipIdx_iff_getElem?.mp rowMember
  simp only [BlockB.definitionSites, List.mem_append] at siteMember
  rcases siteMember with parameterMember | impossible
  · obtain ⟨indexed, indexedMember, equal⟩ := List.mem_map.mp parameterMember
    rcases indexed with ⟨param, position⟩
    cases param with
    | mk paramValue paramType =>
      simp only [Prod.mk.injEq] at equal
      rcases equal with ⟨rfl, siteEqual⟩
      injection siteEqual with blockEqual indexEqual typeEqual
      subst foundBlock
      subst position
      subst paramType
      have parameterLookup := List.mk_mem_zipIdx_iff_getElem?.mp indexedMember
      refine ⟨b, ?_, ?_⟩
      · simpa only [Array.getElem?_toList] using rowLookup
      · exact parameterLookup
  · simp only [List.mem_filterMap] at impossible
    obtain ⟨indexed, _, equal⟩ := impossible
    rcases indexed with ⟨inst, _⟩
    cases inst <;> simp at equal

private theorem instructionSite_lookup {ls : LS} {block index : Nat} {value : ValueId} {op : Op}
    (member : (value, DefinitionSite.instruction block index op) ∈ ls.definitionSites) :
    ∃ b : BlockB, ls.blocks[block]? = some b ∧ b.insts.toList[index]? = some (.def value op) := by
  unfold LS.definitionSites at member
  obtain ⟨row, rowMember, siteMember⟩ := List.mem_flatMap.mp member
  rcases row with ⟨b, foundBlock⟩
  have rowLookup := List.mk_mem_zipIdx_iff_getElem?.mp rowMember
  simp only [BlockB.definitionSites, List.mem_append] at siteMember
  rcases siteMember with impossible | instructionMember
  · simp only [List.mem_map] at impossible
    obtain ⟨indexed, _, equal⟩ := impossible
    rcases indexed with ⟨param, _⟩
    cases param with
    | mk paramValue paramType => simp at equal
  · simp only [List.mem_filterMap] at instructionMember
    obtain ⟨indexed, indexedMember, equal⟩ := instructionMember
    rcases indexed with ⟨inst, position⟩
    cases inst with
    | «def» result emittedOp =>
      simp only [Option.some.injEq, Prod.mk.injEq] at equal
      rcases equal with ⟨rfl, siteEqual⟩
      injection siteEqual with blockEqual indexEqual opEqual
      subst foundBlock
      subst position
      subst emittedOp
      have instructionLookup := List.mk_mem_zipIdx_iff_getElem?.mp indexedMember
      refine ⟨b, ?_, ?_⟩
      · simpa only [Array.getElem?_toList] using rowLookup
      · exact instructionLookup
    | «eff» _ => simp at equal
    | «term» _ => simp at equal

theorem definitionSite_mem_of_ext {before after : LS} (extension : before.Ext after)
    {value : ValueId} {site : DefinitionSite}
    (member : (value, site) ∈ before.definitionSites) :
    (value, site) ∈ after.definitionSites := by
  cases site with
  | parameter block index ty =>
    obtain ⟨oldBlock, oldBlockFound, oldParameterFound⟩ := parameterSite_lookup member
    obtain ⟨newBlock, newBlockFound, sameParams, _⟩ := extension.2 block oldBlock oldBlockFound
    apply parameterSite_mem newBlockFound
    rw [sameParams]
    exact oldParameterFound
  | instruction block index op =>
    obtain ⟨oldBlock, oldBlockFound, oldInstructionFound⟩ := instructionSite_lookup member
    obtain ⟨newBlock, newBlockFound, _, extra, sameInstructions⟩ :=
      extension.2 block oldBlock oldBlockFound
    have indexBound : index < oldBlock.insts.toList.length :=
      (List.getElem?_eq_some_iff.mp oldInstructionFound).1
    have appendedInstruction :
        (oldBlock.insts.toList ++ extra)[index]? = some (.def value op) := by
      rw [List.getElem?_append_left indexBound]
      exact oldInstructionFound
    have newInstruction : newBlock.insts.toList[index]? = some (.def value op) := by
      simpa only [sameInstructions] using appendedInstruction
    exact instructionSite_mem newBlockFound newInstruction

private theorem entry_eq_of_nodup_ids {entries : List (ValueId × DefinitionSite)}
    (unique : (entries.map Prod.fst).Nodup) {left right : ValueId × DefinitionSite}
    (leftMem : left ∈ entries) (rightMem : right ∈ entries)
    (sameValue : left.1 = right.1) : left = right := by
  induction entries with
  | nil => simp at leftMem
  | cons entry entries ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp leftMem with leftHead | leftTail
    · subst left
      rcases List.mem_cons.mp rightMem with rightHead | rightTail
      · exact rightHead.symm
      · exact False.elim (unique.1 (List.mem_map.mpr ⟨right, rightTail, sameValue.symm⟩))
    · rcases List.mem_cons.mp rightMem with rightHead | rightTail
      · subst right
        exact False.elim (unique.1 (List.mem_map.mpr ⟨left, leftTail, sameValue⟩))
      · exact ih unique.2 leftTail rightTail

theorem oldDefinitionSite {before after : LS}
    (denseBefore : before.DenseDefinitions) (denseAfter : after.DenseDefinitions)
    (extension : before.Ext after) {value : ValueId} {site : DefinitionSite}
    (bound : value < before.vals.size)
    (member : (value, site) ∈ after.definitionSites) :
    (value, site) ∈ before.definitionSites := by
  have definedBefore : value ∈ before.defs :=
    denseBefore.symm.subset (List.mem_range.mpr bound)
  have siteValue : value ∈ before.definitionSites.map Prod.fst := by
    rw [LS.definitionSites_ids]
    exact definedBefore
  obtain ⟨candidate, candidateMember, candidateValue⟩ := List.mem_map.mp siteValue
  rcases candidate with ⟨candidateId, candidateSite⟩
  have candidateEq : candidateId = value := by simpa using candidateValue
  subst candidateId
  have candidateAfter := definitionSite_mem_of_ext extension candidateMember
  have uniqueAfter : (after.definitionSites.map Prod.fst).Nodup := by
    rw [LS.definitionSites_ids]
    exact denseAfter.nodup
  have sameSite := entry_eq_of_nodup_ids uniqueAfter member candidateAfter rfl
  cases sameSite
  exact candidateMember

theorem old_instruction_site {before after : LS}
    (denseBefore : before.DenseDefinitions) (denseAfter : after.DenseDefinitions)
    (extension : before.Ext after) {block index : Nat} {value : ValueId} {op : Op}
    {afterBlock : BlockB} (blockFound : after.blocks[block]? = some afterBlock)
    (instructionFound : afterBlock.insts.toList[index]? = some (.def value op))
    (bound : value < before.vals.size) :
    ∃ beforeBlock : BlockB, before.blocks[block]? = some beforeBlock ∧
      beforeBlock.insts.toList[index]? = some (.def value op) := by
  have siteAfter := instructionSite_mem blockFound instructionFound
  exact instructionSite_lookup
    (oldDefinitionSite denseBefore denseAfter extension bound siteAfter)

theorem old_parameter_site {before after : LS}
    (denseBefore : before.DenseDefinitions) (denseAfter : after.DenseDefinitions)
    (extension : before.Ext after) {block index : Nat} {value : ValueId} {ty : VTy}
    {afterBlock : BlockB} (blockFound : after.blocks[block]? = some afterBlock)
    (parameterFound : afterBlock.params[index]? = some (value, ty))
    (bound : value < before.vals.size) :
    ∃ beforeBlock : BlockB, before.blocks[block]? = some beforeBlock ∧
      beforeBlock.params[index]? = some (value, ty) := by
  have siteAfter := parameterSite_mem blockFound parameterFound
  exact parameterSite_lookup
    (oldDefinitionSite denseBefore denseAfter extension bound siteAfter)

end Goose.Lower.Validation
