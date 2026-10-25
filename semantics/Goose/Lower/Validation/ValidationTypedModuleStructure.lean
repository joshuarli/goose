import Goose.Lower.Validation.ValidationTypedModuleInterfaces
import Goose.Lower.Validation.EmittedMetadataStatic
import Goose.Lower.Validation.ValidationTypedModuleResolved
import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceModule

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem function_info {module : GIR.Module} {func : Func}
    (member : func ∈ module.funcs.toList ++ module.globals.toList.map (·.init)) :
    ∃ info ∈ module.infos, info.f = func := by
  rcases List.mem_append.mp member with functionMember | globalMember
  · refine ⟨⟨s!"function {func.name}", func, func.valueTypes module⟩, ?_, rfl⟩
    apply List.mem_map.mpr
    refine ⟨(s!"function {func.name}", func), ?_, rfl⟩
    exact List.mem_append_left _ (List.mem_map.mpr ⟨func, functionMember, rfl⟩)
  · obtain ⟨global, inGlobals, same⟩ := List.mem_map.mp globalMember
    rw [← same]
    refine ⟨⟨s!"initializer of global {global.name}", global.init, global.init.valueTypes module⟩, ?_, rfl⟩
    apply List.mem_map.mpr
    refine ⟨(s!"initializer of global {global.name}", global.init), ?_, rfl⟩
    exact List.mem_append_right _ (List.mem_map.mpr ⟨global, inGlobals, rfl⟩)

theorem lower_function_interface_resolved {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {func : Func}
    (member : func ∈ (lower module).funcs.toList ++ (lower module).globals.toList.map (·.init)) :
    ∀ type ∈ func.params ++ func.results ++ func.slots.toList.map (fun slot : GIR.Slot => slot.ty),
      Core.checkResolvedType module type = .ok () := by
  obtain ⟨info, infoMember, rfl⟩ := function_info member
  exact lower_info_interface_resolved accepted infoMember

theorem emitted_static_finished_rows {module : Core.Module} {func : Func} {state : LS}
    (source : EmittedStatic module state) (blocks : func.blocks = finishBlocks state.blocks)
    {block : GIR.Block} (member : block ∈ func.blocks.toList) :
    (∀ parameter ∈ block.params, EmittedVTyResolved module parameter.2) ∧
      (∀ instruction ∈ block.insts,
        EmittedProfileInst module.profile instruction ∧ EmittedAnnotationResolved module instruction) := by
  rw [blocks, finishBlocks, Array.toList_map] at member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  constructor
  · exact source.resolved.parameters original originalMember
  · intro instruction instructionMember
    have actual : instruction ∈ state.insts := List.mem_flatMap.mpr ⟨original, originalMember, instructionMember⟩
    exact ⟨source.profiles instruction actual, source.resolved.annotations instruction actual⟩

private theorem forIn_unit_ok {items : List α} {body : α → PUnit → Except ε (ForInStep PUnit)}
    (checked : ∀ item ∈ items, body item PUnit.unit = .ok (.yield PUnit.unit)) :
    forIn items PUnit.unit body = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest inductionHypothesis =>
    rw [List.forIn_cons, checked item (by simp)]
    simp only [bind, Except.bind]
    exact inductionHypothesis (fun next member => checked next (by simp [member]))

private theorem struct_types_of_rows {module : Core.Module}
    (accepted : Core.validate module = .ok ())
    (rows : ∀ func ∈ (lower module).funcs.toList ++ (lower module).globals.toList.map (·.init),
      ∀ block ∈ func.blocks.toList,
        (∀ parameter ∈ block.params, EmittedVTyResolved module parameter.2) ∧
        (∀ instruction ∈ block.insts,
          EmittedProfileInst module.profile instruction ∧ EmittedAnnotationResolved module instruction)) :
    checkStructTypes (lower module) = .ok () := by
  let lowered := lower module
  let cm : Core.Module :=
    { files := lowered.files, types := #[], globals := #[], impls := #[], contexts := #[],
      entry := 0, origins := lowered.origins, profile := lowered.profile, structs := lowered.structs }
  let check : Core.V Unit → Check Unit := fun result => match result with
    | .ok _ => pure ()
    | .error error => violation .v010 error.message
  have resolved (type : Ty) (source : Core.checkResolvedType module type = .ok ()) :
      check (Core.checkResolvedType cm type) = .ok () := by
    have same : Core.checkResolvedType cm type = Core.checkResolvedType module type :=
      resolvedType_eq_of_tables (source := cm) (target := module) rfl rfl type
    simp [same, source, check, pure, Except.pure]
  have descriptor : check (Core.checkStructTables cm) = .ok () := by
    rw [show Core.checkStructTables cm = .ok () from lower_structDescriptorTables accepted]
    rfl
  have regionGlobals := lower_checkRegionGlobalTypes accepted
  have globals : forIn lowered.globals PUnit.unit (fun (global : GIR.Global) _ => do
      check (Core.checkResolvedType cm global.ty)
      pure (ForInStep.yield PUnit.unit)) = (Except.ok PUnit.unit : Check PUnit) := by
    rw [← Array.forIn_toList]
    apply forIn_unit_ok
    intro global member
    obtain ⟨index, globalAt⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    cases sourceAt : module.globals[index]? with
    | none => simp [lowered, lower, Array.getElem?_map, sourceAt] at globalAt
    | some source =>
      have same : global = lowerGlobal module source := by
        simpa only [lowered, lower, Array.getElem?_map, sourceAt, Option.map_some, Option.some.injEq] using globalAt.symm
      have checked := checkStructTables_global_resolved (Core.Sound.validate_modOk module accepted).structTables
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? sourceAt))
      rw [same]
      change (do check (Core.checkResolvedType cm source.ty); pure (ForInStep.yield PUnit.unit)) = (Except.ok (ForInStep.yield PUnit.unit) : Check (ForInStep PUnit))
      rw [resolved source.ty checked]
      rfl
  have functions : forIn (lowered.funcs.toList ++ lowered.globals.toList.map (fun global : GIR.Global => global.init)) PUnit.unit (fun (func : Func) _ => do
      for type in func.params ++ func.results ++ func.slots.toList.map (fun slot : GIR.Slot => slot.ty) do
        check (Core.checkResolvedType cm type)
      for block in func.blocks do
        for (_, type) in block.params do
          match type with
          | VTy.data type | VTy.view _ type => check (Core.checkResolvedType cm type)
        for instruction in block.insts do
          match instruction with
          | .def _ (.structLit type _) | .def _ (.arrLit type _) | .def _ (.arrFill type _) =>
              check (Core.checkResolvedType cm type)
          | .def _ (.fieldAddr ..) =>
              unless lowered.profile == ArtifactProfile.shrink do violation .v010 "structs require core-shrink"
          | _ => pure ()
      pure (ForInStep.yield PUnit.unit)) = (Except.ok PUnit.unit : Check PUnit) := by
    apply forIn_unit_ok
    intro func member
    have interface := lower_function_interface_resolved accepted member
    have parameterLoop : forIn (func.params ++ func.results ++ func.slots.toList.map (fun slot : GIR.Slot => slot.ty)) PUnit.unit
        (fun type _ => do check (Core.checkResolvedType cm type); pure (ForInStep.yield PUnit.unit)) = (Except.ok PUnit.unit : Check PUnit) := by
      apply forIn_unit_ok
      intro type inInterface
      rw [resolved type (interface type inInterface)]
      rfl
    rw [parameterLoop]
    simp only [bind, Except.bind]
    suffices blockLoop : forIn func.blocks PUnit.unit (fun (block : GIR.Block) _ => do
        for (_, type) in block.params do
          match type with
          | VTy.data type | VTy.view _ type => check (Core.checkResolvedType cm type)
        for instruction in block.insts do
          match instruction with
          | .def _ (.structLit type _) | .def _ (.arrLit type _) | .def _ (.arrFill type _) =>
              check (Core.checkResolvedType cm type)
          | .def _ (.fieldAddr ..) =>
              unless lowered.profile == ArtifactProfile.shrink do violation .v010 "structs require core-shrink"
          | _ => pure ()
        pure (ForInStep.yield PUnit.unit)) = (Except.ok PUnit.unit : Check PUnit) by
      simp only [bind, Except.bind, pure, Except.pure] at blockLoop ⊢
      rw [blockLoop]
    rw [← Array.forIn_toList]
    apply forIn_unit_ok
    intro block blockMember
    obtain ⟨parameters, instructions⟩ := rows func member block blockMember
    have blockParameters : forIn block.params PUnit.unit (fun (_, type) _ => do
        match type with
        | VTy.data type | VTy.view _ type => check (Core.checkResolvedType cm type)
        pure (ForInStep.yield PUnit.unit)) = (Except.ok PUnit.unit : Check PUnit) := by
      apply forIn_unit_ok
      intro parameter inBlock
      have typed := parameters parameter inBlock
      rcases parameter with ⟨value, type⟩
      cases type with
      | data type | view mu type =>
        simp only [resolved type typed, bind, Except.bind, pure, Except.pure]
    rw [blockParameters]
    simp only [bind, Except.bind]
    suffices instructionLoop : forIn block.insts PUnit.unit (fun (instruction : Inst) _ => do
        match instruction with
        | .def _ (.structLit type _) | .def _ (.arrLit type _) | .def _ (.arrFill type _) =>
            check (Core.checkResolvedType cm type)
        | .def _ (.fieldAddr ..) =>
            unless lowered.profile == ArtifactProfile.shrink do violation .v010 "structs require core-shrink"
        | _ => pure ()
        pure (ForInStep.yield PUnit.unit)) = (Except.ok PUnit.unit : Check PUnit) by
      simp only [bind, Except.bind, pure, Except.pure] at instructionLoop ⊢
      rw [instructionLoop]
    apply forIn_unit_ok
    intro instruction inBlock
    obtain ⟨profile, annotation⟩ := instructions instruction inBlock
    cases instruction with
    | «def» value op =>
      cases op <;> try rfl
      all_goals solve
        | simp only [resolved _ annotation, bind, Except.bind, pure, Except.pure]
        | simp [EmittedProfileInst] at profile
          simp [lowered, show (lower module).profile = module.profile from rfl, profile,
            pure, Except.pure]
    | eff effect => rfl
    | term term => rfl
  simp only [bind, Except.bind, pure, Except.pure] at globals functions
  unfold checkStructTypes
  change (do
    check (Core.checkStructTables cm)
    asCheck .v010 "globals" lowered.checkRegionGlobalTypes
    for global in lowered.globals do check (Core.checkResolvedType cm global.ty)
    for func in lowered.funcs.toList ++ lowered.globals.toList.map (fun global : GIR.Global => global.init) do
      for type in func.params ++ func.results ++ func.slots.toList.map (fun slot : GIR.Slot => slot.ty) do check (Core.checkResolvedType cm type)
      for block in func.blocks do
        for (_, type) in block.params do
          match type with
          | VTy.data type | VTy.view _ type => check (Core.checkResolvedType cm type)
        for instruction in block.insts do
          match instruction with
          | .def _ (.structLit type _) | .def _ (.arrLit type _) | .def _ (.arrFill type _) =>
              check (Core.checkResolvedType cm type)
          | .def _ (.fieldAddr ..) =>
              unless lowered.profile == ArtifactProfile.shrink do violation .v010 "structs require core-shrink"
          | _ => pure ()) = .ok ()
  rw [descriptor]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [regionGlobals]
  simp only [asCheck]
  rw [globals]
  simp only []
  rw [functions]

private theorem body_resolved_finished_rows {module : Core.Module} {func : Func} {state : LS}
    (source : EmittedBodyResolved module state) (blocks : func.blocks = finishBlocks state.blocks)
    {block : GIR.Block} (member : block ∈ func.blocks.toList) :
    (∀ parameter ∈ block.params, EmittedVTyResolved module parameter.2) ∧
      (∀ instruction ∈ block.insts, EmittedAnnotationResolved module instruction) := by
  rw [blocks, finishBlocks, Array.toList_map] at member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  constructor
  · exact source.parameters original originalMember
  · intro instruction instructionMember
    exact source.annotations instruction (List.mem_flatMap.mpr ⟨original, originalMember, instructionMember⟩)

theorem lower_function_bodyResolved_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {func : Func}
    (member : func ∈ (lower module).funcs.toList ++ (lower module).globals.toList.map (·.init))
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList) :
    (∀ parameter ∈ block.params, EmittedVTyResolved module parameter.2) ∧
      (∀ instruction ∈ block.insts, EmittedAnnotationResolved module instruction) := by
  obtain ⟨info, infoMember, same⟩ := function_info member
  rw [← same] at blockMember
  obtain ⟨_, source⟩ := lower_info_source accepted infoMember
  rcases source with ⟨contextIndex, context, impl, contextAt, implAt, same⟩ |
    ⟨globalIndex, global, globalAt, same⟩
  · rw [same] at blockMember
    exact body_resolved_finished_rows (lowerImpl_resolved_of_accepted accepted implAt).toEmittedBodyResolved
      (cfg_context_blocks module context impl) blockMember
  · rw [same] at blockMember
    exact body_resolved_finished_rows (lowerGlobal_resolved_of_accepted accepted globalAt).toEmittedBodyResolved
      (cfg_global_blocks module global) blockMember

theorem lower_checkStructTypes_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) : checkStructTypes (lower module) = .ok () := by
  apply struct_types_of_rows accepted
  intro func member block blockMember
  obtain ⟨parameters, annotations⟩ := lower_function_bodyResolved_of_accepted accepted member blockMember
  exact ⟨parameters, fun instruction instructionMember =>
    ⟨lower_functionProfile_of_accepted accepted func member block blockMember instruction instructionMember,
      annotations instruction instructionMember⟩⟩

end Goose.Lower.Validation
