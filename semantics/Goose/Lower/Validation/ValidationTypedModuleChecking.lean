import Goose.Lower.Validation.ValidationTypedModuleInterfaces
import Goose.Lower.Validation.ValidationTypedModuleInstructions
import Goose.Lower.Validation.EmittedMetadataStatic
import Goose.Lower.Validation.EmittedMetadataStaticProfileSourceModule

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem forIn_unit_ok {items : List α} {body : α → PUnit → Except ε (ForInStep PUnit)}
    (checked : ∀ item ∈ items, body item PUnit.unit = .ok (.yield PUnit.unit)) :
    forIn items PUnit.unit body = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest inductionHypothesis =>
    rw [List.forIn_cons, checked item (by simp)]
    simp only [bind, Except.bind]
    exact inductionHypothesis (fun next member => checked next (by simp [member]))

private theorem profile_instruction_check {profile : ArtifactProfile} {instruction : Inst}
    (supported : EmittedProfileInst profile instruction) :
    (do
      match instruction with
      | .def _ (.pop ..) | .eff (.popN ..) | .eff (.resize ..)
      | .eff (.clear ..) | .eff (.replace ..) =>
          unless profile == .shrink do throw "operation requires core-shrink"
      | .term (.abort kind _) =>
          if profile != .shrink && kind ∈ [.popEmpty, .popNRange, .resizeNegative, .resizeFill, .capacity] then
            throw s!"abort kind {kind.tag.quote} requires core-shrink"
      | _ => pure ()
      pure (ForInStep.yield PUnit.unit)) = (Except.ok (.yield PUnit.unit) : Except String _) := by
  cases instruction with
  | «def» value op => cases op <;> simp_all [EmittedProfileInst, pure, Except.pure]
  | eff effect => cases effect <;> simp_all [EmittedProfileInst, pure, Except.pure]
  | term term =>
    cases term with
    | abort kind origin =>
      by_cases forbidden : kind ∈ [AbortKind.popEmpty, .popNRange, .resizeNegative, .resizeFill, .capacity]
      · have same := supported forbidden
        simp [same, pure, Except.pure]
      · simp [forbidden, pure, Except.pure]
    | _ => rfl

private theorem profile_function_checks {module : GIR.Module} {func : Func}
    (supported : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      EmittedProfileInst module.profile instruction) :
    forIn func.blocks PUnit.unit (fun block _ => do
      for instruction in block.insts do
        match instruction with
        | .def _ (.pop ..) | .eff (.popN ..) | .eff (.resize ..)
        | .eff (.clear ..) | .eff (.replace ..) =>
            unless module.profile == .shrink do throw "operation requires core-shrink"
        | .term (.abort kind _) =>
            if module.profile != .shrink && kind ∈ [.popEmpty, .popNRange, .resizeNegative, .resizeFill, .capacity] then
              throw s!"abort kind {kind.tag.quote} requires core-shrink"
        | _ => pure ()
      pure (.yield PUnit.unit)) = (Except.ok PUnit.unit : Except String _) := by
  rw [← Array.forIn_toList]
  apply forIn_unit_ok
  intro block member
  suffices inner : forIn block.insts PUnit.unit (fun instruction _ => do
      match instruction with
      | .def _ (.pop ..) | .eff (.popN ..) | .eff (.resize ..)
      | .eff (.clear ..) | .eff (.replace ..) =>
          unless module.profile == .shrink do throw "operation requires core-shrink"
      | .term (.abort kind _) =>
          if module.profile != .shrink && kind ∈ [.popEmpty, .popNRange, .resizeNegative, .resizeFill, .capacity] then
            throw s!"abort kind {kind.tag.quote} requires core-shrink"
      | _ => pure ()
      pure (.yield PUnit.unit)) = (Except.ok PUnit.unit : Except String _) by
    rw [inner]
    rfl
  apply forIn_unit_ok
  intro instruction inBlock
  exact profile_instruction_check (supported block member instruction inBlock)

private theorem check_types_of_instructions {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {info : FnInfo}
    (member : info ∈ (lower module).infos)
    (supported : ∀ block ∈ info.f.blocks.toList, ∀ instruction ∈ block.insts,
      EmittedProfileInst module.profile instruction)
    (instructions : ∀ block ∈ info.f.blocks.toList, ∀ instruction ∈ block.insts,
      checkInstTypes info.f { (lower module).tyEnv info.f with vals := info.vt }
        info.vt instruction = .ok ()) :
    checkTypes (lower module) info.label info.f info.vt = .ok () := by
  have profiles := profile_function_checks (module := lower module) supported
  have parameters : (checkAll info.f.params fun ty => do
      unless ty.paramOk do throw "a parameter has a type no parameter may have") =
      (Except.ok () : Except String Unit) := by
    obtain ⟨_, source⟩ := lower_info_source accepted member
    rcases source with ⟨contextIndex, context, impl, contextAt, implAt, same⟩ |
      ⟨globalIndex, global, globalAt, same⟩
    · rw [same]
      exact lowerContextAt_parameterTypeChecks context accepted implAt
    · rw [same]
      rfl
  have results := lower_info_resultTypeChecks accepted member
  have slots := lower_info_slotTypeChecks accepted member
  have rows : (checkAll info.f.blocks.toList fun block =>
      checkAll block.insts (checkInstTypes info.f { (lower module).tyEnv info.f with vals := info.vt } info.vt)) =
        (Except.ok () : Except String Unit) := by
    apply Origins.checkAll_ok_of_forall
    intro block inFunction
    apply Origins.checkAll_ok_of_forall
    exact instructions block inFunction
  obtain ⟨entry, entryAt, entryTypes⟩ := lower_info_entry_types accepted member
  have checked : (do
      for block in info.f.blocks do
        for instruction in block.insts do
          match instruction with
          | .def _ (.pop ..) | .eff (.popN ..) | .eff (.resize ..)
          | .eff (.clear ..) | .eff (.replace ..) =>
              unless (lower module).profile == .shrink do throw "operation requires core-shrink"
          | .term (.abort kind _) =>
              if (lower module).profile != .shrink && kind ∈ [.popEmpty, .popNRange, .resizeNegative, .resizeFill, .capacity] then
                throw s!"abort kind {kind.tag.quote} requires core-shrink"
          | _ => pure ()
      checkAll info.f.params fun ty => do
        unless ty.paramOk do throw "a parameter has a type no parameter may have"
      checkAll info.f.results fun ty => do
        unless !ty.isRefSlice do throw "a reference-to-slice type is only valid for a parameter"
      checkAll info.f.slots.toList.zipIdx fun (slot, position) => do
        unless slot.var == position do
          throw s!"slot {position} must describe variable {position}, found variable {slot.var}"
        let parameterRefSliceSlot := slot.var < info.f.params.length &&
          info.f.params[slot.var]? == some slot.ty && slot.ty.isRefSlice
        unless slot.ty.storable || parameterRefSliceSlot do
          throw s!"the slot of variable {slot.var} has a type no variable may have"
      checkAll info.f.blocks.toList fun block =>
        checkAll block.insts (checkInstTypes info.f { (lower module).tyEnv info.f with vals := info.vt } info.vt)
      match info.f.blocks[0]? with
      | some block =>
        unless block.params.map (·.2) == info.f.params.map VTy.data do
          throw "the parameters of block 0 are not the function's parameters"
      | none => throw "no blocks") = (Except.ok () : Except String Unit) := by
    rw [profiles]
    simp only [bind, Except.bind]
    rw [parameters]
    rw [results]
    simp only [bind, Except.bind, pure, Except.pure, throw] at slots ⊢
    rw [slots, rows, entryAt]
    simp [entryTypes]
  exact congrArg (asCheck .v010 info.label) checked

private theorem profile_shrink (instruction : Inst) : EmittedProfileInst .shrink instruction := by
  cases instruction with
  | «def» value op => cases op <;> simp [EmittedProfileInst]
  | eff effect => cases effect <;> simp [EmittedProfileInst]
  | term term => cases term <;> simp [EmittedProfileInst]

theorem lower_info_checkTypes_shrink_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (profile : module.profile = .shrink)
    {info : FnInfo} (member : info ∈ (lower module).infos) :
    checkTypes (lower module) info.label info.f info.vt = .ok () := by
  apply check_types_of_instructions accepted member
  · intro block blockMember instruction instructionMember
    rw [profile]
    exact profile_shrink instruction
  · exact fun block blockMember instruction instructionMember =>
      lower_instructions_typed_of_accepted accepted member blockMember instructionMember

theorem lower_checkTypes_shrink_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) (profile : module.profile = .shrink) :
    (checkAll (lower module).infos fun info => checkTypes (lower module) info.label info.f info.vt) = .ok () := by
  apply Origins.checkAll_ok_of_forall
  exact fun info member => lower_info_checkTypes_shrink_of_accepted accepted profile member

theorem lower_info_checkTypes_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {info : FnInfo}
    (member : info ∈ (lower module).infos) :
    checkTypes (lower module) info.label info.f info.vt = .ok () := by
  apply check_types_of_instructions accepted member
  · obtain ⟨_, source⟩ := lower_info_source accepted member
    rcases source with ⟨contextIndex, context, impl, contextAt, implAt, same⟩ |
      ⟨globalIndex, global, globalAt, same⟩
    · rw [same]
      exact lowerContextAt_functionProfile_of_accepted accepted implAt
    · rw [same]
      exact lowerGlobal_functionProfile_of_accepted accepted globalAt
  · exact fun block blockMember instruction instructionMember =>
      lower_instructions_typed_of_accepted accepted member blockMember instructionMember

theorem lower_checkTypes_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    (checkAll (lower module).infos fun info => checkTypes (lower module) info.label info.f info.vt) = .ok () := by
  apply Origins.checkAll_ok_of_forall
  exact fun info member => lower_info_checkTypes_of_accepted accepted member

end Goose.Lower.Validation
