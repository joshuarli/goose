import Goose.Lower.Validation.ValidationTypedModuleEmission
import Goose.Lower.Validation.ValidationTypedModuleFunctions
import Goose.Lower.Validation.EmittedMetadataAcceptance

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lower_instructions_typed_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) {info : FnInfo}
    (member : info ∈ (lower module).infos) {block : GIR.Block}
    (blockMember : block ∈ info.f.blocks.toList) {instruction : Inst}
    (instructionMember : instruction ∈ block.insts) :
    checkInstTypes info.f { (lower module).tyEnv info.f with vals := info.vt }
      info.vt instruction = .ok () := by
  by_cases definition : ∃ value op, instruction = Inst.def value op
  · obtain ⟨value, op, rfl⟩ := definition
    exact lower_definitions_typed_of_accepted accepted member blockMember instructionMember
  · have nondefinition : ∀ value op, instruction ≠ Inst.def value op := by
      intro value op same
      exact definition ⟨value, op, same⟩
    obtain ⟨tables, source⟩ := lower_info_source accepted member
    rw [tables]
    rcases source with ⟨contextIndex, context, impl, contextAt, implAt, same⟩ |
      ⟨globalIndex, global, globalAt, same⟩
    · rw [same] at blockMember ⊢
      rw [lowerContext_valueTypes_of_accepted (context := context) accepted implAt]
      exact (lowerContext_metadata_of_accepted accepted contextAt implAt).finishedNondefinition
        (cfg_context_blocks module context impl) rfl blockMember instructionMember nondefinition _ rfl rfl
    · rw [same] at blockMember ⊢
      rw [lowerGlobal_valueTypes_of_accepted accepted globalAt]
      exact (lowerGlobal_metadata_of_accepted accepted globalAt).finishedNondefinition
        (cfg_global_blocks module global) rfl blockMember instructionMember nondefinition _ rfl rfl

theorem lower_instructionTypeChecks_of_accepted {module : Core.Module}
    (accepted : Core.validate module = .ok ()) :
    (checkAll (lower module).infos fun info =>
      checkAll info.f.blocks.toList fun block =>
        checkAll block.insts (checkInstTypes info.f { (lower module).tyEnv info.f with vals := info.vt } info.vt)) =
          (Except.ok () : Except String Unit) := by
  apply Origins.checkAll_ok_of_forall
  intro info member
  apply Origins.checkAll_ok_of_forall
  intro block blockMember
  apply Origins.checkAll_ok_of_forall
  intro instruction instructionMember
  exact lower_instructions_typed_of_accepted accepted member blockMember instructionMember

end Goose.Lower.Validation
