import Goose.Lower.Validation.EmittedMetadataSourceContracts

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem EmittedMetadata.finishedInst {le : LEnv} {state : LS}
    (metadata : EmittedMetadata le state) {func : Func}
    (blocks : func.blocks = finishBlocks state.blocks) {block : GIR.Block}
    (blockMember : block ∈ func.blocks.toList) {inst : Inst} (instructionMember : inst ∈ block.insts) :
    EmittedMetadataInst le state inst := by
  rw [blocks, finishBlocks, Array.toList_map] at blockMember
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp blockMember
  exact metadata inst (List.mem_flatMap.mpr ⟨original, originalMember, instructionMember⟩)

theorem EmittedMetadata.finishedEffect {le : LEnv} {state : LS}
    (metadata : EmittedMetadata le state) {func : Func}
    (blocks : func.blocks = finishBlocks state.blocks) {block : GIR.Block}
    (blockMember : block ∈ func.blocks.toList) {effect : Effect}
    (instructionMember : Inst.eff effect ∈ block.insts) (env : TyEnv)
    (slots : env.slots = le.slots) (values : env.vals = state.vals) :
    checkEffectTypes env effect = .ok () :=
  EmittedEffectTyped.checkWith (metadata.finishedInst blocks blockMember instructionMember) env slots values

theorem EmittedMetadata.finishedTerm {le : LEnv} {state : LS}
    (metadata : EmittedMetadata le state) {func : Func}
    (blocks : func.blocks = finishBlocks state.blocks) (results : func.results = le.results) {block : GIR.Block}
    (blockMember : block ∈ func.blocks.toList) {term : Term}
    (instructionMember : Inst.term term ∈ block.insts) (env : TyEnv) (values : env.vals = state.vals) :
    checkTermTypes func env term = .ok () :=
  EmittedTermTyped.checkWith (le := le) (metadata.finishedInst blocks blockMember instructionMember) func results env values

theorem EmittedMetadata.finishedNondefinition {le : LEnv} {state : LS}
    (metadata : EmittedMetadata le state) {func : Func}
    (blocks : func.blocks = finishBlocks state.blocks) (results : func.results = le.results) {block : GIR.Block}
    (blockMember : block ∈ func.blocks.toList) {inst : Inst} (instructionMember : inst ∈ block.insts)
    (nondefinition : ∀ value op, inst ≠ Inst.def value op) (env : TyEnv)
    (slots : env.slots = le.slots) (values : env.vals = state.vals) :
    checkInstTypes func env state.vals inst = .ok () := by
  cases inst with
  | «def» value op => exact (nondefinition value op rfl).elim
  | eff effect => exact metadata.finishedEffect blocks blockMember instructionMember env slots values
  | term term => exact metadata.finishedTerm blocks results blockMember instructionMember env values

end Goose.Lower.Validation
