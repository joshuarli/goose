import Goose.Lower.Validation.ReplacementSourceCertificates
import Goose.Lower.Validation.FreshRunSourceAssignment
import Goose.Lower.Validation.ExpressionTypingGenerated

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem AcceptedReplacementSite.owner_fresh {le : LEnv} {state : LS}
    {owner value : ValueId} {origin : OriginId}
    (witness : AcceptedReplacementSite le state owner value origin)
    {module : GIR.Module} {func : Func}
    (builder : EmittedBuilder le initState state)
    (blocks : func.blocks = finishBlocks state.blocks) (slots : func.slots = le.slots)
    (globals : (module.globals.map fun global => (global.ty, global.kind)) = le.globals)
    (sigs : (module.funcs.map fun signature => (signature.params, signature.results)) = le.sigs)
    (structs : module.structs = le.mod.structs) (profile : module.profile = le.mod.profile)
    (graphs : MutableSnapshotGraphs module func state)
    (closed : ∀ body ∈ state.blocks.toList, ClosedBlock body) :
    (∃ element, ownerTy (func.valueTypes module) owner = some (.grow element) ∨
      ownerTy (func.valueTypes module) owner = some (.growshrink element)) ∧
      (freshRuns func (func.valueTypes module))[value]? = some true := by
  have ownerRun : lowerPlace witness.place
      (lowerEnv witness.sourceEnv.mod witness.sourceEnv.vars witness.results)
      witness.initial = (witness.site.owner, witness.site.addressed) := by
    simpa only [witness.environment] using witness.site.addressRun
  have rhsRun : lowerExpr witness.rhs
      (lowerEnv witness.sourceEnv.mod witness.sourceEnv.vars witness.results)
      witness.site.cleared = (witness.site.value, witness.site.captured) := by
    simpa only [witness.environment] using witness.site.rhsRun
  have sourceBuilder : EmittedBuilder
      (lowerEnv witness.sourceEnv.mod witness.sourceEnv.vars witness.results) initState state := by
    simpa only [witness.environment] using builder
  have sourceSlots : func.slots =
      (lowerEnv witness.sourceEnv.mod witness.sourceEnv.vars witness.results).slots := by
    simpa only [witness.environment] using slots
  have sourceGlobals : (module.globals.map fun global => (global.ty, global.kind)) =
      (lowerEnv witness.sourceEnv.mod witness.sourceEnv.vars witness.results).globals := by
    simpa only [witness.environment] using globals
  have sourceSigs : (module.funcs.map fun signature => (signature.params, signature.results)) =
      (lowerEnv witness.sourceEnv.mod witness.sourceEnv.vars witness.results).sigs := by
    simpa only [witness.environment] using sigs
  have sourceStructs : module.structs = witness.sourceEnv.mod.structs := by
    simpa only [← witness.environment, lowerEnv] using structs
  have sourceProfile : module.profile = witness.sourceEnv.mod.profile := by
    simpa only [← witness.environment, lowerEnv] using profile
  obtain ⟨info, element, childStart, placeSource, ownerShape, _, _, _, _⟩ :=
    tyStmt_assignWhole_children witness.accepted
  have clearedLive := (dead_lowerExpr witness.rhs).live_before witness.site.rhsRun witness.live
  have addressedLive := (dead_emitEffect (.clear witness.site.owner (some origin))).live_before
    witness.site.clearRun clearedLive
  obtain ⟨mode, typed⟩ := lowerPlace_generated_typed witness.place placeSource ownerRun addressedLive witness.generated
  have finalRow := witness.types witness.site.owner (.data (.ref mode info.ty)) typed
  rw [witness.owner_eq] at finalRow
  have retained := valueTypes_eq_retained_of_source_graphs builder blocks slots globals sigs structs profile graphs
  constructor
  · refine ⟨element, ?_⟩
    rcases ownerShape with grow | growshrink
    · exact Or.inl (by simp [ownerTy, retained, finalRow, grow])
    · exact Or.inr (by simp [ownerTy, retained, finalRow, growshrink])
  · have fresh := assignWhole_freshRuns_reconstructed witness.accepted rhsRun witness.live
      witness.cleared_generated witness.framed witness.captured_extension closed
      sourceBuilder blocks sourceSlots sourceGlobals sourceSigs sourceStructs sourceProfile graphs
    simpa only [witness.value_eq] using fresh

#print axioms AcceptedReplacementSite.owner_fresh

end Goose.Lower.Validation
