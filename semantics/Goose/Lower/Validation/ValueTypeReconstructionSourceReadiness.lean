import Goose.Lower.Validation.ValueTypeReconstructionOperations
import Goose.Lower.Validation.ValueTypeReconstructionPrefix
import Goose.Lower.Validation.ExpressionTypingGraphFrame

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def SnapshotAuthorityRetained (site : LS) (module : GIR.Module)
    (func : Func) (owner : ValueId) : Prop :=
  ∀ types : Array (Option VTy), types.size = func.numValues →
    (∀ value, value < site.vals.size → site.vals[value]? = types[value]?) →
    ∃ authorized, ContentsClosed (module.globals.map (·.kind)) module.structs
      func types authorized ∧ authorized owner

theorem snapshotAuthorityRetained_of_graph
    {site : LS} {module : GIR.Module} {func : Func} {owner : ValueId}
    {recorded : Array (Option VTy)} {authorized : ValueId → Prop}
    (closed : ContentsClosed (module.globals.map (·.kind)) module.structs func recorded authorized)
    (bounded : ∀ value, authorized value → value < site.vals.size)
    (retained : ∀ value, authorized value → recorded[value]? = site.vals[value]?)
    (member : authorized owner) : SnapshotAuthorityRetained site module func owner := by
  intro types size prefixTypes
  exact ⟨authorized, closed.replace_types (fun value allowed =>
    (retained value allowed).trans (prefixTypes value (bounded value allowed))), member⟩

theorem reconstructionReady_of_source_emission
    {module : GIR.Module} {func : Func} {le : LEnv} {site : LS}
    {types : ValueId → VTy} {value : ValueId} {op : Op}
    (slots : func.slots = le.slots)
    (globals : (module.globals.map fun g => (g.ty, g.kind)) = le.globals)
    (sigs : (module.funcs.map fun h => (h.params, h.results)) = le.sigs)
    (structs : module.structs = le.mod.structs) (profile : module.profile = le.mod.profile)
    (dense : site.DenseDefinitions) (extension : ExtT site func.blocks)
    (operandBounds : ∀ inst ∈ site.insts, ∀ operand ∈ inst.uses, operand < site.vals.size)
    (fresh : value = site.vals.size) (bound : value < func.numValues)
    (recorded : ∀ operand, operand < site.vals.size →
      site.vals[operand]? = some (some (types operand)))
    (typed : op.resultTy (tyEnv le site) = .ok (types value))
    (ordered : ∀ operand ∈ op.uses, operand < value)
    (authority : ∀ mode owner, op = .snapshot mode owner →
      (tyEnv le site).contentsWritable owner = some true →
      SnapshotAuthorityRetained site module func owner) :
    ReconstructionReady module func types id value op := by
  apply reconstructionReady_of_emission
    (emitted := tyEnv le site) slots globals sigs structs profile typed
  · intro operand member
    have earlier := ordered operand member
    exact ⟨Nat.lt_trans earlier bound, earlier, recorded operand (by rwa [← fresh])⟩
  · intro roundStart roundSize roundFront mode owner snapshot
    have ownerUse : owner ∈ op.uses := by simp [snapshot, Op.uses]
    have oldBound : owner < site.vals.size := by rw [← fresh]; exact ordered owner ownerUse
    have newBound := Nat.lt_trans (ordered owner ownerUse) bound
    have tables : ∀ operand, operand < site.vals.size → site.vals[operand]? = roundStart[operand]? := by
      intro operand previous
      exact (recorded operand previous).trans
        (roundFront operand (Nat.lt_trans (by rwa [← fresh] at previous) bound)
          (by simpa only [id_eq, fresh] using previous)).symm
    obtain ⟨writable, oldContents⟩ := tyEnv_contentsWritable_present le dense oldBound
    cases writable with
    | false =>
      have globalKinds : module.globals.map (·.kind) = le.globals.map (·.2) := by
        rw [← globals]
        simp only [Array.map_map, Function.comp_def]
      have retained := readonly_snapshot_contents_retained dense extension slots.symm
        globalKinds structs operandBounds tables oldBound newBound oldContents
      exact retained.trans oldContents.symm
    | true =>
      obtain ⟨authorized, closed, member⟩ := authority mode owner snapshot oldContents roundStart roundSize tables
      exact (permissionContents_option_true closed member).trans oldContents.symm

end Goose.Lower.Validation
