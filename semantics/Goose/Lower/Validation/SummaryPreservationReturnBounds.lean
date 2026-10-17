import Goose.Lower.Validation.SummaryPreservationReplayBuilder
import Goose.Lower.Validation.SummaryPreservationRefinedResults

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def BuilderReturnsBound (upper : Prov) (target : List RootRef) (state : LS) : Prop :=
  ∀ value origin, .term (.ret [value] origin) ∈ state.insts →
    ∀ root ∈ rootsAt upper.vals value, root ∈ target

theorem BuilderReturnsBound.retained {before after : LS} {oldUpper newUpper : Prov}
    {target : List RootRef} {le : LEnv} {scopeCount : Nat}
    (prior : BuilderReturnsBound oldUpper target before)
    (symbols : before.SymbolWF le scopeCount) (size : oldUpper.vals.size = before.vals.size)
    (prefixRoots : ∀ index, index < oldUpper.vals.size → rootsAt newUpper.vals index = rootsAt oldUpper.vals index)
    (returns : ∀ value origin, .term (.ret [value] origin) ∈ after.insts →
      .term (.ret [value] origin) ∈ before.insts) :
    BuilderReturnsBound newUpper target after := by
  intro value origin member root rootMember
  have original := returns value origin member
  have valueBound := (symbols.instructions _ original).uses value (by simp [Inst.uses, Term.uses])
  rw [prefixRoots value (by simpa only [size] using valueBound)] at rootMember
  exact prior value origin original root rootMember

theorem BuilderReturnsBound.appendInst {state : LS} {upper : Prov} {target : List RootRef}
    {block : BlockId} {inst : Inst} (prior : BuilderReturnsBound upper target state)
    (bound : block < state.blocks.size)
    (added : ∀ value origin, inst = .term (.ret [value] origin) →
      ∀ root ∈ rootsAt upper.vals value, root ∈ target) :
    BuilderReturnsBound upper target (state.appendInst block inst) := by
  intro value origin member root rootMember
  have membership : .term (.ret [value] origin) ∈ state.insts ∨ .term (.ret [value] origin) = inst := by
    simpa using (LS.insts.modifyPush bound inst).mem_iff.mp member
  rcases membership with original | same
  · exact prior value origin original root rootMember
  · exact added value origin (by simpa using same.symm) root rootMember

theorem BuilderReturnsBound.emitTerm {state : LS} {upper : Prov} {target : List RootRef}
    {le : LEnv} (prior : BuilderReturnsBound upper target state)
    (current : state.CurrentBlocks) (term : Term)
    (added : ∀ value origin, term = .ret [value] origin →
      ∀ root ∈ rootsAt upper.vals value, root ∈ target) :
    BuilderReturnsBound upper target (Goose.Lower.emitTerm term le state).2 := by
  cases active : state.cur with
  | none => rw [emitTerm_none _ _ active]; exact prior
  | some block =>
    have generated := prior.appendInst (current block active) (inst := .term term) (by
      intro value origin same
      exact added value origin (Inst.term.inj same))
    rw [emitTerm_run _ _ active]
    exact generated

theorem returnedRoots_below_upper {func : Func} {actual upper : Prov} {target : List RootRef}
    (bounded : ProvenanceBelow actual upper)
    (returns : ∀ block ∈ func.blocks.toList, ∀ value origin, .term (.ret [value] origin) ∈ block.insts →
      ∀ root ∈ rootsAt upper.vals value, root ∈ target) :
    ∀ root ∈ func.returnedRoots actual, root ∈ target := by
  unfold Func.returnedRoots
  rw [← Array.foldl_toList]
  apply List.foldlRecOn (motive := fun roots => ∀ root ∈ roots, root ∈ target)
    func.blocks.toList _ (by simp)
  intro accumulated prior block blockMember
  apply List.foldlRecOn (motive := fun roots => ∀ root ∈ roots, root ∈ target)
    block.insts _ prior
  intro accumulated prior inst instMember
  cases inst with
  | «def» _ _ => exact prior
  | eff _ => exact prior
  | term term =>
    cases term <;> try exact prior
    rename_i values origin
    cases values with
    | nil => exact prior
    | cons value rest =>
      cases rest with
      | nil =>
        intro root member
        rcases mem_unionRoots_iff.mp member with old | returned
        · exact prior root old
        · exact returns block blockMember value origin instMember root (bounded.vals _ _ returned)
      | cons _ _ => exact prior

theorem returnedRoots_finishBlocks_below {func : Func} {state : LS} {actual upper : Prov}
    {target : List RootRef} (bounded : ProvenanceBelow actual upper)
    (returns : BuilderReturnsBound upper target state) :
    ∀ root ∈ ({ func with blocks := finishBlocks state.blocks }).returnedRoots actual, root ∈ target := by
  apply returnedRoots_below_upper bounded
  intro block blockMember value origin instMember root rootMember
  have mapped : block ∈ state.blocks.toList.map (fun builder =>
      ({ params := builder.params, insts := builder.insts.toList } : GIR.Block)) := by
    simpa only [finishBlocks, Array.toList_map] using blockMember
  obtain ⟨builder, builderMember, rfl⟩ := List.mem_map.mp mapped
  have member : .term (.ret [value] origin) ∈ state.insts :=
    List.mem_flatMap.mpr ⟨builder, builderMember, instMember⟩
  exact returns value origin member root rootMember

end Goose.Lower.Validation.SummaryPreservation
