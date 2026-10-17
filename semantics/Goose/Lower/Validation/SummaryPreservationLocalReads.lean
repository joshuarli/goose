import Goose.Lower.Validation.SummaryPreservationLeaves
import Goose.Lower.Validation.SummaryPreservationReads

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem lowerExpr_read_var_root_witness {res : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {upper : Prov} {ls : LS} {le : LEnv}
    {scopeCount : Nat} {block : BlockId} {env : PEnv} {varId : VarId}
    {localVar : LocalVar} {sourceRoots : List RootRef} {start finish : RState}
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness res vt func upper ls)
    (slotBound : varId < le.slots.size)
    (checked : checkAnnotationShape env.mod env.impl env.ctx = .ok ())
    (variableRow : env.impl.vars[varId]? = some localVar)
    (source : readRoots env (.var varId) start = .ok (sourceRoots, finish))
    (slotRoots : RootsRepresent func (rootsAt upper.slots varId) (env.ann varId |>.getD [])) :
    ∃ next : Prov, BuilderRootWitness res vt func next (lowerExpr (.read (.var varId)) le ls).2 ∧
      RootsRepresent func (rootsAt next.vals (lowerExpr (.read (.var varId)) le ls).1) sourceRoots ∧
      next.slots = upper.slots := by
  let address := lowerPlace (.var varId) le ls
  obtain ⟨middle, middleWitness, addressRoots, sameSlots⟩ :=
    lowerPlace_var_exact_root_witness symbols current blockBound witness varId
  have middleSymbols := lowerPlace_var_symbols symbols current blockBound varId slotBound
  have middleCurrent : address.2.cur = some block := by
    dsimp [address, lowerPlace]
    rw [emitDef_run _ _ current]
    exact current
  have middleBlockBound : block < address.2.blocks.size := by
    dsimp [address, lowerPlace]
    rw [emitDef_run _ _ current]
    simpa using blockBound
  have addressBound : address.1 < address.2.vals.size := by
    dsimp [address, lowerPlace]
    rw [emitDef_run _ _ current]
    simp
  have represented : RootsRepresent func
      (rootsOfDef res vt func middle address.2.vals.size (.load address.1)) sourceRoots := by
    apply readRoots_variable_load_represent_of_annotations checked variableRow source addressRoots
    rw [sameSlots]
    exact slotRoots
  obtain ⟨next, nextWitness, roots, slots⟩ := emitDef_represented_witness middleSymbols
    middleCurrent middleBlockBound middleWitness (op := .load address.1)
    (by simpa [Op.uses] using addressBound) represented
  refine ⟨next, ?_, ?_, slots.trans sameSlots⟩
  · exact nextWitness
  · exact roots

end Goose.Lower.Validation.SummaryPreservation
