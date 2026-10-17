import Goose.Lower.Validation.SummaryPreservationEmit
import Goose.Lower.Validation.SummaryPreservationRootBounds

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem emitDef_represented_witness {res : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper : Prov} {ls : LS} {le : LEnv} {scopeCount : Nat}
    {block : BlockId} {op : Op} {sourceRoots : List RootRef}
    (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size)
    (witness : BuilderRootWitness res vt func upper ls)
    (uses : ∀ used ∈ op.uses, used < ls.vals.size)
    (roots : RootsRepresent func (rootsOfDef res vt func upper ls.vals.size op) sourceRoots) :
    ∃ next : Prov, BuilderRootWitness res vt func next (emitDef op le ls).2 ∧
      RootsRepresent func (rootsAt next.vals (emitDef op le ls).1) sourceRoots ∧
      next.slots = upper.slots := by
  obtain ⟨next, nextWitness, resultRoots, slots⟩ := emitDef_root_witness symbols current
    blockBound witness uses (show emitDef op le ls = ((emitDef op le ls).1, (emitDef op le ls).2) from rfl)
  refine ⟨next, nextWitness, ?_, slots⟩
  rw [resultRoots]
  have value : (emitDef op le ls).1 = ls.vals.size := by rw [emitDef_run op le current]
  simpa only [value] using roots

theorem lowerExpr_lit_root_witness {res : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper : Prov} {ls : LS} {le : LEnv} {scopeCount : Nat}
    {block : BlockId} (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness res vt func upper ls)
    (ty : IntTy) (value : Int) :
    ∃ next : Prov, BuilderRootWitness res vt func next (lowerExpr (.lit ty value) le ls).2 ∧
      RootsRepresent func (rootsAt next.vals (lowerExpr (.lit ty value) le ls).1) [] ∧
      next.slots = upper.slots := by
  exact emitDef_represented_witness symbols current blockBound witness
    (by simp [Op.uses]) (rootsRepresent_empty func [])

theorem lowerExpr_bool_root_witness {res : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper : Prov} {ls : LS} {le : LEnv} {scopeCount : Nat}
    {block : BlockId} (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness res vt func upper ls)
    (value : Bool) :
    ∃ next : Prov, BuilderRootWitness res vt func next (lowerExpr (.bool value) le ls).2 ∧
      RootsRepresent func (rootsAt next.vals (lowerExpr (.bool value) le ls).1) [] ∧
      next.slots = upper.slots := by
  exact emitDef_represented_witness symbols current blockBound witness
    (by simp [Op.uses]) (rootsRepresent_empty func [])

theorem lowerPlace_var_root_witness {res : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper : Prov} {ls : LS} {le : LEnv} {scopeCount : Nat}
    {block : BlockId} (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness res vt func upper ls)
    (varId : VarId) :
    ∃ next : Prov, BuilderRootWitness res vt func next (lowerPlace (.var varId) le ls).2 ∧
      RootsRepresent func (rootsAt next.vals (lowerPlace (.var varId) le ls).1) [.local varId] ∧
      next.slots = upper.slots := by
  exact emitDef_represented_witness symbols current blockBound witness
    (by simp [Op.uses]) (rootsRepresent_local func varId)

theorem lowerPlace_global_root_witness {res : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {upper : Prov} {ls : LS} {le : LEnv} {scopeCount : Nat}
    {block : BlockId} (symbols : ls.SymbolWF le scopeCount) (current : ls.cur = some block)
    (blockBound : block < ls.blocks.size) (witness : BuilderRootWitness res vt func upper ls)
    (global : GlobalId) :
    ∃ next : Prov, BuilderRootWitness res vt func next (lowerPlace (.global global) le ls).2 ∧
      RootsRepresent func (rootsAt next.vals (lowerPlace (.global global) le ls).1) [.global global] ∧
      next.slots = upper.slots := by
  exact emitDef_represented_witness symbols current blockBound witness
    (by simp [Op.uses]) (rootsRepresent_global func global)

end Goose.Lower.Validation.SummaryPreservation
