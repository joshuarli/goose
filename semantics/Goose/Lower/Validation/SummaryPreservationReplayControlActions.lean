import Goose.Lower.Validation.SummaryPreservationReplayLoopsBuilder
import Goose.Lower.Validation.SummaryPreservationReplayTerm
import Goose.Lower.Validation.SummaryPreservationReplayMutationsEmit

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem leaveAll (scopes : List ScopeId)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (bounds : ∀ scope ∈ scopes, scope < scopeCount) :
    ReplayBuilder module results vt func target le scopeCount slots
      (Goose.Lower.leaveAll scopes le ls).2 upper := by
  induction scopes generalizing ls with
  | nil => exact ready
  | cons scope rest ih =>
    have left := ready.emitEffect_live (.leave scope)
      (by
        intro _
        apply Inst.SymbolsWithin.eff
        · simp [Effect.uses]
        · simp [Effect.origin]
        · simpa [Effect.SymbolRefsValid] using bounds scope (by simp))
      (by intros; trivial)
      (by intros; exact effectRefinement_empty func target)
    exact ih left (fun next member => bounds next (by simp [member]))

theorem leaveTo (depth : Nat)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (bounds : ∀ scope ∈ ls.stack, scope < scopeCount) :
    ReplayBuilder module results vt func target le scopeCount slots
      (Goose.Lower.leaveTo depth le ls).2 upper := by
  simpa only [Goose.Lower.leaveTo, bind_run, get_apply] using
    ready.leaveAll (ls.stack.take (ls.stack.length - depth))
      (fun scope member => bounds scope (List.mem_of_mem_take member))

theorem patchTerm (block : BlockId) (term : Term)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (blockBound : block < ls.blocks.size)
    (symbols : Inst.SymbolsWithin le scopeCount ls.vals.size ls.blocks.size (.term term))
    (closed : InstructionRootsClosed results vt {func with blocks := finishBlocks ls.blocks} upper (.term term))
    (delta : EffectRefinement func (func.effectStep module vt upper {} (.term term)) target) :
    ReplayBuilder module results vt func target le scopeCount slots
      (Goose.Lower.patchTerm block term le ls).2 upper := by
  rw [patchTerm_run]
  have next := appendInst_refined_witness blockBound ready.roots ready.effects closed delta
  refine ⟨next.1, next.2, ready.symbols.patchTerm blockBound symbols, ?_, ready.slotsEq, ready.recipes.same rfl⟩
  intro current row
  simpa [LS.appendInst] using ready.current current row

theorem patchBrs0 (join : BlockId) (ends : List BlockId)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (joinBound : join < ls.blocks.size) (bounds : ∀ block ∈ ends, block < ls.blocks.size) :
    ReplayBuilder module results vt func target le scopeCount slots
      (Goose.Lower.patchBrs0 join ends le ls).2 upper := by
  induction ends generalizing ls with
  | nil => exact ready
  | cons block rest ih =>
    have patched := ready.patchTerm block (.br join []) (bounds block (by simp))
      (by
        apply Inst.SymbolsWithin.term
        · simp [Term.uses]
        · simp [Term.origin]
        · simpa [Term.successors] using joinBound)
      (by intro destination lookup pair member; simp at member)
      (effectRefinement_empty func target)
    exact ih patched (by simpa [patchTerm_run] using joinBound)
      (fun next member => by simpa [patchTerm_run] using bounds next (by simp [member]))

theorem joinArms (yes no : Option BlockId)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (yesBound : ∀ block, yes = some block → block < ls.blocks.size)
    (noBound : ∀ block, no = some block → block < ls.blocks.size) :
    ReplayBuilder module results vt func target le scopeCount slots
      (Goose.Lower.joinArms yes no le ls).2 upper := by
  let edges := yes.toList ++ no.toList
  have allocated := ready.loopEmptyBlock
  have patched := allocated.patchBrs0 ls.blocks.size edges
    (by simp [newBlock0_run]) (by
      intro block member
      simp only [edges, List.mem_append, Option.mem_toList] at member
      rcases member with first | second
      · exact Nat.lt_trans (yesBound block first) (by simp [newBlock0_run])
      · exact Nat.lt_trans (noBound block second) (by simp [newBlock0_run]))
  have selected := patched.setCur (some ls.blocks.size) (by
    intro block row
    cases row
    have size := patchBrs0_size (jb := ls.blocks.size) edges (le := le) (ls1 := (newBlock [] le ls).2) rfl
    rw [← size]
    simp [newBlock0_run])
  cases yes <;> cases no
  · simpa [Goose.Lower.joinArms, bind_run] using ready.setCur none (by simp)
  all_goals simpa only [Goose.Lower.joinArms, bind_run, newBlock0_run, setCur_run, edges] using selected

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
