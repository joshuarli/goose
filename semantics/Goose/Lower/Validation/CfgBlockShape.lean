import Goose.Lower.Validation.CfgCurrentOpen

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def ShapedBlocks (state : LS) : Prop :=
  ∀ (block : BlockId) (body : BlockB), state.blocks[block]? = some body → OpenBlock body ∨ ClosedBlock body

theorem ShapedBlocks.of_blocks {before after : LS} (shaped : ShapedBlocks before)
    (same : after.blocks = before.blocks) : ShapedBlocks after := by
  intro block body row
  exact shaped block body (same ▸ row)

theorem ShapedBlocks.modify {state : LS} (shaped : ShapedBlocks state) (block : BlockId)
    (update : BlockB → BlockB)
    (updated : ∀ body, state.blocks[block]? = some body →
      OpenBlock (update body) ∨ ClosedBlock (update body)) :
    ShapedBlocks { state with blocks := state.blocks.modify block update } := by
  intro index body row
  change (state.blocks.modify block update)[index]? = some body at row
  simp only [Array.getElem?_modify] at row
  split at row
  · rename_i same
    subst index
    cases old : state.blocks[block]? with
    | none => simp [old] at row
    | some previous =>
      simp only [old, Option.map_some, Option.some.injEq] at row
      subst body
      exact updated previous old
  · exact shaped index body row

theorem ShapedBlocks.emitDef {state : LS} (shaped : ShapedBlocks state)
    (currentOpen : CurrentOpen state) (op : Op) (env : LEnv) :
    ShapedBlocks (Goose.Lower.emitDef op env state).2 := by
  cases current : state.cur with
  | none => simpa [Goose.Lower.emitDef, current, bind_run, get_apply, pure_run] using shaped
  | some block =>
    rw [emitDef_run op env current]
    exact ShapedBlocks.of_blocks
      (shaped.modify block (fun body => { body with insts := body.insts.push (.def state.vals.size op) }) (by
      intro body row
      exact Or.inl (open_push_def (currentOpen.row current row) _ _))) rfl

theorem ShapedBlocks.emitEffect {state : LS} (shaped : ShapedBlocks state)
    (currentOpen : CurrentOpen state) (effect : Effect) (env : LEnv) :
    ShapedBlocks (Goose.Lower.emitEffect effect env state).2 := by
  cases current : state.cur with
  | none => simpa [Goose.Lower.emitEffect, curBlock, current, bind_run, get_apply, pure_run] using shaped
  | some block =>
    rw [emitEffect_run effect env current]
    apply shaped.modify block (fun body => { body with insts := body.insts.push (.eff effect) })
    intro body row
    exact Or.inl (open_push_effect (currentOpen.row current row) _)

theorem ShapedBlocks.emitTerm {state : LS} (shaped : ShapedBlocks state)
    (currentOpen : CurrentOpen state) (term : Term) (env : LEnv) :
    ShapedBlocks (Goose.Lower.emitTerm term env state).2 := by
  cases current : state.cur with
  | none => simpa [Goose.Lower.emitTerm, curBlock, current, bind_run, get_apply, pure_run] using shaped
  | some block =>
    rw [emitTerm_run term env current]
    exact ShapedBlocks.of_blocks
      (shaped.modify block (fun body => { body with insts := body.insts.push (.term term) }) (by
      intro body row
      exact Or.inr (open_push_term (currentOpen.row current row) _))) rfl

theorem ShapedBlocks.patchTerm {state : LS} (shaped : ShapedBlocks state)
    (block : BlockId) (openTarget : ∀ body, state.blocks[block]? = some body → OpenBlock body)
    (term : Term) (env : LEnv) : ShapedBlocks (Goose.Lower.patchTerm block term env state).2 := by
  rw [patchTerm_run]
  apply shaped.modify block (fun body => { body with insts := body.insts.push (.term term) })
  intro body row
  exact Or.inr (open_push_term (openTarget body row) _)

theorem ShapedBlocks.newBlock {state : LS} (shaped : ShapedBlocks state)
    (types : List VTy) (env : LEnv) : ShapedBlocks (Goose.Lower.newBlock types env state).2 := by
  intro index body row
  change (state.blocks.push _)[index]? = some body at row
  rw [Array.getElem?_push] at row
  split at row
  · have same := Option.some.inj row
    subst body
    exact Or.inl (open_empty _)
  · exact shaped index body row

theorem ShapedBlocks.setCur {state : LS} (shaped : ShapedBlocks state)
    (current : Option BlockId) (env : LEnv) : ShapedBlocks (Goose.Lower.setCur current env state).2 :=
  shaped.of_blocks rfl

def AllClosed (state : LS) : Prop :=
  ∀ (block : BlockId) (body : BlockB), state.blocks[block]? = some body → ClosedBlock body

theorem allClosed_of_shaped_noOpen {state : LS} (shaped : ShapedBlocks state)
    (noOpen : ∀ (block : BlockId) (body : BlockB), state.blocks[block]? = some body → ¬ OpenBlock body) : AllClosed state := by
  intro block body row
  exact (shaped block body row).resolve_left (noOpen block body row)

theorem allClosed_blocks {state : LS} (closed : AllClosed state) :
    ∀ body ∈ state.blocks.toList, ClosedBlock body := by
  intro body member
  obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
  exact closed index body row

end Goose.Lower.Validation
