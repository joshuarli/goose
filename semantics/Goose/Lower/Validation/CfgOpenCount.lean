import Goose.Lower.Validation.CfgBlockShape

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def OpenCount (state : LS) : Nat :=
  state.blocks.countP fun body => (cfgBlock body).terms.isEmpty

theorem allClosed_of_shaped_count {state : LS} (shaped : ShapedBlocks state)
    (count : OpenCount state = 0) : AllClosed state := by
  apply allClosed_of_shaped_noOpen shaped
  intro block body row openBody
  have absent := Array.countP_eq_zero.mp count body (Array.mem_of_getElem? row)
  exact absent (List.isEmpty_iff.mpr openBody)

theorem openCount_modify {state : LS} {block : BlockId} {body : BlockB}
    (row : state.blocks[block]? = some body) (update : BlockB → BlockB) :
    OpenCount { state with blocks := state.blocks.modify block update } =
      OpenCount state - (if (cfgBlock body).terms.isEmpty then 1 else 0) +
        (if (cfgBlock (update body)).terms.isEmpty then 1 else 0) := by
  have bound := (Array.getElem?_eq_some_iff.mp row).1
  have value := (Array.getElem?_eq_some_iff.mp row).2
  unfold OpenCount Array.modify Array.modifyM
  simp only [bound, dite_true, pure, bind, Id.run]
  rw [Array.countP_set bound]
  simp only [value]

theorem openCount_push_def {state : LS} {block : BlockId} {body : BlockB}
    (row : state.blocks[block]? = some body) (value : ValueId) (op : Op) :
    OpenCount { state with blocks := state.blocks.modify block (fun body => { body with insts := body.insts.push (.def value op) }) } = OpenCount state := by
  rw [openCount_modify row]
  have lower : (if (cfgBlock body).terms.isEmpty then 1 else 0) ≤ OpenCount state := by
    simpa [OpenCount, (Array.getElem?_eq_some_iff.mp row).2] using
      (Array.boole_getElem_le_countP (xs := state.blocks)
        (p := fun body => (cfgBlock body).terms.isEmpty) (i := block)
        (Array.getElem?_eq_some_iff.mp row).1)
  simp only [cfgBlock, GIR.Block.terms, Array.toList_push, List.filterMap_append,
    List.filterMap_cons, List.filterMap_nil, Inst.term?, List.append_nil]
  simp only [cfgBlock, GIR.Block.terms] at lower
  by_cases isOpen : (body.insts.toList.filterMap Inst.term?).isEmpty = true
  · simp only [isOpen, ite_true] at lower ⊢
    omega
  · simp [isOpen]

theorem openCount_push_effect {state : LS} {block : BlockId} {body : BlockB}
    (row : state.blocks[block]? = some body) (effect : Effect) :
    OpenCount { state with blocks := state.blocks.modify block (fun body => { body with insts := body.insts.push (.eff effect) }) } = OpenCount state := by
  rw [openCount_modify row]
  have lower : (if (cfgBlock body).terms.isEmpty then 1 else 0) ≤ OpenCount state := by
    simpa [OpenCount, (Array.getElem?_eq_some_iff.mp row).2] using
      (Array.boole_getElem_le_countP (xs := state.blocks)
        (p := fun body => (cfgBlock body).terms.isEmpty) (i := block)
        (Array.getElem?_eq_some_iff.mp row).1)
  simp only [cfgBlock, GIR.Block.terms, Array.toList_push, List.filterMap_append,
    List.filterMap_cons, List.filterMap_nil, Inst.term?, List.append_nil]
  simp only [cfgBlock, GIR.Block.terms] at lower
  by_cases isOpen : (body.insts.toList.filterMap Inst.term?).isEmpty = true
  · simp only [isOpen, ite_true] at lower ⊢
    omega
  · simp [isOpen]

theorem openCount_push_term {state : LS} {block : BlockId} {body : BlockB}
    (row : state.blocks[block]? = some body) (openBody : OpenBlock body) (term : Term) :
    OpenCount { state with blocks := state.blocks.modify block (fun body => { body with insts := body.insts.push (.term term) }) } + 1 = OpenCount state := by
  rw [openCount_modify row]
  have present : 1 ≤ OpenCount state := by
    have lower := Array.boole_getElem_le_countP (xs := state.blocks)
      (p := fun body => (cfgBlock body).terms.isEmpty) (i := block)
      (Array.getElem?_eq_some_iff.mp row).1
    simpa only [(Array.getElem?_eq_some_iff.mp row).2, List.isEmpty_iff.mpr openBody,
      ite_true, OpenCount] using lower
  have closed := open_push_term openBody term
  have notOpen : (cfgBlock { body with insts := body.insts.push (.term term) }).terms.isEmpty = false := by
    cases terms : (cfgBlock { body with insts := body.insts.push (.term term) }).terms with
    | nil => have count := closed.1; simp [terms] at count
    | cons _ _ => rfl
  simp only [List.isEmpty_iff.mpr openBody, ite_true, notOpen, Bool.false_eq_true, ite_false, Nat.add_zero]
  omega

theorem openCount_newBlock (state : LS) (types : List VTy) (env : LEnv) :
    OpenCount (newBlock types env state).2 = OpenCount state + 1 := by
  change (state.blocks.push _).countP _ = _
  rw [Array.countP_push]
  rfl

end Goose.Lower.Validation
