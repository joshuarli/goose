import Goose.Lower.Validation.JoinContentsGraph

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ContentsClosed.patchTerm_argument {le : LEnv} {before after : LS}
    {source target : BlockId} {argument parameter : ValueId} {ty : VTy} {result : Unit}
    {authorized : ValueId → Prop} {destination : GIR.Block}
    (sourceBound : source < before.blocks.size)
    (targetRow : (permissionFunc le before).blocks[target]? = some destination)
    (parameters : destination.params = [(parameter, ty)])
    (run : Goose.Lower.patchTerm source (.br target [argument]) le before = (result, after))
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized)
    (permitted : authorized parameter) : authorized argument := by
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  have extension := (LS.Ext.refl before).modify (appends_push (.term (.br target [argument]))) source
  obtain ⟨next, nextRow, params, _, _⟩ := permissionFunc_ext_at extension targetRow
  let old := before.blocks[source]
  let updated : GIR.Block := ⟨old.params, old.insts.toList ++ [.term (.br target [argument])]⟩
  have sourceRow : (permissionFunc le
      { before with blocks := before.blocks.modify source (fun block => { block with insts := block.insts.push (.term (.br target [argument])) }) }).blocks[source]? =
      some updated := by
    simp [permissionFunc, updated, old, Array.getElem?_modify, Array.getElem?_eq_getElem sourceBound]
  apply closed.edges updated (Array.mem_toList_iff.mpr (Array.mem_of_getElem? sourceRow))
    (.br target [argument]) (by simp [updated]) (target, [argument])
    (by simp [Term.permissionEdges]) next nextRow ((parameter, ty), argument)
    (by rw [params, parameters]; simp) permitted

theorem patchBrs_frame_at {le : LEnv} {before after : LS} {result : Unit} {target index : BlockId}
    {destination : GIR.Block} (incoming : List (BlockId × ValueId))
    (run : Goose.Lower.patchBrs target incoming le before = (result, after))
    (row : (permissionFunc le before).blocks[index]? = some destination) :
    ∃ next, (permissionFunc le after).blocks[index]? = some next ∧ next.params = destination.params := by
  obtain ⟨next, nextRow, params, _, _⟩ := permissionFunc_ext_at (adv_patchBrs_ext incoming run) row
  exact ⟨next, nextRow, params⟩

theorem ContentsClosed.patchBrs_arguments {le : LEnv} {before after : LS}
    {target : BlockId} {parameter : ValueId} {ty : VTy} {result : Unit}
    {authorized : ValueId → Prop} {destination : GIR.Block}
    (incoming : List (BlockId × ValueId))
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (sourceBounds : ∀ pair ∈ incoming, pair.1 < before.blocks.size)
    (targetRow : (permissionFunc le before).blocks[target]? = some destination)
    (parameters : destination.params = [(parameter, ty)])
    (run : Goose.Lower.patchBrs target incoming le before = (result, after))
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized)
    (permitted : authorized parameter) : ∀ pair ∈ incoming, authorized pair.2 := by
  induction incoming generalizing before after result destination with
  | nil => simp
  | cons pair rest ih =>
      obtain ⟨stepResult, middle, firstRun, restRun⟩ := bind_eq.mp run
      have middleFacts := dense_patchTerm pair.1 (.br target [pair.2]) le before stepResult middle firstRun checked bounded
      have afterFacts := dense_patchBrs target rest le middle result after restRun middleFacts.1 middleFacts.2.1
      have middleClosed := closed.restrict_same_values middleFacts.1 afterFacts.1
        (adv_patchBrs_ext rest restRun) (patchBrs_values rest restRun)
      have head := middleClosed.patchTerm_argument (sourceBounds pair (by simp))
        targetRow parameters firstRun permitted
      have extension : before.Ext middle := by
        rw [patchTerm_run] at firstRun
        obtain ⟨_, rfl⟩ := Prod.mk.inj firstRun
        exact (LS.Ext.refl before).modify (appends_push _) pair.1
      obtain ⟨next, nextRow, params, _, _⟩ := permissionFunc_ext_at extension targetRow
      have tail := ih middleFacts.1 middleFacts.2.1
        (fun next member => Nat.lt_of_lt_of_le (sourceBounds next (List.mem_cons_of_mem _ member)) extension.1)
        nextRow (params.trans parameters) restRun closed
      intro next member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact tail next member

end Goose.Lower.Validation
