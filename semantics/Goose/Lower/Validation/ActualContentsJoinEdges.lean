import Goose.Lower.Validation.ActualContentsOperations

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ActualContentsAmbient.patchTerm_argument {le : LEnv} {before after : LS}
    (ambient : ActualContentsAmbient le after) {source target : BlockId}
    {argument parameter : ValueId} {type : VTy} {result : Unit} {destination : GIR.Block}
    (sourceBound : source < before.blocks.size)
    (targetRow : (permissionFunc le before).blocks[target]? = some destination)
    (parameters : destination.params = [(parameter, type)])
    (run : patchTerm source (.br target [argument]) le before = (result, after))
    (allowed : ambient.authorized parameter) : ambient.authorized argument := by
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  have extension := (LS.Ext.refl before).modify (appends_push (.term (.br target [argument]))) source
  obtain ⟨next, nextRow, params, _, _⟩ := permissionFunc_ext_at extension targetRow
  let updated : GIR.Block := ⟨before.blocks[source].params,
    before.blocks[source].insts.toList ++ [.term (.br target [argument])]⟩
  have sourceRow : (permissionFunc le
      { before with blocks := before.blocks.modify source (fun block =>
        { block with insts := block.insts.push (.term (.br target [argument])) }) }).blocks[source]? =
      some updated := by
    simp [permissionFunc, updated, Array.getElem?_modify, Array.getElem?_eq_getElem sourceBound]
  exact ambient.edge (term := .br target [argument]) (edge := (target, [argument]))
    (entry := ((parameter, type), argument)) (Array.mem_toList_iff.mpr (Array.mem_of_getElem? sourceRow))
    (by simp [updated]) (by simp [Term.permissionEdges]) nextRow
    (by rw [params, parameters]; simp) allowed

theorem ActualContentsAmbient.patchBrs_arguments {le : LEnv} {before after : LS}
    (ambient : ActualContentsAmbient le after) {result : Unit} {target parameter : Nat}
    {type : VTy} {destination : GIR.Block} (incoming : List (BlockId × ValueId))
    (sourceBounds : ∀ pair ∈ incoming, pair.1 < before.blocks.size)
    (targetRow : (permissionFunc le before).blocks[target]? = some destination)
    (parameters : destination.params = [(parameter, type)])
    (run : patchBrs target incoming le before = (result, after))
    (allowed : ambient.authorized parameter) : ∀ pair ∈ incoming, ambient.authorized pair.2 := by
  induction incoming generalizing before result destination with
  | nil => simp
  | cons pair rest ih =>
    obtain ⟨stepResult, middle, firstRun, restRun⟩ := bind_eq.mp run
    let middleAmbient := ambient.before (adv_patchBrs_ext rest restRun)
      (types_patchBrs target rest _ _ _ _ restRun)
    have head := middleAmbient.patchTerm_argument (sourceBounds pair (by simp)) targetRow parameters firstRun allowed
    have extension : before.Ext middle := by
      rw [patchTerm_run] at firstRun
      obtain ⟨_, rfl⟩ := Prod.mk.inj firstRun
      exact (LS.Ext.refl before).modify (appends_push _) pair.1
    obtain ⟨next, nextRow, params, _, _⟩ := permissionFunc_ext_at extension targetRow
    have tail := ih (fun next member =>
      Nat.lt_of_lt_of_le (sourceBounds next (List.mem_cons_of_mem _ member)) extension.1)
      nextRow (params.trans parameters) restRun
    intro next member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact tail next member

end Goose.Lower.Validation
