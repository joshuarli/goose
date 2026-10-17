import Goose.GIR.Validate

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def NoEntryTargets (func : Func) : Prop :=
  ∀ block ∈ func.blocks.toList, ∀ target ∈ block.terms.flatMap Term.successors, target ≠ 0

theorem predecessors_entry (func : Func) (noEntry : NoEntryTargets func) :
    (predecessors func)[0]?.getD [] = [] := by
  let n := func.blocks.size
  let addTarget := fun (source : BlockId) (acc : Array (List BlockId)) (target : BlockId) =>
    if target < n then acc.modify target (source :: ·) else acc
  have inner (source : BlockId) (targets : List BlockId)
      (positive : ∀ target ∈ targets, target ≠ 0) (acc : Array (List BlockId)) :
      (targets.foldl (addTarget source) acc)[0]? = acc[0]? := by
    induction targets generalizing acc with
    | nil => rfl
    | cons target rest ih =>
      rw [List.foldl_cons, ih (fun next member => positive next (by simp [member]))]
      have nonzero := positive target (by simp)
      simp only [addTarget]
      split
      · simp only [Array.getElem?_modify, nonzero, ite_false]
      · rfl
  let addBlock := fun (acc : Array (List BlockId)) (source : BlockId) =>
    match func.blocks[source]? with
    | none => acc
    | some block => (block.terms.flatMap Term.successors).foldl (addTarget source) acc
  have outer (sources : List BlockId) (acc : Array (List BlockId)) :
      (sources.foldl addBlock acc)[0]? = acc[0]? := by
    induction sources generalizing acc with
    | nil => rfl
    | cons source rest ih =>
      rw [List.foldl_cons, ih]
      simp only [addBlock]
      cases row : func.blocks[source]? with
      | none => rfl
      | some block =>
        exact inner source _
          (noEntry block (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row))) acc
  have rowZero := outer (List.range n) (Array.replicate n [])
  change ((List.range n).foldl addBlock (Array.replicate n []))[0]?.getD [] = []
  rw [rowZero]
  cases n <;> simp

end Goose.Lower.Validation
