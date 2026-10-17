import Goose.GIR.ReplacementContentFlowProofsCanonicalMemory

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

def WriteRows (func : Func) (writes : Array Write) : Prop :=
  ∀ index, index < writes.size → ∀ roots,
    writes[index]?.getD (.assigned .unknown) = .assigned roots →
      (func.roots.contents.find? (·.1 == index)).isSome = true

theorem WriteRows.assign {func : Func} {writes : Array Write} {index : Nat} {roots : Roots}
    (before : WriteRows func writes)
    (observed : (func.roots.contents.find? (·.1 == index)).isSome = true) :
    WriteRows func (writes.set! index
      ((writes[index]?.getD (.assigned .unknown)).join (.assigned roots))) := by
  intro cell bounded actual assigned
  have priorBound : cell < writes.size := by simpa using bounded
  by_cases same : index = cell
  · simpa only [same] using observed
  · apply before cell priorBound actual
    simpa only [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds,same,ite_false] using assigned

theorem start_writeRows (func : Func) (vt : Array (Option VTy)) :
    WriteRows func (start func vt).writes := by
  rw [start_components]
  intro index bounded roots assigned
  have bound : index < func.params.length := by simpa using bounded
  simp [bound] at assigned

theorem ArrayExtends.writeRows {func : Func} {before after : Array Write}
    (growth : ArrayExtends (.assigned .unknown) Write.Extends before after) (rows : WriteRows func after) : WriteRows func before := by
  intro index bounded roots assigned
  have nextBound : index < after.size := by simpa [growth.size] using bounded
  have next := growth.values index
  rw [assigned] at next
  cases found : after[index]?.getD (.assigned .unknown) with
  | unchanged => simp [found,Write.Extends] at next
  | assigned actual => exact rows index nextBound actual found

end Goose.GIR.ReplacementContentFlow.Model
