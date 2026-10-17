import Goose.Lower.Validation.SnapshotContentsSourceControlActions
import Goose.Lower.Validation.SnapshotContentsLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem snapshot_control_header0 {le : LEnv} {first : ValueId} {before : LS}
    (trace : SnapshotSourceTrace le first before before) (generated : GeneratedBuilderState before)
    (fresh : first ≤ before.vals.size) (tail : BlockId → B Unit)
    (tailTrace : ∀ header state, SnapshotSourceTrace le first state state → GeneratedBuilderState state →
      first ≤ state.vals.size → (∃ block, state.blocks[header]? = some block ∧ block.params = []) →
      SnapshotSourceTrace le first (tail header le state).2 (tail header le state).2) :
    let action : B Unit := do
      let (header, params) ← Goose.Lower.newBlock []
      Goose.Lower.emitTerm (.br header [])
      Goose.Lower.setCur (some header)
      tail header
    SnapshotSourceTrace le first (action le before).2 (action le before).2 := by
  let allocated : LS := { before with blocks := before.blocks.push ⟨[], #[]⟩, vals := before.vals }
  have allocation : Goose.Lower.newBlock [] le before = ((before.blocks.size, [ ]), allocated) := rfl
  have allocatedTrace := trace.newBlock [] generated allocation
  have allocatedGenerated := generated.newBlock [] allocation
  let closed := Goose.Lower.emitTerm (.br before.blocks.size []) le allocated
  have headerRow : allocated.blocks[before.blocks.size]? = some ⟨[], #[]⟩ := by
    simp only [allocated, Array.getElem?_push, ite_true]
  have closedTrace := allocatedTrace.emitTerm_integer allocatedGenerated (term := .br before.blocks.size []) (by
    intro edge member destination row param belongs
    have equal : edge = (before.blocks.size, []) := by simpa [Term.permissionEdges] using member
    subst edge
    have located : destination = ⟨[], []⟩ := by
      simpa only [permissionFunc, Array.getElem?_map, headerRow, Option.map_some, Option.some.injEq] using row.symm
    rw [located] at belongs
    cases belongs) (show Goose.Lower.emitTerm (.br before.blocks.size []) le allocated = closed from rfl)
  have closedGenerated := allocatedGenerated.emitTerm (.br before.blocks.size []) (by
    intro target member
    have equal : target = before.blocks.size := by simpa [Term.successors] using member
    subst target
    simp [allocated]) (show Goose.Lower.emitTerm (.br before.blocks.size []) le allocated = closed from rfl)
  have closingAdvance := advB_emitTerm (.br before.blocks.size []) le allocated closed.1 closed.2 rfl
  let selected := Goose.Lower.setCur (some before.blocks.size) le closed.2
  have selectedTrace := closedTrace.setCur_full (show Goose.Lower.setCur (some before.blocks.size) le closed.2 = selected from rfl)
  have selectedGenerated := closedGenerated.setCur (some before.blocks.size) (fun target equal => by
    have equal := Option.some.inj equal
    subst target
    exact Nat.lt_of_lt_of_le (by simp [allocated]) closingAdvance.ext.1) (show Goose.Lower.setCur (some before.blocks.size) le closed.2 = selected from rfl)
  have selectedFresh : first ≤ selected.2.vals.size := by
    have allocatedGrowth := (adv_newBlock0 allocation).vals
    exact Nat.le_trans fresh (Nat.le_trans allocatedGrowth closingAdvance.vals)
  have selectedHeader : ∃ block, selected.2.blocks[before.blocks.size]? = some block ∧ block.params = [] := by
    obtain ⟨block, row, params, _⟩ := closingAdvance.ext.2 before.blocks.size _ headerRow
    exact ⟨block, row, params⟩
  have finished := tailTrace before.blocks.size selected.2 selectedTrace selectedGenerated selectedFresh selectedHeader
  simpa only [bind_run, newBlock0_run, setCur_run, List.headD_cons, selected, closed, allocated] using finished

theorem snapshot_control_header1 {le : LEnv} {first : ValueId} {before : LS}
    (trace : SnapshotSourceTrace le first before before) (generated : GeneratedBuilderState before)
    (fresh : first ≤ before.vals.size) (hint : IntTy) (initial : ValueId) (tail : BlockId → ValueId → B Unit)
    (tailTrace : ∀ header counter state, SnapshotSourceTrace le first state state → GeneratedBuilderState state →
      first ≤ state.vals.size → (∃ block, state.blocks[header]? = some block ∧ block.params = [(counter, .data (.int hint))]) →
      SnapshotSourceTrace le first (tail header counter le state).2 (tail header counter le state).2) :
    let action : B Unit := do
      let (header, params) ← Goose.Lower.newBlock [.data (.int hint)]
      let counter := params.headD 0
      Goose.Lower.emitTerm (.br header [initial])
      Goose.Lower.setCur (some header)
      tail header counter
    SnapshotSourceTrace le first (action le before).2 (action le before).2 := by
  let allocated : LS := { before with blocks := before.blocks.push ⟨[(before.vals.size, .data (.int hint))], #[]⟩, vals := before.vals.push (some (.data (.int hint))) }
  have allocation : Goose.Lower.newBlock [.data (.int hint)] le before = ((before.blocks.size, [before.vals.size]), allocated) := rfl
  have allocatedTrace := trace.newBlock [.data (.int hint)] generated allocation
  have allocatedGenerated := generated.newBlock [.data (.int hint)] allocation
  let closed := Goose.Lower.emitTerm (.br before.blocks.size [initial]) le allocated
  have headerRow : allocated.blocks[before.blocks.size]? = some ⟨[(before.vals.size, .data (.int hint))], #[]⟩ := by
    simp only [allocated, Array.getElem?_push, ite_true]
  have closedTrace := allocatedTrace.emitTerm_integer allocatedGenerated (term := .br before.blocks.size [initial]) (by
    intro edge member destination row param belongs
    have equal : edge = (before.blocks.size, [initial]) := by simpa [Term.permissionEdges] using member
    subst edge
    have located : destination = ⟨[(before.vals.size, .data (.int hint))], []⟩ := by
      simpa only [permissionFunc, Array.getElem?_map, headerRow, Option.map_some, Option.some.injEq] using row.symm
    rw [located] at belongs
    have equal := List.mem_singleton.mp belongs
    subst param
    exact ⟨hint, rfl⟩) (show Goose.Lower.emitTerm (.br before.blocks.size [initial]) le allocated = closed from rfl)
  have closedGenerated := allocatedGenerated.emitTerm (.br before.blocks.size [initial]) (by
    intro target member
    have equal : target = before.blocks.size := by simpa [Term.successors] using member
    subst target
    simp [allocated]) (show Goose.Lower.emitTerm (.br before.blocks.size [initial]) le allocated = closed from rfl)
  have closingAdvance := advB_emitTerm (.br before.blocks.size [initial]) le allocated closed.1 closed.2 rfl
  let selected := Goose.Lower.setCur (some before.blocks.size) le closed.2
  have selectedTrace := closedTrace.setCur_full (show Goose.Lower.setCur (some before.blocks.size) le closed.2 = selected from rfl)
  have selectedGenerated := closedGenerated.setCur (some before.blocks.size) (fun target equal => by
    have equal := Option.some.inj equal
    subst target
    exact Nat.lt_of_lt_of_le (by simp [allocated]) closingAdvance.ext.1) (show Goose.Lower.setCur (some before.blocks.size) le closed.2 = selected from rfl)
  have selectedFresh : first ≤ selected.2.vals.size := by
    have allocatedGrowth := (adv_newBlock1 allocation).vals
    exact Nat.le_trans fresh (Nat.le_trans allocatedGrowth closingAdvance.vals)
  have selectedHeader : ∃ block, selected.2.blocks[before.blocks.size]? = some block ∧ block.params = [(before.vals.size, .data (.int hint))] := by
    obtain ⟨block, row, params, _⟩ := closingAdvance.ext.2 before.blocks.size _ headerRow
    exact ⟨block, row, params⟩
  have finished := tailTrace before.blocks.size before.vals.size selected.2 selectedTrace selectedGenerated selectedFresh selectedHeader
  simpa only [bind_run, newBlock1_run, setCur_run, List.headD_cons, selected, closed, allocated] using finished

end Goose.Lower.Validation
