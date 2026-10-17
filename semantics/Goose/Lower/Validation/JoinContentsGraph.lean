import Goose.Lower.Validation.JoinContentsPatch

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ContentsClosed.patchBrs {le : LEnv} {before after : LS} {result : Unit}
    {target : BlockId} (incoming : List (BlockId × ValueId)) {authorized : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : patchBrs target incoming le before = (result, after))
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized)
    (arguments : ∀ pair ∈ incoming, authorized pair.2) :
    ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized := by
  induction incoming generalizing before after result with
  | nil =>
      obtain ⟨_, rfl⟩ := pure_eq.mp run
      exact closed
  | cons pair rest ih =>
      obtain ⟨unit, middle, firstRun, restRun⟩ := bind_eq.mp run
      have middleDense := dense_patchTerm pair.1 (.br target [pair.2]) le before unit middle firstRun checked bounded
      apply ih middleDense.1 middleDense.2.1 restRun
      · apply closed.patchTerm checked bounded firstRun
        intro edge member destination row entry belongs permitted
        have edgeEqual : edge = (target, [pair.2]) := by simpa [Term.permissionEdges] using member
        subst edge
        have same : entry.2 = pair.2 := by simpa using (List.of_mem_zip belongs).2
        rw [same]
        exact arguments pair (List.mem_cons_self ..)
      · intro next member
        exact arguments next (List.mem_cons_of_mem _ member)

theorem NonIntegerParameters.patchBrs {le : LEnv} {before after : LS} {result : Unit}
    {target : BlockId} (incoming : List (BlockId × ValueId)) {authorized : ValueId → Prop}
    (run : patchBrs target incoming le before = (result, after))
    (checked : NonIntegerParameters (permissionFunc le before) authorized) :
    NonIntegerParameters (permissionFunc le after) authorized := by
  induction incoming generalizing before after result with
  | nil =>
      obtain ⟨_, rfl⟩ := pure_eq.mp run
      exact checked
  | cons pair rest ih =>
      obtain ⟨unit, middle, firstRun, restRun⟩ := bind_eq.mp run
      exact ih restRun (checked.patchTerm firstRun)

theorem ContentsClosed.restrict_same_values {le : LEnv} {before after : LS} {authorized : ValueId → Prop}
    (beforeDense : before.DenseDefinitions) (afterDense : after.DenseDefinitions)
    (extension : before.Ext after) (values : after.vals = before.vals)
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized) :
    ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized := by
  have types : TypePrefix after before := by intro value ty row; simpa only [values] using row
  constructor
  · intro value member
    simpa only [permissionFunc_numValues beforeDense le, permissionFunc_numValues afterDense le, values]
      using closed.bounded value member
  · intro block row param member permitted
    obtain ⟨next, nextRow, params, suffix, instructions⟩ := permissionFunc_ext_at extension row
    exact typedPermissions_retained types
      (closed.entry next nextRow param (by rw [params]; exact member) permitted)
  · intro block member value op instruction permitted
    obtain ⟨index, row⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    obtain ⟨next, nextRow, params, suffix, instructions⟩ := permissionFunc_ext_at extension row
    exact (closed.definitions next (Array.mem_toList_iff.mpr (Array.mem_of_getElem? nextRow)) value op
      (by rw [instructions]; exact List.mem_append_left _ instruction) permitted).retained types
  · intro block member term instruction edge edgeMember destination row entry belongs permitted
    obtain ⟨index, blockRow⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    obtain ⟨next, nextRow, params, suffix, instructions⟩ := permissionFunc_ext_at extension blockRow
    obtain ⟨nextDestination, nextDestinationRow, destinationParams, _, _⟩ := permissionFunc_ext_at extension row
    exact closed.edges next (Array.mem_toList_iff.mpr (Array.mem_of_getElem? nextRow)) term
      (by rw [instructions]; exact List.mem_append_left _ instruction) edge edgeMember nextDestination
      nextDestinationRow entry (by rw [destinationParams]; exact belongs) permitted

theorem patchBrs_values {le : LEnv} {before after : LS} {result : Unit}
    {target : BlockId} (incoming : List (BlockId × ValueId))
    (run : patchBrs target incoming le before = (result, after)) : after.vals = before.vals := by
  induction incoming generalizing before after result with
  | nil => obtain ⟨_, rfl⟩ := pure_eq.mp run; rfl
  | cons pair rest ih =>
      obtain ⟨unit, middle, firstRun, restRun⟩ := bind_eq.mp run
      have same := ih restRun
      rw [patchTerm_run] at firstRun
      obtain ⟨_, rfl⟩ := Prod.mk.inj firstRun
      exact same

theorem FreshContentsEvidence.common {le : LEnv} {first : Nat} {state : LS}
    (incoming : List (BlockId × ValueId))
    (evidence : ∀ pair ∈ incoming, FreshContentsEvidence le first state pair.2) :
    ∃ authorized,
      ContentsClosed (le.globals.map (·.2)) le.mod.structs
        (permissionFunc le state) state.vals authorized ∧
      NonIntegerParameters (permissionFunc le state) authorized ∧
      (∀ pair ∈ incoming, authorized pair.2) ∧
      ∀ value, authorized value → first ≤ value := by
  induction incoming with
  | nil =>
      exact ⟨fun _ => False, .empty _ _ _ _, .empty _, by simp, by simp⟩
  | cons pair rest ih =>
      obtain ⟨left, leftClosed, leftNoninteger, leftMember, leftFresh⟩ := evidence pair (by simp)
      obtain ⟨right, rightClosed, rightNoninteger, rightMembers, rightFresh⟩ :=
        ih (fun next member => evidence next (List.mem_cons_of_mem _ member))
      refine ⟨fun value => left value ∨ right value, leftClosed.union rightClosed,
        leftNoninteger.union rightNoninteger, ?_, ?_⟩
      · intro next member
        rcases List.mem_cons.mp member with rfl | member
        · exact Or.inl leftMember
        · exact Or.inr (rightMembers next member)
      · intro value member
        exact member.elim (leftFresh value) (rightFresh value)

theorem ContentsClosed.patchBrs_avoiding_target {le : LEnv} {before after : LS} {result : Unit}
    {target : BlockId} (incoming : List (BlockId × ValueId)) {authorized : ValueId → Prop}
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : Goose.Lower.patchBrs target incoming le before = (result, after))
    (closed : ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le before) before.vals authorized)
    (excluded : ∀ destination, (permissionFunc le before).blocks[target]? = some destination →
      ∀ parameter ∈ destination.params, ¬ authorized parameter.1) :
    ContentsClosed (le.globals.map (·.2)) le.mod.structs
      (permissionFunc le after) after.vals authorized := by
  induction incoming generalizing before after result with
  | nil => obtain ⟨_, rfl⟩ := pure_eq.mp run; exact closed
  | cons pair rest ih =>
      obtain ⟨stepResult, middle, firstRun, restRun⟩ := bind_eq.mp run
      have middleFacts := dense_patchTerm pair.1 (.br target [pair.2]) le before stepResult middle firstRun checked bounded
      apply ih middleFacts.1 middleFacts.2.1 restRun
      · apply closed.patchTerm checked bounded firstRun
        intro edge member destination row entry belongs permitted
        have same : edge = (target, [pair.2]) := by simpa [Term.permissionEdges] using member
        subst edge
        exact (excluded destination row entry.1 (List.of_mem_zip belongs).1 permitted).elim
      · intro destination row parameter member permitted
        obtain ⟨old, oldRow, params⟩ := join_patchTerm_frame_at firstRun row
        exact excluded old oldRow parameter (by rw [← params]; exact member) permitted

theorem FreshContentsEvidence.patchBrs_before {le : LEnv} {before after : LS} {first : Nat}
    {target : BlockId} {value : ValueId} {result : Unit} (incoming : List (BlockId × ValueId))
    (evidence : FreshContentsEvidence le first before value)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (run : patchBrs target incoming le before = (result, after))
    (earlier : ∀ destination, (permissionFunc le before).blocks[target]? = some destination →
      ∀ parameter ∈ destination.params, parameter.1 < first) :
    FreshContentsEvidence le first after value := by
  obtain ⟨authorized, closed, noninteger, member, fresh⟩ := evidence
  refine ⟨authorized, closed.patchBrs_avoiding_target incoming checked bounded run ?_,
    noninteger.patchBrs incoming run, member, fresh⟩
  intro destination row parameter belongs permitted
  exact Nat.not_lt_of_ge (fresh parameter.1 permitted) (earlier destination row parameter belongs)

end Goose.Lower.Validation
