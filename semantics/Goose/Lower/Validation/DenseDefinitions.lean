import Goose.Lower.Validation.CfgFrontier
import Goose.Lower.Validation.CfgBuilderFunctions
import Goose.Lower.Validation.Definitions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def DenseRun (action : B α) : Prop :=
  ∀ le before result after, action le before = (result, after) →
    before.DenseDefinitions → LiveBound before →
    after.DenseDefinitions ∧ LiveBound after ∧ before.blocks.size ≤ after.blocks.size

theorem DenseRun.pure (value : α) : DenseRun (pure value) := by
  intro le before result after run checked bounded
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact ⟨checked, bounded, Nat.le_refl _⟩

theorem DenseRun.bind {action : B α} {next : α → B β}
    (first : DenseRun action) (second : ∀ value, DenseRun (next value)) :
    DenseRun (action >>= next) := by
  intro le before result after run checked bounded
  obtain ⟨value, middle, firstRun, secondRun⟩ := bind_eq.mp run
  have one := first le before value middle firstRun checked bounded
  have two := second value le middle result after secondRun one.1 one.2.1
  exact ⟨two.1, two.2.1, Nat.le_trans one.2.2 two.2.2⟩

private theorem DenseRun.of_bounded {action : B α}
    (preserves : BoundedRun LS.DenseDefinitions action) (advances : AdvB action) : DenseRun action := by
  intro le before result after run checked bounded
  have advance := advances le before result after run
  exact ⟨preserves le before result after run checked bounded,
    liveBound_of_adv advance bounded, advance.ext.1⟩

theorem DenseRun.of_unchanged {action : B α}
    (unchanged : ∀ le state, (action le state).2 = state) : DenseRun action := by
  intro le before result after run checked bounded
  have equal := unchanged le before
  rw [run] at equal
  change after = before at equal
  subst after
  exact ⟨checked, bounded, Nat.le_refl _⟩

theorem dense_recordValueRootRecipe (value : ValueId) (sourceScope : ScopeId) :
    DenseRun (recordValueRootRecipe value sourceScope) := by
  apply DenseRun.of_bounded ?_ (advB_recordValueRootRecipe value sourceScope)
  intro le before result after run checked bounded
  rw [recordValueRootRecipe_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact checked

theorem dense_recordReadValueRootRecipe (value : ValueId) (place : Place) :
    DenseRun (recordReadValueRootRecipe value place) := by
  apply DenseRun.of_bounded ?_ (advB_recordReadValueRootRecipe value place)
  intro le before result after run checked bounded
  cases place <;> simp only [recordReadValueRootRecipe_run] at run
  all_goals try split at run
  all_goals try rw [recordValueRootSource_run] at run
  all_goals obtain ⟨_, rfl⟩ := Prod.mk.inj run
  all_goals exact checked

theorem dense_emitDef (op : Op) : DenseRun (emitDef op) := by
  apply DenseRun.of_bounded ?_ (advB_emitDef op)
  intro le before result after run checked bounded
  cases current : before.cur with
  | none =>
    rw [emitDef_none op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitDef_run op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact LS.DenseDefinitions.emitDef checked current (bounded block current)

theorem dense_newBlock (types : List VTy) : DenseRun (newBlock types) := by
  intro le before result after run checked bounded
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  refine ⟨checked.newBlock (le := le), ?_, by simp⟩
  intro block current
  exact Nat.lt_trans (bounded block current) (by simp)

theorem dense_setCur_at {le : LEnv} {before after : LS} {block : Option BlockId} {result : Unit}
    (run : setCur block le before = (result, after)) (checked : before.DenseDefinitions)
    (bounded : ∀ current, block = some current → current < before.blocks.size) :
    after.DenseDefinitions ∧ LiveBound after ∧ before.blocks.size ≤ after.blocks.size := by
  rw [setCur_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨checked, bounded, Nat.le_refl _⟩

theorem dense_emitEffect (effect : Effect) : DenseRun (emitEffect effect) := by
  apply DenseRun.of_bounded ?_ (advB_emitEffect effect)
  intro le before result after run checked bounded
  cases current : before.cur with
  | none =>
    rw [emitEffect_none effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitEffect_run effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked.emitEffect (le := le) (bounded block current)

theorem dense_emitTerm (term : Term) : DenseRun (emitTerm term) := by
  apply DenseRun.of_bounded ?_ (advB_emitTerm term)
  intro le before result after run checked bounded
  cases current : before.cur with
  | none =>
    rw [emitTerm_none term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitTerm_run term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked.emitTerm (le := le) (bounded block current)

theorem dense_patchTerm (block : BlockId) (term : Term) : DenseRun (patchTerm block term) := by
  intro le before result after run checked bounded
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  refine ⟨?_, ?_, by simp⟩
  · change (before.appendInst block (.term term)).DenseDefinitions
    by_cases bound : block < before.blocks.size
    · exact checked.patchTerm (le := le) bound
    · have same : before.appendInst block (.term term) = before := by
        unfold LS.appendInst
        congr 1
        apply Array.ext
        · simp
        · intro index leftBound rightBound
          have different : block ≠ index := by intro equal; subst block; exact bound rightBound
          simp [Array.getElem_modify, different]
      simpa only [same] using checked
  · intro current active
    simpa [LS.appendInst] using bounded current active

theorem dense_curBlock : DenseRun curBlock := by
  apply DenseRun.of_unchanged
  intros
  rfl

theorem dense_get : DenseRun (get : B LS) := by
  apply DenseRun.of_unchanged
  intros
  rfl

theorem dense_read : DenseRun (read : B LEnv) := by
  apply DenseRun.of_unchanged
  intros
  rfl

theorem dense_valTy (value : ValueId) : DenseRun (valTy value) := by
  apply DenseRun.of_unchanged
  intros
  rw [valTy_run]

theorem dense_isLive : DenseRun isLive := by
  apply DenseRun.of_unchanged
  intros
  rfl

theorem dense_pushScope (scope : ScopeId) : DenseRun (pushScope scope) := by
  intro le before result after run checked bounded
  rw [pushScope_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨checked, bounded, Nat.le_refl _⟩

theorem dense_popScope : DenseRun popScope := by
  intro le before result after run checked bounded
  rw [popScope_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact ⟨checked, bounded, Nat.le_refl _⟩

theorem dense_inScope (scope : ScopeId) {action : B α} (typed : DenseRun action) :
    DenseRun (inScope scope action) := by
  unfold inScope
  exact DenseRun.bind (dense_pushScope _) fun _ =>
    DenseRun.bind typed fun _ => DenseRun.bind dense_popScope fun _ => DenseRun.pure _

theorem dense_whenLive (default : α) {action : BlockId → B α}
    (typed : ∀ block, DenseRun (action block)) : DenseRun (whenLive default action) := by
  unfold whenLive
  refine DenseRun.bind dense_curBlock fun current => ?_
  cases current
  · exact DenseRun.pure _
  · exact typed _

theorem dense_intTyOf (v : ValueId) : DenseRun (intTyOf v) := by
  unfold intTyOf
  refine DenseRun.bind (dense_valTy v) fun t => ?_
  cases t with
  | data t => cases t <;> exact DenseRun.pure _
  | view _ _ => exact DenseRun.pure _

theorem dense_freezeTo (m : Mutability) (r : ValueId) : DenseRun (freezeTo m r) := by
  unfold freezeTo
  refine DenseRun.bind (dense_valTy r) fun t => ?_
  cases m <;> cases t <;> first
    | exact DenseRun.pure _
    | (rename_i t; cases t <;> first | exact DenseRun.pure _ | (rename_i m' _; cases m' <;> first | exact DenseRun.pure _ | exact dense_emitDef _))

theorem dense_borrowTo (m : Mutability) (r : ValueId) : DenseRun (borrowTo m r) := by
  intro le before result after run
  rcases borrowTo_cases run with frozen | borrowed
  · exact dense_freezeTo m r le before result after frozen
  · exact dense_emitDef _ le before result after borrowed

theorem dense_coerceTo (target : Ty) (r : ValueId) (org : OriginId) : DenseRun (coerceTo target r org) := by
  unfold coerceTo
  refine DenseRun.bind (dense_valTy r) fun source => ?_
  split
  · exact dense_emitDef _
  · exact DenseRun.bind (dense_emitDef _) (fun _ => dense_emitDef _)
  · exact DenseRun.pure _

theorem dense_coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) :
    DenseRun (coerceSlot slot value org) := by
  unfold coerceSlot
  refine DenseRun.bind dense_read fun le => ?_
  cases le.slots[slot]? with
  | none => exact DenseRun.pure _
  | some destination => exact dense_coerceTo destination.ty value org

theorem dense_coerceResult (value : ValueId) (org : OriginId) :
    DenseRun (coerceResult value org) := by
  unfold coerceResult
  refine DenseRun.bind dense_read fun le => ?_
  cases le.results.head? with
  | none => exact DenseRun.pure _
  | some destination => exact dense_coerceTo destination value org

theorem dense_growOwner (r : ValueId) : DenseRun (growOwner r) := by
  unfold growOwner
  refine DenseRun.bind (dense_valTy r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact DenseRun.pure _ | (rename_i m' t'; cases t' <;> exact DenseRun.pure _)
  | view _ _ => exact DenseRun.pure _

theorem dense_leaveAll : ∀ scs, DenseRun (leaveAll scs)
  | [] => DenseRun.pure _
  | sc :: rest => by
    unfold leaveAll
    exact DenseRun.bind (dense_emitEffect _) fun _ => dense_leaveAll rest

theorem dense_leaveTo (d : Nat) : DenseRun (leaveTo d) := by
  unfold leaveTo
  exact DenseRun.bind dense_get fun _ => dense_leaveAll _

theorem dense_initSlots : ∀ ps, DenseRun (initSlots ps)
  | [] => DenseRun.pure _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact DenseRun.bind (dense_emitEffect _) fun _ => dense_initSlots rest

theorem dense_eachElemValue (x : VarId) (byRef : Bool) (elem : ValueId) :
    DenseRun (eachElemValue x byRef elem) := by
  unfold eachElemValue
  cases byRef
  · exact dense_emitDef _
  · refine DenseRun.bind dense_read fun le => ?_
    cases le.vars[x]? with
    | none => exact DenseRun.pure _
    | some lv =>
      dsimp only
      cases lv.ty with
      | ref m t => exact dense_borrowTo m elem
      | _ => exact DenseRun.pure _

theorem dense_regrowOf (o : Option ValueId) : DenseRun (regrowOf o) := by
  cases o with
  | none => exact DenseRun.pure _
  | some r => exact dense_growOwner r

theorem dense_eachSampled (regrow : Bool) (vw : ValueId) : DenseRun (eachSampled regrow vw) := by
  unfold eachSampled
  cases regrow
  · exact dense_emitDef _
  · exact DenseRun.pure _

theorem dense_eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    DenseRun (eachLen regrow owner sampled) := by
  unfold eachLen
  cases regrow
  · exact DenseRun.pure _
  · exact dense_emitDef _

theorem dense_fork (condition : ValueId) : DenseRun (fork condition) := by
  unfold fork
  exact DenseRun.bind (dense_newBlock _) fun ⟨thenBlock, _⟩ =>
    DenseRun.bind (dense_newBlock _) fun ⟨elseBlock, _⟩ =>
    DenseRun.bind (dense_emitTerm _) fun _ => DenseRun.pure _

theorem dense_patchBrs (target : BlockId) : ∀ incoming, DenseRun (patchBrs target incoming)
  | [] => DenseRun.pure _
  | (block, value) :: rest => by
    unfold patchBrs
    exact DenseRun.bind (dense_patchTerm _ _) fun _ => dense_patchBrs target rest

theorem dense_patchBrs0 (target : BlockId) : ∀ incoming, DenseRun (patchBrs0 target incoming)
  | [] => DenseRun.pure _
  | block :: rest => by
    unfold patchBrs0
    exact DenseRun.bind (dense_patchTerm _ _) fun _ => dense_patchBrs0 target rest

theorem dense_scFork (isAnd : Bool) (value : ValueId) : DenseRun (scFork isAnd value) := by
  unfold scFork
  refine DenseRun.bind (dense_newBlock _) fun ⟨_, _⟩ =>
    DenseRun.bind (dense_newBlock _) fun ⟨_, _⟩ => ?_
  cases isAnd <;> exact DenseRun.bind (dense_emitTerm _) fun _ => DenseRun.pure _

theorem dense_setCur_none : DenseRun (setCur none) := by
  intro le before result after run checked _
  exact dense_setCur_at run checked (by intros; contradiction)

theorem dense_newBlock_resume (types : List VTy) {prepare : BlockId → List ValueId → B Unit}
    {tail : BlockId → List ValueId → B α}
    (prepares : ∀ block params, DenseRun (prepare block params))
    (continues : ∀ block params, DenseRun (tail block params)) :
    DenseRun (do
      let (block, params) ← newBlock types
      prepare block params
      setCur (some block)
      tail block params) := by
  intro le before result after run checked bounded
  simp only [bind_eq] at run
  obtain ⟨⟨block, params⟩, allocated, allocation, _, prepared, preparation,
    _, entered, entry, continuation⟩ := run
  have one := dense_newBlock types le before _ allocated allocation checked bounded
  have two := prepares block params le allocated _ prepared preparation one.1 one.2.1
  have fresh := liveBound_newBlock types le before
  rw [allocation] at fresh
  have target : block < prepared.blocks.size := Nat.lt_of_lt_of_le fresh two.2.2
  have three := dense_setCur_at entry two.1 (by intro current equal; cases equal; exact target)
  have four := continues block params le entered result after continuation three.1 three.2.1
  exact ⟨four.1, four.2.1, Nat.le_trans one.2.2 (Nat.le_trans two.2.2 (Nat.le_trans three.2.2 four.2.2))⟩

theorem dense_joinValue (endT : Option BlockId) (vt : ValueId) (endF : Option BlockId) (vf : ValueId) :
    DenseRun (joinValue endT vt endF vf) := by
  have branch (incoming : List (BlockId × ValueId)) : DenseRun (do
      let ty ← valTy (incoming.headD (0, 0)).2
      let (join, params) ← newBlock [ty]
      patchBrs join incoming
      setCur (some join)
      pure (params.headD 0)) := by
    exact DenseRun.bind (dense_valTy _) fun ty =>
      dense_newBlock_resume [ty]
        (prepare := fun join _ => patchBrs join incoming)
        (tail := fun _ params => pure (params.headD 0))
        (fun join _ => dense_patchBrs join incoming) (fun _ _ => DenseRun.pure _)
  unfold joinValue
  split
  · exact DenseRun.bind dense_setCur_none fun _ => DenseRun.pure _
  · exact branch _

theorem dense_joinArms (endT endF : Option BlockId) : DenseRun (joinArms endT endF) := by
  have branch (incoming : List BlockId) : DenseRun (do
      let (join, _) ← newBlock []
      patchBrs0 join incoming
      setCur (some join)) := by
    exact dense_newBlock_resume []
      (prepare := fun join _ => patchBrs0 join incoming) (tail := fun _ _ => pure ())
      (fun join _ => dense_patchBrs0 join incoming) (fun _ _ => DenseRun.pure ())
  unfold joinArms
  split
  · exact dense_setCur_none
  · exact branch _

theorem dense_header0 {tail : BlockId → B Unit} (continues : ∀ header, DenseRun (tail header)) :
    DenseRun (do
      let (header, _) ← newBlock []
      emitTerm (.br header [])
      setCur (some header)
      tail header) :=
  dense_newBlock_resume [] (prepare := fun header _ => emitTerm (.br header []))
    (tail := fun header _ => tail header)
    (fun _ _ => dense_emitTerm _) (fun header _ => continues header)

theorem dense_header1 (ty : VTy) (value : ValueId) {tail : BlockId → ValueId → B Unit}
    (continues : ∀ header parameter, DenseRun (tail header parameter)) :
    DenseRun (do
      let (header, parameters) ← newBlock [ty]
      let parameter := parameters.headD 0
      emitTerm (.br header [value])
      setCur (some header)
      tail header parameter) :=
  dense_newBlock_resume [ty] (prepare := fun header _ => emitTerm (.br header [value]))
    (tail := fun header parameters => tail header (parameters.headD 0))
    (fun _ _ => dense_emitTerm _) (fun header parameters => continues header (parameters.headD 0))

theorem dense_fork_actions (condition : ValueId) {first : B α} {second : B β}
    {join : Option BlockId → α → Option BlockId → β → B γ}
    (one : DenseRun first) (two : DenseRun second)
    (joining : ∀ endT valueT endF valueF, DenseRun (join endT valueT endF valueF)) :
    DenseRun (do
      let (thenBlock, elseBlock) ← fork condition
      setCur (some thenBlock)
      let thenValue ← first
      let thenEnd ← curBlock
      setCur (some elseBlock)
      let elseValue ← second
      let elseEnd ← curBlock
      join thenEnd thenValue elseEnd elseValue) := by
  intro le before result after run checked bounded
  simp only [bind_eq] at run
  obtain ⟨⟨thenBlock, elseBlock⟩, forked, forkRun, _, enteredT, entryT,
    thenValue, endedT, thenRun, thenEnd, readT, readThen,
    _, enteredF, entryF, elseValue, endedF, elseRun, elseEnd, readF, readElse, joinRun⟩ := run
  rw [curBlock_run] at readThen readElse
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj readThen
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj readElse
  have forkedState := dense_fork condition le before _ forked forkRun checked bounded
  have ids := fork_ids forkRun
  have thenBound : thenBlock < forked.blocks.size := by
    have equal := congrArg Prod.fst ids.1
    dsimp only at equal
    rw [equal, ids.2]
    nat_omega
  have elseBound : elseBlock < forked.blocks.size := by
    have equal := congrArg Prod.snd ids.1
    dsimp only at equal
    rw [equal, ids.2]
    nat_omega
  have thenEntry := dense_setCur_at entryT forkedState.1
    (by intro current equal; cases equal; exact thenBound)
  have thenState := one le enteredT thenValue endedT thenRun thenEntry.1 thenEntry.2.1
  have elseTarget := Nat.lt_of_lt_of_le elseBound (Nat.le_trans thenEntry.2.2 thenState.2.2)
  have elseEntry := dense_setCur_at entryF thenState.1
    (by intro current equal; cases equal; exact elseTarget)
  have elseState := two le enteredF elseValue endedF elseRun elseEntry.1 elseEntry.2.1
  have joined := joining endedT.cur thenValue endedF.cur elseValue
    le endedF result after joinRun elseState.1 elseState.2.1
  exact ⟨joined.1, joined.2.1,
    Nat.le_trans forkedState.2.2 (Nat.le_trans thenEntry.2.2 (Nat.le_trans thenState.2.2
      (Nat.le_trans elseEntry.2.2 (Nat.le_trans elseState.2.2 joined.2.2))))⟩

theorem dense_ifE_core (condition : ValueId) (sourceScope : ScopeId) {first second : B ValueId}
    (one : DenseRun first) (two : DenseRun second) :
    DenseRun (whenLive 0 fun _ => do
      let (thenBlock, elseBlock) ← fork condition
      setCur (some thenBlock)
      let thenValue ← first
      let thenEnd ← curBlock
      setCur (some elseBlock)
      let elseValue ← second
      let elseEnd ← curBlock
      let result ← joinValue thenEnd thenValue elseEnd elseValue
      recordValueRootRecipe result sourceScope
      pure result) :=
  dense_whenLive _ fun _ => dense_fork_actions condition one two fun thenEnd thenValue elseEnd elseValue =>
    DenseRun.bind (dense_joinValue thenEnd thenValue elseEnd elseValue) fun result =>
      DenseRun.bind (dense_recordValueRootRecipe result sourceScope) fun _ => DenseRun.pure result

theorem dense_ifS_some_core (condition : ValueId) {first second : B ValueId}
    (one : DenseRun first) (two : DenseRun second) :
    DenseRun (whenLive () fun _ => do
      let (thenBlock, elseBlock) ← fork condition
      setCur (some thenBlock)
      let _ ← first
      let thenEnd ← curBlock
      setCur (some elseBlock)
      let _ ← second
      let elseEnd ← curBlock
      joinArms thenEnd elseEnd) :=
  dense_whenLive _ fun _ => dense_fork_actions condition one two (fun endT _ endF _ => dense_joinArms endT endF)

theorem dense_resume_pair {allocate : B (BlockId × BlockId × δ)}
    {body : BlockId → δ → B α} {back : BlockId → α → B Unit}
    (allocates : DenseRun allocate)
    (targets : ∀ le before pair after, allocate le before = (pair, after) →
      pair.1 < after.blocks.size ∧ pair.2.1 < after.blocks.size)
    (works : ∀ target token, DenseRun (body target token))
    (backs : ∀ target value, DenseRun (back target value)) :
    DenseRun (do
      let (first, last, token) ← allocate
      setCur (some first)
      let value ← body last token
      back last value
      setCur (some last)
      pure token) := by
  intro le before result after run checked bounded
  simp only [bind_eq] at run
  obtain ⟨⟨first, last, token⟩, allocated, allocation, _, entered, entry,
    value, ended, work, _, backed, backing, _, reentered, reentry, final⟩ := run
  obtain ⟨_, rfl⟩ := pure_eq.mp final
  have one := allocates le before _ allocated allocation checked bounded
  have bounds := targets le before (first, last, token) allocated allocation
  have two := dense_setCur_at entry one.1 (by intro current equal; cases equal; exact bounds.1)
  have three := works last token le entered value ended work two.1 two.2.1
  have four := backs last value le ended _ backed backing three.1 three.2.1
  have lastBound := Nat.lt_of_lt_of_le bounds.2
    (Nat.le_trans two.2.2 (Nat.le_trans three.2.2 four.2.2))
  have five := dense_setCur_at reentry four.1 (by intro current equal; cases equal; exact lastBound)
  exact ⟨five.1, five.2.1, Nat.le_trans one.2.2 (Nat.le_trans two.2.2
    (Nat.le_trans three.2.2 (Nat.le_trans four.2.2 five.2.2)))⟩

theorem dense_fork_pair (condition : ValueId) :
    DenseRun (do
      let (first, last) ← fork condition
      pure (first, last, ())) :=
  DenseRun.bind (dense_fork condition) fun _ => DenseRun.pure _

theorem dense_fork_pair_targets (condition : ValueId) (le : LEnv) (before : LS)
    (pair : BlockId × BlockId × Unit) (after : LS)
    (run : ((do
      let (first, last) ← fork condition
      pure (first, last, ())) : B (BlockId × BlockId × Unit)) le before = (pair, after)) :
    pair.1 < after.blocks.size ∧ pair.2.1 < after.blocks.size := by
  obtain ⟨⟨first, last⟩, middle, forkRun, final⟩ := bind_eq.mp run
  obtain ⟨rfl, rfl⟩ := pure_eq.mp final
  have ids := fork_ids forkRun
  simp only [Prod.mk.injEq] at ids
  obtain ⟨⟨rfl, rfl⟩, size⟩ := ids
  rw [size]
  exact ⟨by nat_omega, by nat_omega⟩

theorem dense_ifS_none_core (condition : ValueId) {body : B ValueId} (works : DenseRun body) :
    DenseRun (whenLive () fun _ => do
      let (thenBlock, join) ← fork condition
      setCur (some thenBlock)
      let _ ← body
      emitTerm (.br join [])
      setCur (some join)) := by
  apply dense_whenLive
  intro block
  exact dense_resume_pair (allocate := do
    let (first, last) ← fork condition
    pure (first, last, ()))
    (body := fun _ _ => body) (back := fun target _ => emitTerm (.br target []))
    (dense_fork_pair condition) (dense_fork_pair_targets condition)
    (fun _ _ => works) (fun _ _ => dense_emitTerm _)

theorem dense_loopBody (condition : ValueId) {body : Nat → BlockId → B ValueId} {back : B Unit}
    (works : ∀ depth target, DenseRun (body depth target)) (backs : DenseRun back) :
    DenseRun (loopBody condition body back) := by
  unfold loopBody
  apply DenseRun.bind dense_get
  intro state
  exact dense_resume_pair (allocate := do
    let (first, last) ← fork condition
    pure (first, last, ()))
    (body := fun target _ => body state.stack.length target) (back := fun _ _ => back)
    (dense_fork_pair condition) (dense_fork_pair_targets condition)
    (fun _ _ => works _ _) (fun _ _ => backs)

theorem dense_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (works : DenseRun rhs) : DenseRun (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  apply dense_whenLive
  intro block
  apply dense_resume_pair (allocates := dense_scFork isAnd value)
    (body := fun _ _ => rhs) (back := fun target result => emitTerm (.br target [result]))
    (works := fun _ _ => works) (backs := fun _ _ => dense_emitTerm _)
  intro le before pair after run
  have ids := scFork_ids run
  rcases pair with ⟨first, last, parameter⟩
  simp only [Prod.mk.injEq] at ids
  obtain ⟨⟨rfl, rfl, rfl⟩, size⟩ := ids
  rw [size]
  exact ⟨by nat_omega, by nat_omega⟩

theorem dense_assert_core (condition : ValueId) (origin : OriginId) :
    DenseRun (whenLive () fun _ => do
      let (pass, fail) ← fork condition
      setCur (some fail)
      emitTerm (.abort .assert (some origin))
      setCur (some pass)) := by
  apply dense_whenLive
  intro block
  apply dense_resume_pair
    (allocate := do
      let (pass, fail) ← fork condition
      pure (fail, pass, ()))
    (body := fun _ _ => emitTerm (.abort .assert (some origin)))
    (back := fun _ _ => pure ())
    (allocates := DenseRun.bind (dense_fork condition) fun _ => DenseRun.pure _)
    (works := fun _ _ => dense_emitTerm _) (backs := fun _ _ => DenseRun.pure _)
  intro le before pair after run
  obtain ⟨⟨pass, fail⟩, middle, forkRun, final⟩ := bind_eq.mp run
  obtain ⟨rfl, rfl⟩ := pure_eq.mp final
  have ids := fork_ids forkRun
  simp only [Prod.mk.injEq] at ids
  obtain ⟨⟨rfl, rfl⟩, size⟩ := ids
  rw [size]
  exact ⟨by nat_omega, by nat_omega⟩

theorem dense_rangeBack (t : IntTy) (i : ValueId) (hb : BlockId) : DenseRun (rangeBack t i hb) := by
  unfold rangeBack
  refine DenseRun.bind dense_isLive fun live => ?_
  cases live
  · exact DenseRun.pure _
  · exact DenseRun.bind (dense_emitDef _) fun _ => dense_emitTerm _


theorem dense_lowerWhile (hb : BlockId) {cond : B ValueId} {body : Nat → BlockId → B ValueId}
    (hc : DenseRun cond) (hbody : ∀ d xb, DenseRun (body d xb)) : DenseRun (lowerWhile hb cond body) := by
  unfold lowerWhile
  exact DenseRun.bind hc fun cv => dense_whenLive _ fun _ =>
    dense_loopBody cv hbody (dense_emitTerm _)

theorem dense_lowerRange (t : IntTy) (i b : ValueId) (hb : BlockId) {body : Nat → BlockId → B ValueId}
    (hbody : ∀ d xb, DenseRun (body d xb)) : DenseRun (lowerRange t i b hb body) := by
  unfold lowerRange
  exact DenseRun.bind (dense_emitDef _) fun c => dense_loopBody c hbody (dense_rangeBack _ _ _)

theorem dense_lowerEach (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (hb : BlockId)
    (i : ValueId) {body : Nat → BlockId → B ValueId} (hbody : ∀ d xb, DenseRun (body d xb)) :
    DenseRun (lowerEach regrow owner sampled hb i body) := by
  unfold lowerEach
  exact DenseRun.bind (dense_eachLen _ _ _) fun n => DenseRun.bind (dense_emitDef _) fun c =>
    dense_loopBody c hbody (dense_rangeBack _ _ _)

mutual

theorem dense_lowerExpr : ∀ e : Expr, DenseRun (lowerExpr e)
  | .structLit t es => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerExprs es) fun _ => dense_emitDef _
  | .lit t n => by simp only [lowerExpr]; exact dense_emitDef _
  | .bool b => by simp only [lowerExpr]; exact dense_emitDef _
  | .read p => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerPlace p) fun _ =>
      DenseRun.bind (dense_emitDef _) fun value =>
        DenseRun.bind (dense_recordReadValueRootRecipe value p) fun _ => DenseRun.pure value
  | .ref m p => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerPlace p) fun r => dense_borrowTo m r
  | .slice m v lo hi org => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerView v) fun _ => DenseRun.bind (dense_lowerBound lo) fun _ =>
      DenseRun.bind (dense_lowerBound hi) fun _ => dense_emitDef _
  | .len v => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerView v) fun _ => dense_emitDef _
  | .un op e org => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerExpr e) fun a => DenseRun.bind (dense_intTyOf a) fun _ => dense_emitDef _
  | .bin op a b org => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerExpr a) fun x => DenseRun.bind (dense_lowerExpr b) fun y =>
      DenseRun.bind (dense_intTyOf x) fun _ => dense_emitDef _
  | .cmp op a b => by
    simp only [lowerExpr]
    refine DenseRun.bind (dense_lowerExpr a) fun x => DenseRun.bind (dense_lowerExpr b) fun y =>
      DenseRun.bind (dense_valTy x) fun t => ?_
    cases t with
    | data t => cases t <;> exact dense_emitDef _
    | view _ _ => exact dense_emitDef _
  | .and a b => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerExpr a) fun x => dense_shortCircuit true x (dense_lowerExpr b)
  | .or a b => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerExpr a) fun x => dense_shortCircuit false x (dense_lowerExpr b)
  | .not e => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerExpr e) fun _ => dense_emitDef _
  | .conv k target e org => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerExpr e) fun a => DenseRun.bind (dense_intTyOf a) fun _ => dense_emitDef _
  | .call c args org => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerArgs args) fun _ =>
      DenseRun.bind (dense_emitDef _) fun r => DenseRun.bind dense_read fun le => by
        cases le.mod.noReturn c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact DenseRun.pure _ | exact DenseRun.bind (dense_emitTerm _) fun _ => DenseRun.pure _
  | .push owner e org => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerPlace owner) fun r => DenseRun.bind (dense_lowerExpr e) fun v =>
      dense_emitDef (.push r v org)
  | .pop owner org => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerPlace owner) fun _ => dense_emitDef _
  | .ifE c t f => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerExpr c) fun cv =>
      dense_ifE_core cv (sourceBlockScope t) (dense_lowerBlock none [] true t) (dense_lowerBlock none [] true f)
  | .blockE b => by
    simp only [lowerExpr]
    exact dense_lowerBlock none [] true b
  | .arrLit t es => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerExprs es) fun _ => dense_emitDef _
  | .fill t e => by
    simp only [lowerExpr]
    exact DenseRun.bind (dense_lowerExpr e) fun _ => dense_emitDef _

theorem dense_lowerExprs : ∀ es : List Expr, DenseRun (lowerExprs es)
  | [] => by simp only [lowerExprs]; exact DenseRun.pure _
  | e :: rest => by
    simp only [lowerExprs]
    exact DenseRun.bind (dense_lowerExpr e) fun _ => DenseRun.bind (dense_lowerExprs rest) fun _ => DenseRun.pure _

theorem dense_lowerArg : ∀ a : Arg, DenseRun (lowerArg a)
  | .byVal e => by simp only [lowerArg]; exact dense_lowerExpr e
  | .byRef m p => by
    simp only [lowerArg]
    exact DenseRun.bind (dense_lowerPlace p) fun r => dense_borrowTo m r

theorem dense_lowerArgs : ∀ as : List Arg, DenseRun (lowerArgs as)
  | [] => by simp only [lowerArgs]; exact DenseRun.pure _
  | a :: rest => by
    simp only [lowerArgs]
    exact DenseRun.bind (dense_lowerArg a) fun _ => DenseRun.bind (dense_lowerArgs rest) fun _ => DenseRun.pure _

theorem dense_lowerPlace : ∀ p : Place, DenseRun (lowerPlace p)
  | .field owner i => by
    simp only [lowerPlace]
    exact DenseRun.bind (dense_lowerPlace owner) fun _ => dense_emitDef _
  | .var x => by simp only [lowerPlace]; exact dense_emitDef _
  | .global g => by simp only [lowerPlace]; exact dense_emitDef _
  | .deref e => by simp only [lowerPlace]; exact dense_lowerExpr e
  | .elem v i org => by
    simp only [lowerPlace]
    exact DenseRun.bind (dense_lowerView v) fun _ => DenseRun.bind (dense_lowerExpr i) fun _ => dense_emitDef _

theorem dense_lowerView : ∀ v : View, DenseRun (lowerView v)
  | .of p => by
    simp only [lowerView]
    exact DenseRun.bind (dense_lowerPlace p) fun _ => dense_emitDef _
  | .val e => by
    simp only [lowerView]
    exact DenseRun.bind (dense_lowerExpr e) fun _ => dense_emitDef _

theorem dense_lowerBound : ∀ b : Bound, DenseRun (lowerBound b)
  | .omitted => by simp only [lowerBound]; exact DenseRun.pure _
  | .expr e => by
    simp only [lowerBound]
    exact DenseRun.bind (dense_lowerExpr e) fun _ => DenseRun.pure _
  | .fromEnd e => by
    simp only [lowerBound]
    exact DenseRun.bind (dense_lowerExpr e) fun _ => DenseRun.pure _

theorem dense_lowerEachSource : ∀ v : View, DenseRun (lowerEachSource v)
  | .of p => by
    simp only [lowerEachSource]
    exact DenseRun.bind (dense_lowerPlace p) fun _ => DenseRun.bind (dense_emitDef _) fun _ => DenseRun.pure _
  | .val e => by
    simp only [lowerEachSource]
    exact DenseRun.bind (dense_lowerExpr e) fun _ => DenseRun.bind (dense_emitDef _) fun _ => DenseRun.pure _

theorem dense_lowerBlockValue (want : Bool) : ∀ v : Option Expr, DenseRun (lowerBlockValue want v)
  | some e => by simp only [lowerBlockValue]; exact dense_lowerExpr e
  | none => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact DenseRun.pure _
    · simp only [lowerBlockValue, ↓reduceIte]; exact dense_emitDef _

theorem dense_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, DenseRun (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    simp only [lowerBlock]
    exact DenseRun.bind (dense_emitEffect _) fun _ => dense_inScope sc
      (DenseRun.bind (dense_initSlots _) fun _ => DenseRun.bind (dense_lowerStmts lc stmts) fun _ =>
        DenseRun.bind (dense_lowerBlockValue want value) fun _ => DenseRun.bind (dense_emitEffect _) fun _ =>
        DenseRun.pure _)

theorem dense_lowerStmts (lc : Option LoopCtx) : ∀ ss : List Stmt, DenseRun (lowerStmts lc ss)
  | [] => by simp only [lowerStmts]; exact DenseRun.pure _
  | s :: rest => by
    simp only [lowerStmts]
    refine DenseRun.bind dense_isLive fun live => ?_
    cases live
    · exact DenseRun.pure _
    · exact DenseRun.bind (dense_lowerStmt lc s) fun _ => dense_lowerStmts lc rest

theorem dense_lowerPrintArgs : ∀ as : List PrintArg, DenseRun (lowerPrintArgs as)
  | [] => by simp only [lowerPrintArgs]; exact DenseRun.pure _
  | .text s :: rest => by
    simp only [lowerPrintArgs]
    exact DenseRun.bind (dense_lowerPrintArgs rest) fun _ => DenseRun.pure _
  | .expr e :: rest => by
    simp only [lowerPrintArgs]
    exact DenseRun.bind (dense_lowerExpr e) fun _ => DenseRun.bind (dense_lowerPrintArgs rest) fun _ => DenseRun.pure _

theorem dense_lowerStmt (lc : Option LoopCtx) : ∀ s : Stmt, DenseRun (lowerStmt lc s)
  | .letS x e org => by
    simp only [lowerStmt]
    exact DenseRun.bind (dense_lowerExpr e) fun value =>
      DenseRun.bind (dense_coerceSlot x value org) fun _ => dense_emitEffect _
  | .assign p e org => by
    simp only [lowerStmt]
    exact DenseRun.bind (dense_lowerPlace p) fun _ => DenseRun.bind (dense_lowerExpr e) fun _ => dense_emitEffect _
  | .assignOp op p e org => by
    simp only [lowerStmt]
    exact DenseRun.bind (dense_lowerPlace p) fun _ => DenseRun.bind (dense_emitDef _) fun _ =>
      DenseRun.bind (dense_lowerExpr e) fun _ => DenseRun.bind (dense_intTyOf _) fun _ =>
      DenseRun.bind (dense_emitDef _) fun _ => dense_emitEffect _
  | .rebind x e org => by
    simp only [lowerStmt]
    exact DenseRun.bind (dense_lowerExpr e) fun value =>
      DenseRun.bind (dense_coerceSlot x value org) fun _ =>
        DenseRun.bind (dense_emitDef _) fun _ => dense_emitEffect _
  | .expr e _ => by
    simp only [lowerStmt]
    exact DenseRun.bind (dense_lowerExpr e) fun _ => DenseRun.pure _
  | .append owner src org => by
    simp only [lowerStmt]
    exact DenseRun.bind (dense_lowerPlace owner) fun _ => DenseRun.bind (dense_lowerView src) fun _ =>
      dense_emitEffect _
  | .popN owner count org => by
    simp only [lowerStmt]
    exact DenseRun.bind (dense_lowerPlace owner) fun r => DenseRun.bind (dense_lowerExpr count) fun n =>
      dense_emitEffect (.popN r n (some org))
  | .resize owner size none org => by
    simp only [lowerStmt]
    exact DenseRun.bind (dense_lowerPlace owner) fun r => DenseRun.bind (dense_lowerExpr size) fun n =>
      DenseRun.bind (DenseRun.pure _) fun fill => dense_emitEffect (.resize r n fill (some org))
  | .resize owner size (some fill) org => by
    simp only [lowerStmt]
    exact DenseRun.bind (dense_lowerPlace owner) fun r => DenseRun.bind (dense_lowerExpr size) fun n =>
      DenseRun.bind (dense_lowerExpr fill) fun v =>
        dense_emitEffect (.resize r n (some v) (some org))
  | .clear owner org => by
    simp only [lowerStmt]
    exact DenseRun.bind (dense_lowerPlace owner) fun r => dense_emitEffect (.clear r (some org))
  | .assignWhole owner replacement org => by
    simp only [lowerStmt]
    exact DenseRun.bind (dense_lowerPlace owner) fun r =>
      DenseRun.bind (dense_emitEffect (.clear r (some org))) fun _ =>
      DenseRun.bind (dense_lowerExpr replacement) fun run =>
        dense_emitEffect (.replace r run (some org))
  | .ifS c t f _ => by
    cases f with
    | none =>
      simp only [lowerStmt]
      exact DenseRun.bind (dense_lowerExpr c) fun cv => dense_ifS_none_core cv (dense_lowerBlock lc [] false t)
    | some fb =>
      simp only [lowerStmt]
      exact DenseRun.bind (dense_lowerExpr c) fun cv =>
        dense_ifS_some_core cv (dense_lowerBlock lc [] false t) (dense_lowerBlock lc [] false fb)
  | .while c body _ => by
    simp only [lowerStmt]
    exact dense_header0 (tail := fun hb => lowerWhile hb (lowerExpr c)
        (fun d xb => lowerBlock (some ⟨d, xb, .jump hb⟩) [] false body))
      (fun hb => dense_lowerWhile hb (dense_lowerExpr c) (fun d xb => dense_lowerBlock _ _ _ body))
  | .forRange x lo hi body org => by
    simp only [lowerStmt]
    refine DenseRun.bind (dense_lowerExpr lo) fun a => DenseRun.bind (dense_lowerExpr hi) fun b =>
      dense_whenLive _ fun _ => DenseRun.bind (dense_intTyOf a) fun t => ?_
    exact dense_header1 (.data (.int t)) a (tail := fun hb i => lowerRange t i b hb (fun d xb =>
        lowerBlock (some ⟨d, xb, .next hb t i⟩) [(x, i, org)] false body))
      (fun hb i => dense_lowerRange t i b hb (fun d xb => dense_lowerBlock _ _ _ body))
  | .forEach x idx v byRef body org => by
    simp only [lowerStmt]
    refine DenseRun.bind (dense_lowerEachSource v) fun ov => DenseRun.bind (dense_regrowOf _) fun regrow =>
      DenseRun.bind (dense_eachSampled _ _) fun sampled => DenseRun.bind (dense_emitDef _) fun startAt =>
      dense_whenLive _ fun _ => ?_
    exact dense_header1 (.data (.int .i64)) startAt (tail := fun hb i =>
        lowerEach regrow ov.1 sampled hb i (fun d xb => do
          let elem ← emitDef (.refElem ov.2 i)
          let ev ← eachElemValue x byRef elem
          let pre := (x, ev, org) :: (match idx with
            | some j => [(j, i, org)]
            | none => [])
          lowerBlock (some ⟨d, xb, .next hb .i64 i⟩) pre false body))
      (fun hb i => dense_lowerEach regrow ov.1 sampled hb i (fun d xb =>
        DenseRun.bind (dense_emitDef _) fun elem => DenseRun.bind (dense_eachElemValue _ _ _) fun ev =>
          dense_lowerBlock _ _ _ body))
  | .ret e org => by
    cases e with
    | some e =>
      simp only [lowerStmt]
      exact DenseRun.bind (dense_lowerExpr e) fun value =>
        DenseRun.bind (dense_coerceResult value org) fun _ =>
          DenseRun.bind (DenseRun.pure _) fun _ =>
            DenseRun.bind (dense_leaveTo 0) fun _ => dense_emitTerm _
    | none =>
      simp only [lowerStmt]
      exact DenseRun.bind (DenseRun.pure _) fun _ => DenseRun.bind (dense_leaveTo 0) fun _ => dense_emitTerm _
  | .brk _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact DenseRun.pure _
    | some l =>
      simp only [lowerStmt]
      exact DenseRun.bind (dense_leaveTo _) fun _ => dense_emitTerm _
  | .cont _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact DenseRun.pure _
    | some l =>
      cases hk : l.cont with
      | jump h =>
        simp only [lowerStmt, hk]
        exact DenseRun.bind (dense_leaveTo _) fun _ => dense_emitTerm _
      | next h t i =>
        simp only [lowerStmt, hk]
        exact DenseRun.bind (dense_leaveTo _) fun _ => DenseRun.bind (dense_emitDef _) fun _ => dense_emitTerm _
  | .print args org => by
    simp only [lowerStmt]
    exact DenseRun.bind (dense_lowerPrintArgs args) fun _ => dense_emitEffect _
  | .assertS e org => by
    simp only [lowerStmt]
    exact DenseRun.bind (dense_lowerExpr e) fun cv => dense_assert_core cv org
  | .abort _ org => by
    simp only [lowerStmt]
    exact dense_emitTerm _
  | .exit e org => by
    simp only [lowerStmt]
    exact DenseRun.bind (dense_lowerExpr e) fun _ => dense_emitTerm _

end


theorem dense_finishFunction (impl : Impl) (value : ValueId) :
    DenseRun (finishFunction impl value) := by
  unfold finishFunction
  refine DenseRun.bind dense_read fun le => DenseRun.bind dense_isLive fun live => ?_
  cases live
  · exact DenseRun.pure _
  · by_cases sink : (!impl.results.isEmpty && impl.body.value.isNone &&
        impl.body.diverges le.mod.noReturn) = true
    · simp only [sink, ite_true]
      exact dense_newBlock_resume []
        (prepare := fun target _ => emitTerm (.br target []))
        (tail := fun target _ => emitTerm (.br target []))
        (fun _ _ => dense_emitTerm _) (fun _ _ => dense_emitTerm _)
    · simp only [sink]
      exact dense_emitTerm _

private theorem definition_filter_length (instructions : List Inst) :
    (instructions.filterMap fun | .def value _ => some value | _ => none).length =
      (instructions.filter fun | .def .. => true | _ => false).length := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih => cases instruction <;> simp_all

theorem Func.numValues_eq_definition_count (func : Func) :
    func.numValues = (func.blocks.toList.flatMap GIR.Block.defs).length := by
  have blockCount (block : GIR.Block) :
      block.params.length + (block.insts.filter fun | .def .. => true | _ => false).length =
        block.defs.length := by
    simp only [GIR.Block.defs, List.length_append, List.length_map]
    exact congrArg (block.params.length + ·) (definition_filter_length block.insts).symm
  have count (blocks : List GIR.Block) (start : Nat) :
      blocks.foldl (fun number block => number + block.defs.length) start =
        start + (blocks.flatMap GIR.Block.defs).length := by
    induction blocks generalizing start with
    | nil => simp
    | cons block rest ih => simp [ih, Nat.add_assoc]
  unfold Func.numValues
  have functions : (fun (number : Nat) (block : GIR.Block) => number +
      (block.params.length + (block.insts.filter fun | .def .. => true | _ => false).length)) =
      (fun number block => number + block.defs.length) := by
    funext number block
    rw [blockCount]
  apply Eq.trans (congrArg (fun step : Nat → GIR.Block → Nat => func.blocks.foldl step 0) functions)
  rw [← Array.foldl_toList]
  simpa only [Nat.zero_add] using count func.blocks.toList 0

theorem dense_finishBlocks {state : LS} (checked : state.DenseDefinitions) {func : Func}
    (blocks : func.blocks = finishBlocks state.blocks) :
    (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues) := by
  rw [Func.numValues_eq_definition_count, blocks, finishBlocks_defs]
  change state.defs.Perm (List.range state.defs.length)
  rw [checked.length]
  exact checked

theorem Func.parameter_ids_bounded_of_dense {func : Func}
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues)) :
    ∀ block ∈ func.blocks.toList, ∀ param ∈ block.params, param.1 < func.numValues := by
  intro block member param parameter
  apply List.mem_range.mp
  apply dense.mem_iff.mp
  apply List.mem_flatMap.mpr
  refine ⟨block, member, ?_⟩
  simp only [GIR.Block.defs, List.mem_append, List.mem_map]
  exact Or.inl ⟨param, parameter, rfl⟩

theorem Func.parameter_ids_distinct_of_dense {func : Func}
    (dense : (func.blocks.toList.flatMap GIR.Block.defs).Perm (List.range func.numValues))
    {block : GIR.Block} (member : block ∈ func.blocks.toList) :
    (block.params.map Prod.fst).Nodup := by
  have sublist : block.defs.Sublist (func.blocks.toList.flatMap GIR.Block.defs) :=
    List.sublist_flatten_of_mem (List.mem_map.mpr ⟨block, member, rfl⟩)
  have distinct := sublist.nodup (dense.nodup_iff.mpr List.nodup_range)
  exact (List.nodup_append.mp distinct).1

theorem dense_cfg_implAction (impl : Core.Impl) : DenseRun (cfg_implAction impl) := by
  intro le before result after run checked bounded
  simp only [cfg_implAction, bind_eq] at run
  obtain ⟨⟨entry, params⟩, allocated, allocation, _, entered, entryRun,
    value, bodyState, bodyRun, finished⟩ := run
  have one := dense_newBlock _ le before _ allocated allocation checked bounded
  have fresh := liveBound_newBlock (impl.params.toList.map fun param => .data (tyOfVar impl param.var)) le before
  rw [allocation] at fresh
  have two := dense_setCur_at entryRun one.1 (by intro current equal; cases equal; exact fresh)
  have three := dense_lowerBlock _ _ _ _ le entered value bodyState bodyRun two.1 two.2.1
  have four := dense_finishFunction impl value le bodyState result after finished three.1 three.2.1
  exact ⟨four.1, four.2.1, Nat.le_trans one.2.2 (Nat.le_trans two.2.2 (Nat.le_trans three.2.2 four.2.2))⟩

theorem dense_cfg_globalAction (global : Core.Global) : DenseRun (cfg_globalAction global) := by
  intro le before result after run checked bounded
  simp only [cfg_globalAction, bind_eq] at run
  obtain ⟨⟨entry, params⟩, allocated, allocation, _, entered, entryRun,
    value, bodyState, bodyRun, finished⟩ := run
  have one := dense_newBlock [] le before _ allocated allocation checked bounded
  have fresh := liveBound_newBlock [] le before
  rw [allocation] at fresh
  have two := dense_setCur_at entryRun one.1 (by intro current equal; cases equal; exact fresh)
  have three := dense_lowerExpr global.init le entered value bodyState bodyRun two.1 two.2.1
  have four := dense_emitTerm (.ret [value] (some global.org)) le bodyState result after finished three.1 three.2.1
  exact ⟨four.1, four.2.1, Nat.le_trans one.2.2 (Nat.le_trans two.2.2 (Nat.le_trans three.2.2 four.2.2))⟩

theorem lowerImplState_denseDefinitions (module : Core.Module) (impl : Core.Impl) :
    (lowerImplState module impl).DenseDefinitions :=
  (dense_cfg_implAction impl (lowerEnv module impl.vars impl.results.toList) initState _ _ rfl
    LS.denseDefinitions_initState liveBound_initState).1

theorem cfg_globalState_denseDefinitions (module : Core.Module) (global : Core.Global) :
    (cfg_globalState module global).DenseDefinitions :=
  (dense_cfg_globalAction global (lowerEnv module #[] [global.ty]) initState _ _ rfl
    LS.denseDefinitions_initState liveBound_initState).1

theorem dense_values_eq_numValues {state : LS} {func : Func} (checked : state.DenseDefinitions)
    (blocks : func.blocks = finishBlocks state.blocks) : state.vals.size = func.numValues := by
  rw [Func.numValues_eq_definition_count, blocks, finishBlocks_defs]
  simpa only [List.length_range, LS.defs] using checked.length.symm

theorem lowerImplState_numValues (module : Core.Module) (impl : Core.Impl) :
    (lowerImplState module impl).vals.size = (lowerImpl module impl).numValues :=
  dense_values_eq_numValues (lowerImplState_denseDefinitions module impl) rfl

theorem lowerContextAt_state_numValues (module : Core.Module) (context : Context) (impl : Core.Impl) :
    (lowerImplState module impl).vals.size = (lowerContextAt module context impl).numValues :=
  dense_values_eq_numValues (lowerImplState_denseDefinitions module impl) rfl

theorem lowerGlobal_state_numValues (module : Core.Module) (global : Core.Global) :
    (cfg_globalState module global).vals.size = (lowerGlobal module global).init.numValues :=
  dense_values_eq_numValues (cfg_globalState_denseDefinitions module global) rfl

theorem lowerImpl_dense_definitions (module : Core.Module) (impl : Core.Impl) :
    ((lowerImpl module impl).blocks.toList.flatMap GIR.Block.defs).Perm
      (List.range (lowerImpl module impl).numValues) :=
  dense_finishBlocks (lowerImplState_denseDefinitions module impl) rfl

theorem lowerGlobal_dense_definitions (module : Core.Module) (global : Core.Global) :
    ((lowerGlobal module global).init.blocks.toList.flatMap GIR.Block.defs).Perm
      (List.range (lowerGlobal module global).init.numValues) :=
  dense_finishBlocks (cfg_globalState_denseDefinitions module global) rfl

#print axioms lowerImplState_denseDefinitions
#print axioms cfg_globalState_denseDefinitions
#print axioms lowerContextAt_state_numValues
#print axioms lowerGlobal_state_numValues

end Goose.Lower.Validation
