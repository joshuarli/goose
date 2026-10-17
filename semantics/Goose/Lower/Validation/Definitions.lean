import Goose.Lower.Validation.Typing

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def DefinitionsValid (state : LS) : Prop :=
  state.defs.Nodup ∧ ∀ value ∈ state.defs, value < state.vals.size

def DefinitionRun (action : B α) : Prop :=
  ∀ le before result after, action le before = (result, after) →
    DefinitionsValid before → DefinitionsValid after

theorem DefinitionRun.pure (value : α) : DefinitionRun (pure value) := by
  intro le before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact checked

theorem DefinitionRun.bind {action : B α} {next : α → B β}
    (first : DefinitionRun action) (second : ∀ value, DefinitionRun (next value)) :
    DefinitionRun (action >>= next) := by
  intro le before result after run checked
  obtain ⟨value, mid, firstRun, secondRun⟩ := bind_eq.mp run
  exact second value _ _ _ _ secondRun (first _ _ _ _ firstRun checked)

theorem DefinitionRun.of_unchanged {action : B α}
    (unchanged : ∀ le state, (action le state).2.defs = state.defs ∧
      (action le state).2.vals.size = state.vals.size) : DefinitionRun action := by
  intro le before result after run checked
  obtain ⟨defs, size⟩ := unchanged le before
  rw [run] at defs size
  simpa only [DefinitionsValid, defs, size] using checked

private theorem flatMap_modify_append {α β : Type} (f : α → List β) (xs : List α) (i : Nat)
    (g : α → α) (extra : List β) (bound : i < xs.length)
    (update : ∀ x, f (g x) = f x ++ extra) :
    List.Perm ((xs.modify i g).flatMap f) (xs.flatMap f ++ extra) := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at bound
    | cons x xs =>
      have swap : List.Perm (extra ++ xs.flatMap f) (xs.flatMap f ++ extra) := List.perm_append_comm
      simp only [List.modify_zero_cons, List.flatMap_cons, update]
      simpa [List.append_assoc] using List.Perm.append_left (f x) swap
  | succ i ih =>
    cases xs with
    | nil => simp at bound
    | cons x xs =>
      have smaller : i < xs.length := by simpa using bound
      simp only [List.modify_succ_cons, List.flatMap_cons]
      simpa [List.append_assoc] using List.Perm.append_left (f x) (ih xs smaller)

private theorem definitions_append (before : LS) (checked : DefinitionsValid before)
    {defs : List ValueId} {size : Nat} (fresh : defs.Nodup)
    (newLower : ∀ value ∈ defs, before.vals.size ≤ value)
    (newUpper : ∀ value ∈ defs, value < size) (grows : before.vals.size ≤ size) :
    (before.defs ++ defs).Nodup ∧ ∀ value ∈ before.defs ++ defs, value < size := by
  constructor
  · apply List.nodup_append.mpr
    refine ⟨checked.1, fresh, ?_⟩
    intro old oldMember next nextMember equal
    have oldBound := checked.2 old oldMember
    have newBound := newLower next nextMember
    subst next
    exact (Nat.not_le_of_lt oldBound) newBound
  · intro value member
    rcases List.mem_append.mp member with old | new
    · exact Nat.lt_of_lt_of_le (checked.2 value old) grows
    · exact newUpper value new

theorem definitions_emitDef (op : Op) : DefinitionRun (emitDef op) := by
  intro le before result after run checked
  cases current : before.cur with
  | none =>
    rw [emitDef_none op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitDef_run op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    by_cases bound : block < before.blocks.size
    · have perm : ((before.blocks.modify block fun blk =>
          { blk with insts := blk.insts.push (.def before.vals.size op) }).toList.flatMap BlockB.defs).Perm
          (before.defs ++ [before.vals.size]) := by
        simpa [LS.defs, Array.toList_modify] using
          flatMap_modify_append BlockB.defs before.blocks.toList block
            (fun blk => { blk with insts := blk.insts.push (.def before.vals.size op) })
            [before.vals.size] (by simpa using bound)
            (by intro blk; simp [BlockB.defs, List.filterMap_append])
      have appended := definitions_append before checked (defs := [before.vals.size])
        (size := before.vals.size + 1) (by simp) (by simp) (by simp) (by omega)
      refine ⟨perm.nodup_iff.mpr appended.1, ?_⟩
      intro value member
      have bounded := appended.2 value (perm.mem_iff.mp member)
      simpa using bounded
    · have same : (before.blocks.modify block fun blk =>
          { blk with insts := blk.insts.push (.def before.vals.size op) }).toList = before.blocks.toList := by
        rw [Array.toList_modify, List.modify_eq_self (by simpa using Nat.le_of_not_gt bound)]
      constructor
      · simpa only [LS.defs, same] using checked.1
      · intro value member
        have oldMember : value ∈ before.defs := by simpa only [LS.defs, same] using member
        have oldBound := checked.2 value oldMember
        simpa using Nat.lt_trans oldBound (Nat.lt_succ_self _)

theorem definitions_newBlock (types : List VTy) : DefinitionRun (newBlock types) := by
  intro le before result after run checked
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  have ids : ((paramIds types before.vals).zip types).map Prod.fst = paramIds types before.vals :=
    List.map_fst_zip (by simp [paramIds])
  have defs :
      ({ before with
        blocks := before.blocks.push ⟨(paramIds types before.vals).zip types, #[]⟩
        vals := pushParamTypes types before.vals }).defs = before.defs ++ paramIds types before.vals := by
    simp [LS.defs, BlockB.defs, ids]
  rw [DefinitionsValid, defs, array_size_pushParamTypes]
  apply definitions_append before checked
  · simpa only [paramIds, ← List.range'_eq_map_range] using (List.nodup_range' (s := before.vals.size) (n := types.length))
  · intro value member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    omega
  · intro value member
    obtain ⟨index, indexMember, rfl⟩ := List.mem_map.mp member
    have bound := List.mem_range.mp indexMember
    exact Nat.add_lt_add_left bound _
  · omega

private theorem defs_appendInst {state : LS} {block : BlockId} {inst : Inst}
    (noDefs : (match inst with | .def .. => False | _ => True)) :
    (state.appendInst block inst).defs = state.defs := by
  change (state.blocks.modify block _).toList.flatMap BlockB.defs = state.blocks.toList.flatMap BlockB.defs
  rw [Array.toList_modify]
  generalize state.blocks.toList = blocks
  induction block generalizing blocks with
  | zero => cases blocks <;> cases inst <;> simp_all [List.modify, BlockB.defs, List.filterMap_append]
  | succ block ih =>
    cases blocks with
    | nil => rfl
    | cons blk blocks => simpa using congrArg (BlockB.defs blk ++ ·) (ih blocks)

theorem definitions_emitEffect (effect : Effect) : DefinitionRun (emitEffect effect) := by
  apply DefinitionRun.of_unchanged
  intro le state
  cases current : state.cur with
  | none => rw [emitEffect_none effect le current]; exact ⟨rfl, rfl⟩
  | some block =>
    rw [emitEffect_run effect le current]
    exact ⟨defs_appendInst (by trivial), rfl⟩

theorem definitions_setCur (block : Option BlockId) : DefinitionRun (setCur block) := by
  apply DefinitionRun.of_unchanged
  intro le state
  rw [setCur_run]
  exact ⟨rfl, rfl⟩

theorem definitions_emitTerm (term : Term) : DefinitionRun (emitTerm term) := by
  apply DefinitionRun.of_unchanged
  intro le state
  cases current : state.cur with
  | none => rw [emitTerm_none term le current]; exact ⟨rfl, rfl⟩
  | some block =>
    rw [emitTerm_run term le current]
    exact ⟨defs_appendInst (by trivial), rfl⟩

theorem definitions_patchTerm (block : BlockId) (term : Term) : DefinitionRun (patchTerm block term) := by
  apply DefinitionRun.of_unchanged
  intro le state
  rw [patchTerm_run]
  exact ⟨defs_appendInst (by trivial), rfl⟩

theorem definitions_curBlock : DefinitionRun curBlock := by
  apply DefinitionRun.of_unchanged
  intros
  exact ⟨rfl, rfl⟩

theorem definitions_get : DefinitionRun (get : B LS) := by
  apply DefinitionRun.of_unchanged
  intros
  exact ⟨rfl, rfl⟩

theorem definitions_read : DefinitionRun (read : B LEnv) := by
  apply DefinitionRun.of_unchanged
  intros
  exact ⟨rfl, rfl⟩

theorem definitions_valTy (value : ValueId) : DefinitionRun (valTy value) := by
  apply DefinitionRun.of_unchanged
  intro le state
  rw [valTy_run]
  exact ⟨rfl, rfl⟩

theorem definitions_pushScope (scope : ScopeId) : DefinitionRun (pushScope scope) := by
  apply DefinitionRun.of_unchanged
  intros
  exact ⟨rfl, rfl⟩

theorem definitions_popScope : DefinitionRun popScope := by
  apply DefinitionRun.of_unchanged
  intros
  exact ⟨rfl, rfl⟩

theorem definitions_inScope (scope : ScopeId) {action : B α} (typed : DefinitionRun action) :
    DefinitionRun (inScope scope action) := by
  unfold inScope
  exact DefinitionRun.bind (definitions_pushScope _) fun _ =>
    DefinitionRun.bind typed fun _ => DefinitionRun.bind definitions_popScope fun _ => DefinitionRun.pure _

theorem definitions_whenLive (default : α) {action : BlockId → B α}
    (typed : ∀ block, DefinitionRun (action block)) : DefinitionRun (whenLive default action) := by
  unfold whenLive
  refine DefinitionRun.bind definitions_curBlock fun current => ?_
  cases current
  · exact DefinitionRun.pure _
  · exact typed _

theorem definitions_intTyOf (v : ValueId) : DefinitionRun (intTyOf v) := by
  unfold intTyOf
  refine DefinitionRun.bind (definitions_valTy v) fun t => ?_
  cases t with
  | data t => cases t <;> exact DefinitionRun.pure _
  | view _ _ => exact DefinitionRun.pure _

theorem definitions_freezeTo (m : Mutability) (r : ValueId) : DefinitionRun (freezeTo m r) := by
  unfold freezeTo
  refine DefinitionRun.bind (definitions_valTy r) fun t => ?_
  cases m <;> cases t <;> first
    | exact DefinitionRun.pure _
    | (rename_i t; cases t <;> first | exact DefinitionRun.pure _ | (rename_i m' _; cases m' <;> first | exact DefinitionRun.pure _ | exact definitions_emitDef _))

theorem definitions_coerceTo (target : Ty) (r : ValueId) (org : OriginId) : DefinitionRun (coerceTo target r org) := by
  unfold coerceTo
  refine DefinitionRun.bind (definitions_valTy r) fun source => ?_
  split
  · exact definitions_emitDef _
  · exact DefinitionRun.bind (definitions_emitDef _) (fun _ => definitions_emitDef _)
  · exact DefinitionRun.pure _

theorem definitions_coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) :
    DefinitionRun (coerceSlot slot value org) := by
  unfold coerceSlot
  refine DefinitionRun.bind definitions_read fun le => ?_
  cases le.slots[slot]? with
  | none => exact DefinitionRun.pure _
  | some destination => exact definitions_coerceTo destination.ty value org

theorem definitions_coerceResult (value : ValueId) (org : OriginId) :
    DefinitionRun (coerceResult value org) := by
  unfold coerceResult
  refine DefinitionRun.bind definitions_read fun le => ?_
  cases le.results.head? with
  | none => exact DefinitionRun.pure _
  | some destination => exact definitions_coerceTo destination value org

theorem definitions_growOwner (r : ValueId) : DefinitionRun (growOwner r) := by
  unfold growOwner
  refine DefinitionRun.bind (definitions_valTy r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact DefinitionRun.pure _ | (rename_i m' t'; cases t' <;> exact DefinitionRun.pure _)
  | view _ _ => exact DefinitionRun.pure _

theorem definitions_leaveAll : ∀ scs, DefinitionRun (leaveAll scs)
  | [] => DefinitionRun.pure _
  | sc :: rest => by
    unfold leaveAll
    exact DefinitionRun.bind (definitions_emitEffect _) fun _ => definitions_leaveAll rest

theorem definitions_leaveTo (d : Nat) : DefinitionRun (leaveTo d) := by
  unfold leaveTo
  exact DefinitionRun.bind definitions_get fun _ => definitions_leaveAll _

theorem definitions_initSlots : ∀ ps, DefinitionRun (initSlots ps)
  | [] => DefinitionRun.pure _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact DefinitionRun.bind (definitions_emitEffect _) fun _ => definitions_initSlots rest

theorem definitions_isLive : DefinitionRun isLive := by
  unfold isLive
  exact DefinitionRun.bind definitions_curBlock fun _ => DefinitionRun.pure _

theorem definitions_eachElemValue (x : VarId) (byRef : Bool) (elem : ValueId) :
    DefinitionRun (eachElemValue x byRef elem) := by
  unfold eachElemValue
  cases byRef
  · exact definitions_emitDef _
  · refine DefinitionRun.bind definitions_read fun le => ?_
    cases le.vars[x]? with
    | none => exact DefinitionRun.pure _
    | some lv =>
      dsimp only
      cases lv.ty with
      | ref m t => exact definitions_freezeTo m elem
      | _ => exact DefinitionRun.pure _

theorem definitions_regrowOf (o : Option ValueId) : DefinitionRun (regrowOf o) := by
  cases o with
  | none => exact DefinitionRun.pure _
  | some r => exact definitions_growOwner r

theorem definitions_eachSampled (regrow : Bool) (vw : ValueId) : DefinitionRun (eachSampled regrow vw) := by
  unfold eachSampled
  cases regrow
  · exact definitions_emitDef _
  · exact DefinitionRun.pure _

theorem definitions_eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    DefinitionRun (eachLen regrow owner sampled) := by
  unfold eachLen
  cases regrow
  · exact DefinitionRun.pure _
  · exact definitions_emitDef _

theorem definitions_fork (condition : ValueId) : DefinitionRun (fork condition) := by
  unfold fork
  exact DefinitionRun.bind (definitions_newBlock _) fun ⟨thenBlock, _⟩ =>
    DefinitionRun.bind (definitions_newBlock _) fun ⟨elseBlock, _⟩ =>
    DefinitionRun.bind (definitions_emitTerm _) fun _ => DefinitionRun.pure _

theorem definitions_patchBrs (target : BlockId) : ∀ incoming, DefinitionRun (patchBrs target incoming)
  | [] => DefinitionRun.pure _
  | (block, value) :: rest => by
    unfold patchBrs
    exact DefinitionRun.bind (definitions_patchTerm _ _) fun _ => definitions_patchBrs target rest

theorem definitions_patchBrs0 (target : BlockId) : ∀ incoming, DefinitionRun (patchBrs0 target incoming)
  | [] => DefinitionRun.pure _
  | block :: rest => by
    unfold patchBrs0
    exact DefinitionRun.bind (definitions_patchTerm _ _) fun _ => definitions_patchBrs0 target rest

theorem definitions_joinValue (endT : Option BlockId) (vt : ValueId) (endF : Option BlockId) (vf : ValueId) :
    DefinitionRun (joinValue endT vt endF vf) := by
  unfold joinValue
  cases endT <;> cases endF
  · exact DefinitionRun.bind (definitions_setCur _) fun _ => DefinitionRun.pure _
  all_goals
    exact DefinitionRun.bind (definitions_valTy _) fun _ =>
      DefinitionRun.bind (definitions_newBlock _) fun ⟨_, _⟩ =>
      DefinitionRun.bind (definitions_patchBrs _ _) fun _ =>
      DefinitionRun.bind (definitions_setCur _) fun _ => DefinitionRun.pure _

theorem definitions_joinArms (endT endF : Option BlockId) : DefinitionRun (joinArms endT endF) := by
  unfold joinArms
  cases endT <;> cases endF
  · exact definitions_setCur _
  all_goals
    exact DefinitionRun.bind (definitions_newBlock _) fun ⟨_, _⟩ =>
      DefinitionRun.bind (definitions_patchBrs0 _ _) fun _ => definitions_setCur _

theorem definitions_scFork (isAnd : Bool) (value : ValueId) : DefinitionRun (scFork isAnd value) := by
  unfold scFork
  refine DefinitionRun.bind (definitions_newBlock _) fun ⟨_, _⟩ =>
    DefinitionRun.bind (definitions_newBlock _) fun ⟨_, _⟩ => ?_
  cases isAnd <;> exact DefinitionRun.bind (definitions_emitTerm _) fun _ => DefinitionRun.pure _

theorem definitions_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (typed : DefinitionRun rhs) : DefinitionRun (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  exact definitions_whenLive _ fun _ =>
    DefinitionRun.bind (definitions_scFork _ _) fun ⟨_, _, _⟩ =>
    DefinitionRun.bind (definitions_setCur _) fun _ => DefinitionRun.bind typed fun _ =>
    DefinitionRun.bind (definitions_emitTerm _) fun _ =>
    DefinitionRun.bind (definitions_setCur _) fun _ => DefinitionRun.pure _

theorem definitions_loopBody (cv : ValueId) {body : Nat → BlockId → B ValueId} {back : B Unit}
    (hbody : ∀ depth exitBlock, DefinitionRun (body depth exitBlock)) (hback : DefinitionRun back) :
    DefinitionRun (loopBody cv body back) := by
  unfold loopBody
  exact DefinitionRun.bind definitions_get fun _ =>
    DefinitionRun.bind (definitions_fork _) fun ⟨_, _⟩ =>
    DefinitionRun.bind (definitions_setCur _) fun _ => DefinitionRun.bind (hbody _ _) fun _ =>
    DefinitionRun.bind hback fun _ => definitions_setCur _

theorem definitions_rangeBack (t : IntTy) (i : ValueId) (hb : BlockId) : DefinitionRun (rangeBack t i hb) := by
  unfold rangeBack
  refine DefinitionRun.bind definitions_isLive fun live => ?_
  cases live
  · exact DefinitionRun.pure _
  · exact DefinitionRun.bind (definitions_emitDef _) fun _ => definitions_emitTerm _


theorem definitions_lowerWhile (hb : BlockId) {cond : B ValueId} {body : Nat → BlockId → B ValueId}
    (hc : DefinitionRun cond) (hbody : ∀ d xb, DefinitionRun (body d xb)) : DefinitionRun (lowerWhile hb cond body) := by
  unfold lowerWhile
  exact DefinitionRun.bind hc fun cv => definitions_whenLive _ fun _ =>
    definitions_loopBody cv hbody (definitions_emitTerm _)

theorem definitions_lowerRange (t : IntTy) (i b : ValueId) (hb : BlockId) {body : Nat → BlockId → B ValueId}
    (hbody : ∀ d xb, DefinitionRun (body d xb)) : DefinitionRun (lowerRange t i b hb body) := by
  unfold lowerRange
  exact DefinitionRun.bind (definitions_emitDef _) fun c => definitions_loopBody c hbody (definitions_rangeBack _ _ _)

theorem definitions_lowerEach (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (hb : BlockId)
    (i : ValueId) {body : Nat → BlockId → B ValueId} (hbody : ∀ d xb, DefinitionRun (body d xb)) :
    DefinitionRun (lowerEach regrow owner sampled hb i body) := by
  unfold lowerEach
  exact DefinitionRun.bind (definitions_eachLen _ _ _) fun n => DefinitionRun.bind (definitions_emitDef _) fun c =>
    definitions_loopBody c hbody (definitions_rangeBack _ _ _)

theorem definitions_ifE_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : DefinitionRun a1) (h2 : DefinitionRun a2) :
    DefinitionRun (whenLive 0 fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let vt ← a1
      let endT ← curBlock
      setCur (some eb)
      let vf ← a2
      let endF ← curBlock
      joinValue endT vt endF vf) := by
  exact definitions_whenLive _ fun _ =>
    DefinitionRun.bind (definitions_fork _) fun ⟨_, _⟩ =>
    DefinitionRun.bind (definitions_setCur _) fun _ => DefinitionRun.bind h1 fun _ =>
    DefinitionRun.bind definitions_curBlock fun _ => DefinitionRun.bind (definitions_setCur _) fun _ =>
    DefinitionRun.bind h2 fun _ => DefinitionRun.bind definitions_curBlock fun _ => definitions_joinValue _ _ _ _

theorem definitions_ifS_some_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : DefinitionRun a1) (h2 : DefinitionRun a2) :
    DefinitionRun (whenLive () fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let _ ← a1
      let endT ← curBlock
      setCur (some eb)
      let _ ← a2
      let endF ← curBlock
      joinArms endT endF) := by
  exact definitions_whenLive _ fun _ =>
    DefinitionRun.bind (definitions_fork _) fun ⟨_, _⟩ =>
    DefinitionRun.bind (definitions_setCur _) fun _ => DefinitionRun.bind h1 fun _ =>
    DefinitionRun.bind definitions_curBlock fun _ => DefinitionRun.bind (definitions_setCur _) fun _ =>
    DefinitionRun.bind h2 fun _ => DefinitionRun.bind definitions_curBlock fun _ => definitions_joinArms _ _

theorem definitions_ifS_none_core (cv : ValueId) {a1 : B ValueId} (h1 : DefinitionRun a1) :
    DefinitionRun (whenLive () fun _ => do
      let (tb, jb) ← fork cv
      setCur (some tb)
      let _ ← a1
      emitTerm (.br jb [])
      setCur (some jb)) := by
  exact definitions_whenLive _ fun _ =>
    DefinitionRun.bind (definitions_fork _) fun ⟨_, _⟩ =>
    DefinitionRun.bind (definitions_setCur _) fun _ => DefinitionRun.bind h1 fun _ =>
    DefinitionRun.bind (definitions_emitTerm _) fun _ => definitions_setCur _

theorem definitions_assert_core (cv : ValueId) (org : OriginId) :
    DefinitionRun (whenLive () fun _ => do
      let (pb, fb) ← fork cv
      setCur (some fb)
      emitTerm (.abort .assert (some org))
      setCur (some pb)) := by
  exact definitions_whenLive _ fun _ =>
    DefinitionRun.bind (definitions_fork _) fun ⟨_, _⟩ =>
    DefinitionRun.bind (definitions_setCur _) fun _ => DefinitionRun.bind (definitions_emitTerm _) fun _ => definitions_setCur _

theorem definitions_header0 {tail : BlockId → B Unit} (ht : ∀ h, DefinitionRun (tail h)) :
    DefinitionRun (do
      let (hb, _) ← newBlock []
      emitTerm (.br hb [])
      setCur (some hb)
      tail hb) := by
  exact DefinitionRun.bind (definitions_newBlock _) fun ⟨_, _⟩ =>
    DefinitionRun.bind (definitions_emitTerm _) fun _ => DefinitionRun.bind (definitions_setCur _) fun _ => ht _

theorem definitions_header1 (ty : VTy) (a : ValueId) {tail : BlockId → ValueId → B Unit}
    (ht : ∀ h i, DefinitionRun (tail h i)) :
    DefinitionRun (do
      let (hb, hs) ← newBlock [ty]
      let i := hs.headD 0
      emitTerm (.br hb [a])
      setCur (some hb)
      tail hb i) := by
  exact DefinitionRun.bind (definitions_newBlock _) fun ⟨_, _⟩ =>
    DefinitionRun.bind (definitions_emitTerm _) fun _ => DefinitionRun.bind (definitions_setCur _) fun _ => ht _ _

mutual

theorem definitions_lowerExpr : ∀ e : Expr, DefinitionRun (lowerExpr e)
  | .structLit t es => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerExprs es) fun _ => definitions_emitDef _
  | .lit t n => by simp only [lowerExpr]; exact definitions_emitDef _
  | .bool b => by simp only [lowerExpr]; exact definitions_emitDef _
  | .read p => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerPlace p) fun _ => definitions_emitDef _
  | .ref m p => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerPlace p) fun r => definitions_freezeTo m r
  | .slice m v lo hi org => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerView v) fun _ => DefinitionRun.bind (definitions_lowerBound lo) fun _ =>
      DefinitionRun.bind (definitions_lowerBound hi) fun _ => definitions_emitDef _
  | .len v => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerView v) fun _ => definitions_emitDef _
  | .un op e org => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerExpr e) fun a => DefinitionRun.bind (definitions_intTyOf a) fun _ => definitions_emitDef _
  | .bin op a b org => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerExpr a) fun x => DefinitionRun.bind (definitions_lowerExpr b) fun y =>
      DefinitionRun.bind (definitions_intTyOf x) fun _ => definitions_emitDef _
  | .cmp op a b => by
    simp only [lowerExpr]
    refine DefinitionRun.bind (definitions_lowerExpr a) fun x => DefinitionRun.bind (definitions_lowerExpr b) fun y =>
      DefinitionRun.bind (definitions_valTy x) fun t => ?_
    cases t with
    | data t => cases t <;> exact definitions_emitDef _
    | view _ _ => exact definitions_emitDef _
  | .and a b => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerExpr a) fun x => definitions_shortCircuit true x (definitions_lowerExpr b)
  | .or a b => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerExpr a) fun x => definitions_shortCircuit false x (definitions_lowerExpr b)
  | .not e => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerExpr e) fun _ => definitions_emitDef _
  | .conv k target e org => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerExpr e) fun a => DefinitionRun.bind (definitions_intTyOf a) fun _ => definitions_emitDef _
  | .call c args org => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerArgs args) fun _ =>
      DefinitionRun.bind (definitions_emitDef _) fun r => DefinitionRun.bind definitions_read fun le => by
        cases le.mod.noReturn c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact DefinitionRun.pure _ | exact DefinitionRun.bind (definitions_emitTerm _) fun _ => DefinitionRun.pure _
  | .push owner e org => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerPlace owner) fun r => DefinitionRun.bind (definitions_lowerExpr e) fun v =>
      definitions_emitDef (.push r v org)
  | .pop owner org => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerPlace owner) fun _ => definitions_emitDef _
  | .ifE c t f => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerExpr c) fun cv =>
      definitions_ifE_core cv (definitions_lowerBlock none [] true t) (definitions_lowerBlock none [] true f)
  | .blockE b => by
    simp only [lowerExpr]
    exact definitions_lowerBlock none [] true b
  | .arrLit t es => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerExprs es) fun _ => definitions_emitDef _
  | .fill t e => by
    simp only [lowerExpr]
    exact DefinitionRun.bind (definitions_lowerExpr e) fun _ => definitions_emitDef _

theorem definitions_lowerExprs : ∀ es : List Expr, DefinitionRun (lowerExprs es)
  | [] => by simp only [lowerExprs]; exact DefinitionRun.pure _
  | e :: rest => by
    simp only [lowerExprs]
    exact DefinitionRun.bind (definitions_lowerExpr e) fun _ => DefinitionRun.bind (definitions_lowerExprs rest) fun _ => DefinitionRun.pure _

theorem definitions_lowerArg : ∀ a : Arg, DefinitionRun (lowerArg a)
  | .byVal e => by simp only [lowerArg]; exact definitions_lowerExpr e
  | .byRef m p => by
    simp only [lowerArg]
    exact DefinitionRun.bind (definitions_lowerPlace p) fun r => definitions_freezeTo m r

theorem definitions_lowerArgs : ∀ as : List Arg, DefinitionRun (lowerArgs as)
  | [] => by simp only [lowerArgs]; exact DefinitionRun.pure _
  | a :: rest => by
    simp only [lowerArgs]
    exact DefinitionRun.bind (definitions_lowerArg a) fun _ => DefinitionRun.bind (definitions_lowerArgs rest) fun _ => DefinitionRun.pure _

theorem definitions_lowerPlace : ∀ p : Place, DefinitionRun (lowerPlace p)
  | .field owner i => by
    simp only [lowerPlace]
    exact DefinitionRun.bind (definitions_lowerPlace owner) fun _ => definitions_emitDef _
  | .var x => by simp only [lowerPlace]; exact definitions_emitDef _
  | .global g => by simp only [lowerPlace]; exact definitions_emitDef _
  | .deref e => by simp only [lowerPlace]; exact definitions_lowerExpr e
  | .elem v i org => by
    simp only [lowerPlace]
    exact DefinitionRun.bind (definitions_lowerView v) fun _ => DefinitionRun.bind (definitions_lowerExpr i) fun _ => definitions_emitDef _

theorem definitions_lowerView : ∀ v : View, DefinitionRun (lowerView v)
  | .of p => by
    simp only [lowerView]
    exact DefinitionRun.bind (definitions_lowerPlace p) fun _ => definitions_emitDef _
  | .val e => by
    simp only [lowerView]
    exact DefinitionRun.bind (definitions_lowerExpr e) fun _ => definitions_emitDef _

theorem definitions_lowerBound : ∀ b : Bound, DefinitionRun (lowerBound b)
  | .omitted => by simp only [lowerBound]; exact DefinitionRun.pure _
  | .expr e => by
    simp only [lowerBound]
    exact DefinitionRun.bind (definitions_lowerExpr e) fun _ => DefinitionRun.pure _
  | .fromEnd e => by
    simp only [lowerBound]
    exact DefinitionRun.bind (definitions_lowerExpr e) fun _ => DefinitionRun.pure _

theorem definitions_lowerEachSource : ∀ v : View, DefinitionRun (lowerEachSource v)
  | .of p => by
    simp only [lowerEachSource]
    exact DefinitionRun.bind (definitions_lowerPlace p) fun _ => DefinitionRun.bind (definitions_emitDef _) fun _ => DefinitionRun.pure _
  | .val e => by
    simp only [lowerEachSource]
    exact DefinitionRun.bind (definitions_lowerExpr e) fun _ => DefinitionRun.bind (definitions_emitDef _) fun _ => DefinitionRun.pure _

theorem definitions_lowerBlockValue (want : Bool) : ∀ v : Option Expr, DefinitionRun (lowerBlockValue want v)
  | some e => by simp only [lowerBlockValue]; exact definitions_lowerExpr e
  | none => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact DefinitionRun.pure _
    · simp only [lowerBlockValue, ↓reduceIte]; exact definitions_emitDef _

theorem definitions_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, DefinitionRun (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    simp only [lowerBlock]
    exact DefinitionRun.bind (definitions_emitEffect _) fun _ => definitions_inScope sc
      (DefinitionRun.bind (definitions_initSlots _) fun _ => DefinitionRun.bind (definitions_lowerStmts lc stmts) fun _ =>
        DefinitionRun.bind (definitions_lowerBlockValue want value) fun _ => DefinitionRun.bind (definitions_emitEffect _) fun _ =>
        DefinitionRun.pure _)

theorem definitions_lowerStmts (lc : Option LoopCtx) : ∀ ss : List Stmt, DefinitionRun (lowerStmts lc ss)
  | [] => by simp only [lowerStmts]; exact DefinitionRun.pure _
  | s :: rest => by
    simp only [lowerStmts]
    refine DefinitionRun.bind definitions_isLive fun live => ?_
    cases live
    · exact DefinitionRun.pure _
    · exact DefinitionRun.bind (definitions_lowerStmt lc s) fun _ => definitions_lowerStmts lc rest

theorem definitions_lowerPrintArgs : ∀ as : List PrintArg, DefinitionRun (lowerPrintArgs as)
  | [] => by simp only [lowerPrintArgs]; exact DefinitionRun.pure _
  | .text s :: rest => by
    simp only [lowerPrintArgs]
    exact DefinitionRun.bind (definitions_lowerPrintArgs rest) fun _ => DefinitionRun.pure _
  | .expr e :: rest => by
    simp only [lowerPrintArgs]
    exact DefinitionRun.bind (definitions_lowerExpr e) fun _ => DefinitionRun.bind (definitions_lowerPrintArgs rest) fun _ => DefinitionRun.pure _

theorem definitions_lowerStmt (lc : Option LoopCtx) : ∀ s : Stmt, DefinitionRun (lowerStmt lc s)
  | .letS x e org => by
    simp only [lowerStmt]
    exact DefinitionRun.bind (definitions_lowerExpr e) fun value =>
      DefinitionRun.bind (definitions_coerceSlot x value org) fun _ => definitions_emitEffect _
  | .assign p e org => by
    simp only [lowerStmt]
    exact DefinitionRun.bind (definitions_lowerPlace p) fun _ => DefinitionRun.bind (definitions_lowerExpr e) fun _ => definitions_emitEffect _
  | .assignOp op p e org => by
    simp only [lowerStmt]
    exact DefinitionRun.bind (definitions_lowerPlace p) fun _ => DefinitionRun.bind (definitions_emitDef _) fun _ =>
      DefinitionRun.bind (definitions_lowerExpr e) fun _ => DefinitionRun.bind (definitions_intTyOf _) fun _ =>
      DefinitionRun.bind (definitions_emitDef _) fun _ => definitions_emitEffect _
  | .rebind x e org => by
    simp only [lowerStmt]
    exact DefinitionRun.bind (definitions_lowerExpr e) fun value =>
      DefinitionRun.bind (definitions_coerceSlot x value org) fun _ =>
        DefinitionRun.bind (definitions_emitDef _) fun _ => definitions_emitEffect _
  | .expr e _ => by
    simp only [lowerStmt]
    exact DefinitionRun.bind (definitions_lowerExpr e) fun _ => DefinitionRun.pure _
  | .append owner src org => by
    simp only [lowerStmt]
    exact DefinitionRun.bind (definitions_lowerPlace owner) fun _ => DefinitionRun.bind (definitions_lowerView src) fun _ =>
      definitions_emitEffect _
  | .popN owner count org => by
    simp only [lowerStmt]
    exact DefinitionRun.bind (definitions_lowerPlace owner) fun r => DefinitionRun.bind (definitions_lowerExpr count) fun n =>
      definitions_emitEffect (.popN r n (some org))
  | .resize owner size none org => by
    simp only [lowerStmt]
    exact DefinitionRun.bind (definitions_lowerPlace owner) fun r => DefinitionRun.bind (definitions_lowerExpr size) fun n =>
      DefinitionRun.bind (DefinitionRun.pure _) fun fill => definitions_emitEffect (.resize r n fill (some org))
  | .resize owner size (some fill) org => by
    simp only [lowerStmt]
    exact DefinitionRun.bind (definitions_lowerPlace owner) fun r => DefinitionRun.bind (definitions_lowerExpr size) fun n =>
      DefinitionRun.bind (definitions_lowerExpr fill) fun v =>
        definitions_emitEffect (.resize r n (some v) (some org))
  | .clear owner org => by
    simp only [lowerStmt]
    exact DefinitionRun.bind (definitions_lowerPlace owner) fun r => definitions_emitEffect (.clear r (some org))
  | .assignWhole owner replacement org => by
    simp only [lowerStmt]
    exact DefinitionRun.bind (definitions_lowerPlace owner) fun r =>
      DefinitionRun.bind (definitions_emitEffect (.clear r (some org))) fun _ =>
      DefinitionRun.bind (definitions_lowerExpr replacement) fun run =>
        definitions_emitEffect (.replace r run (some org))
  | .ifS c t f _ => by
    cases f with
    | none =>
      simp only [lowerStmt]
      exact DefinitionRun.bind (definitions_lowerExpr c) fun cv => definitions_ifS_none_core cv (definitions_lowerBlock lc [] false t)
    | some fb =>
      simp only [lowerStmt]
      exact DefinitionRun.bind (definitions_lowerExpr c) fun cv =>
        definitions_ifS_some_core cv (definitions_lowerBlock lc [] false t) (definitions_lowerBlock lc [] false fb)
  | .while c body _ => by
    simp only [lowerStmt]
    exact definitions_header0 (tail := fun hb => lowerWhile hb (lowerExpr c)
        (fun d xb => lowerBlock (some ⟨d, xb, .jump hb⟩) [] false body))
      (fun hb => definitions_lowerWhile hb (definitions_lowerExpr c) (fun d xb => definitions_lowerBlock _ _ _ body))
  | .forRange x lo hi body org => by
    simp only [lowerStmt]
    refine DefinitionRun.bind (definitions_lowerExpr lo) fun a => DefinitionRun.bind (definitions_lowerExpr hi) fun b =>
      definitions_whenLive _ fun _ => DefinitionRun.bind (definitions_intTyOf a) fun t => ?_
    exact definitions_header1 (.data (.int t)) a (tail := fun hb i => lowerRange t i b hb (fun d xb =>
        lowerBlock (some ⟨d, xb, .next hb t i⟩) [(x, i, org)] false body))
      (fun hb i => definitions_lowerRange t i b hb (fun d xb => definitions_lowerBlock _ _ _ body))
  | .forEach x idx v byRef body org => by
    simp only [lowerStmt]
    refine DefinitionRun.bind (definitions_lowerEachSource v) fun ov => DefinitionRun.bind (definitions_regrowOf _) fun regrow =>
      DefinitionRun.bind (definitions_eachSampled _ _) fun sampled => DefinitionRun.bind (definitions_emitDef _) fun startAt =>
      definitions_whenLive _ fun _ => ?_
    exact definitions_header1 (.data (.int .i64)) startAt (tail := fun hb i =>
        lowerEach regrow ov.1 sampled hb i (fun d xb => do
          let elem ← emitDef (.refElem ov.2 i)
          let ev ← eachElemValue x byRef elem
          let pre := (x, ev, org) :: (match idx with
            | some j => [(j, i, org)]
            | none => [])
          lowerBlock (some ⟨d, xb, .next hb .i64 i⟩) pre false body))
      (fun hb i => definitions_lowerEach regrow ov.1 sampled hb i (fun d xb =>
        DefinitionRun.bind (definitions_emitDef _) fun elem => DefinitionRun.bind (definitions_eachElemValue _ _ _) fun ev =>
          definitions_lowerBlock _ _ _ body))
  | .ret e org => by
    cases e with
    | some e =>
      simp only [lowerStmt]
      exact DefinitionRun.bind (definitions_lowerExpr e) fun value =>
        DefinitionRun.bind (definitions_coerceResult value org) fun _ =>
          DefinitionRun.bind (DefinitionRun.pure _) fun _ =>
            DefinitionRun.bind (definitions_leaveTo 0) fun _ => definitions_emitTerm _
    | none =>
      simp only [lowerStmt]
      exact DefinitionRun.bind (DefinitionRun.pure _) fun _ => DefinitionRun.bind (definitions_leaveTo 0) fun _ => definitions_emitTerm _
  | .brk _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact DefinitionRun.pure _
    | some l =>
      simp only [lowerStmt]
      exact DefinitionRun.bind (definitions_leaveTo _) fun _ => definitions_emitTerm _
  | .cont _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact DefinitionRun.pure _
    | some l =>
      cases hk : l.cont with
      | jump h =>
        simp only [lowerStmt, hk]
        exact DefinitionRun.bind (definitions_leaveTo _) fun _ => definitions_emitTerm _
      | next h t i =>
        simp only [lowerStmt, hk]
        exact DefinitionRun.bind (definitions_leaveTo _) fun _ => DefinitionRun.bind (definitions_emitDef _) fun _ => definitions_emitTerm _
  | .print args org => by
    simp only [lowerStmt]
    exact DefinitionRun.bind (definitions_lowerPrintArgs args) fun _ => definitions_emitEffect _
  | .assertS e org => by
    simp only [lowerStmt]
    exact DefinitionRun.bind (definitions_lowerExpr e) fun cv => definitions_assert_core cv org
  | .abort _ org => by
    simp only [lowerStmt]
    exact definitions_emitTerm _
  | .exit e org => by
    simp only [lowerStmt]
    exact DefinitionRun.bind (definitions_lowerExpr e) fun _ => definitions_emitTerm _

end


theorem definitions_finishFunction (impl : Impl) (value : ValueId) :
    DefinitionRun (finishFunction impl value) := by
  unfold finishFunction
  refine DefinitionRun.bind definitions_read fun le =>
    DefinitionRun.bind definitions_isLive fun live => ?_
  cases live
  · exact DefinitionRun.pure _
  · by_cases sink : (!impl.results.isEmpty && impl.body.value.isNone &&
        impl.body.diverges le.mod.noReturn) = true
    · simp only [sink, ↓reduceIte]
      exact DefinitionRun.bind (definitions_newBlock _) fun ⟨_, _⟩ =>
        DefinitionRun.bind (definitions_emitTerm _) fun _ =>
        DefinitionRun.bind (definitions_setCur _) fun _ => definitions_emitTerm _
    · simp only [sink, ↓reduceIte]
      exact definitions_emitTerm _

theorem definitions_initState : DefinitionsValid initState := by
  simp [DefinitionsValid, LS.defs, initState]

theorem lowerImpl_unique_definitions (module : Core.Module) (impl : Core.Impl) :
    ((lowerImpl module impl).blocks.toList.flatMap GIR.Block.defs).Nodup := by
  let action : B Unit := do
    let (entry, params) ← newBlock (impl.params.toList.map fun param => .data (tyOfVar impl param.var))
    setCur (some entry)
    let pre := (impl.params.toList.zip params).map fun (param, value) =>
      (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
    let value ← lowerBlock none pre false impl.body
    finishFunction impl value
  have preservation : DefinitionRun action :=
    DefinitionRun.bind (definitions_newBlock _) fun ⟨_, _⟩ =>
      DefinitionRun.bind (definitions_setCur _) fun _ =>
      DefinitionRun.bind (definitions_lowerBlock _ _ _ _) fun _ => definitions_finishFunction _ _
  let output := action (lowerEnv module impl.vars impl.results.toList) initState
  have checked := preservation (lowerEnv module impl.vars impl.results.toList)
    initState output.1 output.2 rfl definitions_initState
  change ((finishBlocks output.2.blocks).toList.flatMap GIR.Block.defs).Nodup
  rw [finishBlocks_defs]
  exact checked.1

theorem lowerGlobal_unique_definitions (module : Core.Module) (global : Core.Global) :
    ((lowerGlobal module global).init.blocks.toList.flatMap GIR.Block.defs).Nodup := by
  let action : B Unit := do
    let (entry, _) ← newBlock []
    setCur (some entry)
    let value ← lowerExpr global.init
    emitTerm (.ret [value] (some global.org))
  have preservation : DefinitionRun action :=
    DefinitionRun.bind (definitions_newBlock _) fun ⟨_, _⟩ =>
      DefinitionRun.bind (definitions_setCur _) fun _ =>
      DefinitionRun.bind (definitions_lowerExpr _) fun _ => definitions_emitTerm _
  let output := action (lowerEnv module #[] [global.ty]) initState
  have checked := preservation (lowerEnv module #[] [global.ty])
    initState output.1 output.2 rfl definitions_initState
  change ((finishBlocks output.2.blocks).toList.flatMap GIR.Block.defs).Nodup
  rw [finishBlocks_defs]
  exact checked.1

theorem lower_unique_definitions (module : Core.Module) (func : Func)
    (member : func ∈ (lower module).funcs.toList ++ (lower module).globals.toList.map (·.init)) :
    (func.blocks.toList.flatMap GIR.Block.defs).Nodup := by
  rcases List.mem_append.mp member with implementation | initializer
  · change func ∈ (module.contexts.map fun ctx =>
        match (module.impls.map fun impl => (impl, lowerImpl module impl))[ctx.impl]? with
        | some (impl, body) => { body with roots := lowerContextRootInfo ctx impl }
        | none => invalidContextFunction ctx).toList at implementation
    simp only [Array.toList_map, List.mem_map] at implementation
    obtain ⟨ctx, _, equality⟩ := implementation
    rw [Array.getElem?_map] at equality
    cases source : module.impls[ctx.impl]? with
    | none =>
      simp only [source, Option.map_none] at equality
      subst func
      simp [invalidContextFunction]
    | some impl =>
      simp only [source, Option.map_some] at equality
      subst func
      exact lowerImpl_unique_definitions module impl
  · obtain ⟨global, globalMember, rfl⟩ := List.mem_map.mp initializer
    change global ∈ (module.globals.map (lowerGlobal module)).toList at globalMember
    simp only [Array.toList_map, List.mem_map] at globalMember
    obtain ⟨source, _, rfl⟩ := globalMember
    exact lowerGlobal_unique_definitions _ _

private theorem emitTerm_block_count (term : Term) (le : LEnv) (state : LS) :
    (emitTerm term le state).2.blocks.size = state.blocks.size := by
  cases current : state.cur with
  | none => rw [emitTerm_none term le current]
  | some block => rw [emitTerm_run term le current]; simp

theorem finishFunction_block_count (impl : Core.Impl) (value : ValueId) (le : LEnv) (before : LS) :
    before.blocks.size ≤ (finishFunction impl value le before).2.blocks.size := by
  change before.blocks.size ≤ ((do
    if before.cur.isSome then
      if !impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn then
        let (sink, _) ← newBlock []
        emitTerm (.br sink [])
        setCur (some sink)
        emitTerm (.br sink [])
      else emitTerm (.ret (if impl.body.value.isSome then [value] else []) none)) le before).2.blocks.size
  cases live : before.cur.isSome <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact Nat.le_refl _
  · split
    · simp only [bind_run, newBlock0_run, setCur_run, emitTerm_block_count, Array.size_push]
      omega
    · simp only [emitTerm_block_count]
      omega

theorem lowerImpl_blocks_nonempty (module : Core.Module) (impl : Core.Impl) :
    0 < (lowerImpl module impl).blocks.size := by
  let env := lowerEnv module impl.vars impl.results.toList
  let start := newBlock (impl.params.toList.map fun param => .data (tyOfVar impl param.var)) env initState
  let entered := (setCur (some start.1.1) env start.2).2
  let pre := (impl.params.toList.zip start.1.2).map fun (param, value) =>
    (param.var, value, (impl.vars[param.var]?.map (fun (localVar : LocalVar) => localVar.org)).getD 0)
  let body := lowerBlock none pre false impl.body env entered
  have advance := advB_lowerBlock none pre false impl.body env entered body.1 body.2 rfl
  have positive : 0 < entered.blocks.size := by
    simp [entered, start, newBlock_run_general, setCur_run, initState]
  have bodyPositive := Nat.lt_of_lt_of_le positive advance.ext.1
  have finalPositive := Nat.lt_of_lt_of_le bodyPositive
    (finishFunction_block_count impl body.1 env body.2)
  change 0 < (finishBlocks (finishFunction impl body.1 env body.2).2.blocks).size
  simpa only [finishBlocks, Array.size_map] using finalPositive

theorem lowerGlobal_blocks_nonempty (module : Core.Module) (global : Core.Global) :
    0 < (lowerGlobal module global).init.blocks.size := by
  let env := lowerEnv module #[] [global.ty]
  let start := newBlock [] env initState
  let entered := (setCur (some start.1.1) env start.2).2
  let body := lowerExpr global.init env entered
  have advance := advB_lowerExpr global.init env entered body.1 body.2 rfl
  have positive : 0 < entered.blocks.size := by
    simp [entered, start, newBlock_run_general, setCur_run, initState]
  have bodyPositive := Nat.lt_of_lt_of_le positive advance.ext.1
  change 0 < (finishBlocks (emitTerm (.ret [body.1] (some global.org)) env body.2).2.blocks).size
  simpa only [finishBlocks, Array.size_map, emitTerm_block_count] using bodyPositive

end Goose.Lower.Validation
