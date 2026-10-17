import Goose.Lower.Validation.Typing

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def Op.CheckedIndex : Op → Prop
  | .indexProven .. => False
  | _ => True

def Inst.CheckedIndex : Inst → Prop
  | .def _ op => Op.CheckedIndex op
  | _ => True

def CheckedIndices (state : LS) : Prop :=
  ∀ inst ∈ state.insts, Inst.CheckedIndex inst

def CheckedRun (action : B α) : Prop :=
  ∀ le before result after, action le before = (result, after) →
    CheckedIndices before → CheckedIndices after

theorem CheckedRun.pure (value : α) : CheckedRun (pure value) := by
  intro le before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact checked

theorem CheckedRun.bind {action : B α} {next : α → B β}
    (first : CheckedRun action) (second : ∀ value, CheckedRun (next value)) :
    CheckedRun (action >>= next) := by
  intro le before result after run checked
  obtain ⟨value, mid, firstRun, secondRun⟩ := bind_eq.mp run
  exact second value _ _ _ _ secondRun (first _ _ _ _ firstRun checked)

theorem CheckedRun.of_unchanged {action : B α}
    (unchanged : ∀ le state, (action le state).2.insts = state.insts) : CheckedRun action := by
  intro le before result after run checked
  have equality := unchanged le before
  rw [run] at equality
  simpa only [CheckedIndices, equality] using checked

theorem checked_appendInst {before : LS} (checked : CheckedIndices before)
    (block : BlockId) (inst : Inst) (instruction : Inst.CheckedIndex inst) :
    CheckedIndices (before.appendInst block inst) := by
  intro next member
  change next ∈ (before.blocks.modify block fun blk =>
    { blk with insts := blk.insts.push inst }).toList.flatMap (fun blk => blk.insts.toList) at member
  obtain ⟨blk, blockMember, instructionMember⟩ := List.mem_flatMap.mp member
  obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp blockMember)
  rw [Array.getElem?_modify] at lookup
  by_cases same : block = index
  · simp only [same, ↓reduceIte] at lookup
    cases previous : before.blocks[index]? with
    | none => simp [previous] at lookup
    | some old =>
      simp only [previous, Option.map_some, Option.some.injEq] at lookup
      subst blk
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at instructionMember
      rcases instructionMember with oldInstruction | fresh
      · apply checked next
        simp only [LS.insts, List.mem_flatMap]
        exact ⟨old, Array.mem_toList_iff.mpr (Array.mem_of_getElem? previous), oldInstruction⟩
      · subst next
        exact instruction
  · simp only [same, ↓reduceIte] at lookup
    apply checked next
    simp only [LS.insts, List.mem_flatMap]
    exact ⟨blk, Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), instructionMember⟩

theorem checked_emitDef (op : Op) (instruction : Op.CheckedIndex op := by trivial) :
    CheckedRun (emitDef op) := by
  intro le before result after run checked
  cases current : before.cur with
  | none =>
    rw [emitDef_none op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitDef_run op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    have appended := checked_appendInst checked block (.def before.vals.size op) instruction
    simpa only [CheckedIndices, LS.insts, LS.appendInst] using appended

theorem checked_newBlock (types : List VTy) : CheckedRun (newBlock types) := by
  apply CheckedRun.of_unchanged
  intro le state
  rw [newBlock_run_general]
  simp [LS.insts]

theorem checked_emitEffect (effect : Effect) : CheckedRun (emitEffect effect) := by
  intro le before result after run checked
  cases current : before.cur with
  | none =>
    rw [emitEffect_none effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitEffect_run effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked_appendInst checked block (.eff effect) True.intro

theorem checked_setCur (block : Option BlockId) : CheckedRun (setCur block) := by
  apply CheckedRun.of_unchanged
  intro le state
  rw [setCur_run]
  rfl

theorem checked_patchTerm (block : BlockId) (term : Term) : CheckedRun (patchTerm block term) := by
  intro le before result after run checked
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact checked_appendInst checked block (.term term) True.intro

theorem checked_emitTerm (term : Term) : CheckedRun (emitTerm term) := by
  intro le before result after run checked
  cases current : before.cur with
  | none =>
    rw [emitTerm_none term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitTerm_run term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    have appended := checked_appendInst checked block (.term term) True.intro
    simpa only [CheckedIndices, LS.insts, LS.appendInst] using appended

theorem checked_curBlock : CheckedRun curBlock := by
  apply CheckedRun.of_unchanged
  intro le state
  rw [curBlock_run]

theorem checked_get : CheckedRun (get : B LS) := by
  apply CheckedRun.of_unchanged
  intros
  rfl

theorem checked_read : CheckedRun (read : B LEnv) := by
  apply CheckedRun.of_unchanged
  intros
  rfl

theorem checked_valTy (value : ValueId) : CheckedRun (valTy value) := by
  apply CheckedRun.of_unchanged
  intro le state
  rw [valTy_run]

theorem checked_pushScope (scope : ScopeId) : CheckedRun (pushScope scope) := by
  apply CheckedRun.of_unchanged
  intro le state
  rw [pushScope_run]
  rfl

theorem checked_popScope : CheckedRun popScope := by
  apply CheckedRun.of_unchanged
  intro le state
  rw [popScope_run]
  rfl

theorem checked_inScope (scope : ScopeId) {action : B α} (typed : CheckedRun action) :
    CheckedRun (inScope scope action) := by
  unfold inScope
  exact CheckedRun.bind (checked_pushScope _) fun _ =>
    CheckedRun.bind typed fun _ => CheckedRun.bind checked_popScope fun _ => CheckedRun.pure _

theorem checked_whenLive (default : α) {action : BlockId → B α}
    (typed : ∀ block, CheckedRun (action block)) : CheckedRun (whenLive default action) := by
  unfold whenLive
  refine CheckedRun.bind checked_curBlock fun current => ?_
  cases current
  · exact CheckedRun.pure _
  · exact typed _

theorem checked_intTyOf (v : ValueId) : CheckedRun (intTyOf v) := by
  unfold intTyOf
  refine CheckedRun.bind (checked_valTy v) fun t => ?_
  cases t with
  | data t => cases t <;> exact CheckedRun.pure _
  | view _ _ => exact CheckedRun.pure _

theorem checked_freezeTo (m : Mutability) (r : ValueId) : CheckedRun (freezeTo m r) := by
  unfold freezeTo
  refine CheckedRun.bind (checked_valTy r) fun t => ?_
  cases m <;> cases t <;> first
    | exact CheckedRun.pure _
    | (rename_i t; cases t <;> first | exact CheckedRun.pure _ | (rename_i m' _; cases m' <;> first | exact CheckedRun.pure _ | exact checked_emitDef _))

theorem checked_coerceTo (target : Ty) (r : ValueId) (org : OriginId) : CheckedRun (coerceTo target r org) := by
  unfold coerceTo
  refine CheckedRun.bind (checked_valTy r) fun source => ?_
  split
  · exact checked_emitDef _
  · exact CheckedRun.bind (checked_emitDef _) (fun _ => checked_emitDef _)
  · exact CheckedRun.pure _

theorem checked_coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) :
    CheckedRun (coerceSlot slot value org) := by
  unfold coerceSlot
  refine CheckedRun.bind checked_read fun le => ?_
  cases le.slots[slot]? with
  | none => exact CheckedRun.pure _
  | some destination => exact checked_coerceTo destination.ty value org

theorem checked_coerceResult (value : ValueId) (org : OriginId) :
    CheckedRun (coerceResult value org) := by
  unfold coerceResult
  refine CheckedRun.bind checked_read fun le => ?_
  cases le.results.head? with
  | none => exact CheckedRun.pure _
  | some destination => exact checked_coerceTo destination value org

theorem checked_growOwner (r : ValueId) : CheckedRun (growOwner r) := by
  unfold growOwner
  refine CheckedRun.bind (checked_valTy r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact CheckedRun.pure _ | (rename_i m' t'; cases t' <;> exact CheckedRun.pure _)
  | view _ _ => exact CheckedRun.pure _

theorem checked_leaveAll : ∀ scs, CheckedRun (leaveAll scs)
  | [] => CheckedRun.pure _
  | sc :: rest => by
    unfold leaveAll
    exact CheckedRun.bind (checked_emitEffect _) fun _ => checked_leaveAll rest

theorem checked_leaveTo (d : Nat) : CheckedRun (leaveTo d) := by
  unfold leaveTo
  exact CheckedRun.bind checked_get fun _ => checked_leaveAll _

theorem checked_initSlots : ∀ ps, CheckedRun (initSlots ps)
  | [] => CheckedRun.pure _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact CheckedRun.bind (checked_emitEffect _) fun _ => checked_initSlots rest

theorem checked_isLive : CheckedRun isLive := by
  unfold isLive
  exact CheckedRun.bind checked_curBlock fun _ => CheckedRun.pure _

theorem checked_eachElemValue (x : VarId) (byRef : Bool) (elem : ValueId) :
    CheckedRun (eachElemValue x byRef elem) := by
  unfold eachElemValue
  cases byRef
  · exact checked_emitDef _
  · refine CheckedRun.bind checked_read fun le => ?_
    cases le.vars[x]? with
    | none => exact CheckedRun.pure _
    | some lv =>
      dsimp only
      cases lv.ty with
      | ref m t => exact checked_freezeTo m elem
      | _ => exact CheckedRun.pure _

theorem checked_regrowOf (o : Option ValueId) : CheckedRun (regrowOf o) := by
  cases o with
  | none => exact CheckedRun.pure _
  | some r => exact checked_growOwner r

theorem checked_eachSampled (regrow : Bool) (vw : ValueId) : CheckedRun (eachSampled regrow vw) := by
  unfold eachSampled
  cases regrow
  · exact checked_emitDef _
  · exact CheckedRun.pure _

theorem checked_eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    CheckedRun (eachLen regrow owner sampled) := by
  unfold eachLen
  cases regrow
  · exact CheckedRun.pure _
  · exact checked_emitDef _

theorem checked_fork (condition : ValueId) : CheckedRun (fork condition) := by
  unfold fork
  exact CheckedRun.bind (checked_newBlock _) fun ⟨thenBlock, _⟩ =>
    CheckedRun.bind (checked_newBlock _) fun ⟨elseBlock, _⟩ =>
    CheckedRun.bind (checked_emitTerm _) fun _ => CheckedRun.pure _

theorem checked_patchBrs (target : BlockId) : ∀ incoming, CheckedRun (patchBrs target incoming)
  | [] => CheckedRun.pure _
  | (block, value) :: rest => by
    unfold patchBrs
    exact CheckedRun.bind (checked_patchTerm _ _) fun _ => checked_patchBrs target rest

theorem checked_patchBrs0 (target : BlockId) : ∀ incoming, CheckedRun (patchBrs0 target incoming)
  | [] => CheckedRun.pure _
  | block :: rest => by
    unfold patchBrs0
    exact CheckedRun.bind (checked_patchTerm _ _) fun _ => checked_patchBrs0 target rest

theorem checked_joinValue (endT : Option BlockId) (vt : ValueId) (endF : Option BlockId) (vf : ValueId) :
    CheckedRun (joinValue endT vt endF vf) := by
  unfold joinValue
  cases endT <;> cases endF
  · exact CheckedRun.bind (checked_setCur _) fun _ => CheckedRun.pure _
  all_goals
    exact CheckedRun.bind (checked_valTy _) fun _ =>
      CheckedRun.bind (checked_newBlock _) fun ⟨_, _⟩ =>
      CheckedRun.bind (checked_patchBrs _ _) fun _ =>
      CheckedRun.bind (checked_setCur _) fun _ => CheckedRun.pure _

theorem checked_joinArms (endT endF : Option BlockId) : CheckedRun (joinArms endT endF) := by
  unfold joinArms
  cases endT <;> cases endF
  · exact checked_setCur _
  all_goals
    exact CheckedRun.bind (checked_newBlock _) fun ⟨_, _⟩ =>
      CheckedRun.bind (checked_patchBrs0 _ _) fun _ => checked_setCur _

theorem checked_scFork (isAnd : Bool) (value : ValueId) : CheckedRun (scFork isAnd value) := by
  unfold scFork
  refine CheckedRun.bind (checked_newBlock _) fun ⟨_, _⟩ =>
    CheckedRun.bind (checked_newBlock _) fun ⟨_, _⟩ => ?_
  cases isAnd <;> exact CheckedRun.bind (checked_emitTerm _) fun _ => CheckedRun.pure _

theorem checked_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (typed : CheckedRun rhs) : CheckedRun (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  exact checked_whenLive _ fun _ =>
    CheckedRun.bind (checked_scFork _ _) fun ⟨_, _, _⟩ =>
    CheckedRun.bind (checked_setCur _) fun _ => CheckedRun.bind typed fun _ =>
    CheckedRun.bind (checked_emitTerm _) fun _ =>
    CheckedRun.bind (checked_setCur _) fun _ => CheckedRun.pure _

theorem checked_loopBody (cv : ValueId) {body : Nat → BlockId → B ValueId} {back : B Unit}
    (hbody : ∀ depth exitBlock, CheckedRun (body depth exitBlock)) (hback : CheckedRun back) :
    CheckedRun (loopBody cv body back) := by
  unfold loopBody
  exact CheckedRun.bind checked_get fun _ =>
    CheckedRun.bind (checked_fork _) fun ⟨_, _⟩ =>
    CheckedRun.bind (checked_setCur _) fun _ => CheckedRun.bind (hbody _ _) fun _ =>
    CheckedRun.bind hback fun _ => checked_setCur _

theorem checked_rangeBack (t : IntTy) (i : ValueId) (hb : BlockId) : CheckedRun (rangeBack t i hb) := by
  unfold rangeBack
  refine CheckedRun.bind checked_isLive fun live => ?_
  cases live
  · exact CheckedRun.pure _
  · exact CheckedRun.bind (checked_emitDef _) fun _ => checked_emitTerm _


theorem checked_lowerWhile (hb : BlockId) {cond : B ValueId} {body : Nat → BlockId → B ValueId}
    (hc : CheckedRun cond) (hbody : ∀ d xb, CheckedRun (body d xb)) : CheckedRun (lowerWhile hb cond body) := by
  unfold lowerWhile
  exact CheckedRun.bind hc fun cv => checked_whenLive _ fun _ =>
    checked_loopBody cv hbody (checked_emitTerm _)

theorem checked_lowerRange (t : IntTy) (i b : ValueId) (hb : BlockId) {body : Nat → BlockId → B ValueId}
    (hbody : ∀ d xb, CheckedRun (body d xb)) : CheckedRun (lowerRange t i b hb body) := by
  unfold lowerRange
  exact CheckedRun.bind (checked_emitDef _) fun c => checked_loopBody c hbody (checked_rangeBack _ _ _)

theorem checked_lowerEach (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (hb : BlockId)
    (i : ValueId) {body : Nat → BlockId → B ValueId} (hbody : ∀ d xb, CheckedRun (body d xb)) :
    CheckedRun (lowerEach regrow owner sampled hb i body) := by
  unfold lowerEach
  exact CheckedRun.bind (checked_eachLen _ _ _) fun n => CheckedRun.bind (checked_emitDef _) fun c =>
    checked_loopBody c hbody (checked_rangeBack _ _ _)

theorem checked_ifE_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : CheckedRun a1) (h2 : CheckedRun a2) :
    CheckedRun (whenLive 0 fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let vt ← a1
      let endT ← curBlock
      setCur (some eb)
      let vf ← a2
      let endF ← curBlock
      joinValue endT vt endF vf) := by
  exact checked_whenLive _ fun _ =>
    CheckedRun.bind (checked_fork _) fun ⟨_, _⟩ =>
    CheckedRun.bind (checked_setCur _) fun _ => CheckedRun.bind h1 fun _ =>
    CheckedRun.bind checked_curBlock fun _ => CheckedRun.bind (checked_setCur _) fun _ =>
    CheckedRun.bind h2 fun _ => CheckedRun.bind checked_curBlock fun _ => checked_joinValue _ _ _ _

theorem checked_ifS_some_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : CheckedRun a1) (h2 : CheckedRun a2) :
    CheckedRun (whenLive () fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let _ ← a1
      let endT ← curBlock
      setCur (some eb)
      let _ ← a2
      let endF ← curBlock
      joinArms endT endF) := by
  exact checked_whenLive _ fun _ =>
    CheckedRun.bind (checked_fork _) fun ⟨_, _⟩ =>
    CheckedRun.bind (checked_setCur _) fun _ => CheckedRun.bind h1 fun _ =>
    CheckedRun.bind checked_curBlock fun _ => CheckedRun.bind (checked_setCur _) fun _ =>
    CheckedRun.bind h2 fun _ => CheckedRun.bind checked_curBlock fun _ => checked_joinArms _ _

theorem checked_ifS_none_core (cv : ValueId) {a1 : B ValueId} (h1 : CheckedRun a1) :
    CheckedRun (whenLive () fun _ => do
      let (tb, jb) ← fork cv
      setCur (some tb)
      let _ ← a1
      emitTerm (.br jb [])
      setCur (some jb)) := by
  exact checked_whenLive _ fun _ =>
    CheckedRun.bind (checked_fork _) fun ⟨_, _⟩ =>
    CheckedRun.bind (checked_setCur _) fun _ => CheckedRun.bind h1 fun _ =>
    CheckedRun.bind (checked_emitTerm _) fun _ => checked_setCur _

theorem checked_assert_core (cv : ValueId) (org : OriginId) :
    CheckedRun (whenLive () fun _ => do
      let (pb, fb) ← fork cv
      setCur (some fb)
      emitTerm (.abort .assert (some org))
      setCur (some pb)) := by
  exact checked_whenLive _ fun _ =>
    CheckedRun.bind (checked_fork _) fun ⟨_, _⟩ =>
    CheckedRun.bind (checked_setCur _) fun _ => CheckedRun.bind (checked_emitTerm _) fun _ => checked_setCur _

theorem checked_header0 {tail : BlockId → B Unit} (ht : ∀ h, CheckedRun (tail h)) :
    CheckedRun (do
      let (hb, _) ← newBlock []
      emitTerm (.br hb [])
      setCur (some hb)
      tail hb) := by
  exact CheckedRun.bind (checked_newBlock _) fun ⟨_, _⟩ =>
    CheckedRun.bind (checked_emitTerm _) fun _ => CheckedRun.bind (checked_setCur _) fun _ => ht _

theorem checked_header1 (ty : VTy) (a : ValueId) {tail : BlockId → ValueId → B Unit}
    (ht : ∀ h i, CheckedRun (tail h i)) :
    CheckedRun (do
      let (hb, hs) ← newBlock [ty]
      let i := hs.headD 0
      emitTerm (.br hb [a])
      setCur (some hb)
      tail hb i) := by
  exact CheckedRun.bind (checked_newBlock _) fun ⟨_, _⟩ =>
    CheckedRun.bind (checked_emitTerm _) fun _ => CheckedRun.bind (checked_setCur _) fun _ => ht _ _

mutual

theorem checked_lowerExpr : ∀ e : Expr, CheckedRun (lowerExpr e)
  | .structLit t es => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerExprs es) fun _ => checked_emitDef _
  | .lit t n => by simp only [lowerExpr]; exact checked_emitDef _
  | .bool b => by simp only [lowerExpr]; exact checked_emitDef _
  | .read p => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerPlace p) fun _ => checked_emitDef _
  | .ref m p => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerPlace p) fun r => checked_freezeTo m r
  | .slice m v lo hi org => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerView v) fun _ => CheckedRun.bind (checked_lowerBound lo) fun _ =>
      CheckedRun.bind (checked_lowerBound hi) fun _ => checked_emitDef _
  | .len v => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerView v) fun _ => checked_emitDef _
  | .un op e org => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerExpr e) fun a => CheckedRun.bind (checked_intTyOf a) fun _ => checked_emitDef _
  | .bin op a b org => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerExpr a) fun x => CheckedRun.bind (checked_lowerExpr b) fun y =>
      CheckedRun.bind (checked_intTyOf x) fun _ => checked_emitDef _
  | .cmp op a b => by
    simp only [lowerExpr]
    refine CheckedRun.bind (checked_lowerExpr a) fun x => CheckedRun.bind (checked_lowerExpr b) fun y =>
      CheckedRun.bind (checked_valTy x) fun t => ?_
    cases t with
    | data t => cases t <;> exact checked_emitDef _
    | view _ _ => exact checked_emitDef _
  | .and a b => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerExpr a) fun x => checked_shortCircuit true x (checked_lowerExpr b)
  | .or a b => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerExpr a) fun x => checked_shortCircuit false x (checked_lowerExpr b)
  | .not e => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerExpr e) fun _ => checked_emitDef _
  | .conv k target e org => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerExpr e) fun a => CheckedRun.bind (checked_intTyOf a) fun _ => checked_emitDef _
  | .call c args org => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerArgs args) fun _ =>
      CheckedRun.bind (checked_emitDef _) fun r => CheckedRun.bind checked_read fun le => by
        cases le.mod.noReturn c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact CheckedRun.pure _ | exact CheckedRun.bind (checked_emitTerm _) fun _ => CheckedRun.pure _
  | .push owner e org => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerPlace owner) fun r => CheckedRun.bind (checked_lowerExpr e) fun v =>
      checked_emitDef (.push r v org)
  | .pop owner org => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerPlace owner) fun _ => checked_emitDef _
  | .ifE c t f => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerExpr c) fun cv =>
      checked_ifE_core cv (checked_lowerBlock none [] true t) (checked_lowerBlock none [] true f)
  | .blockE b => by
    simp only [lowerExpr]
    exact checked_lowerBlock none [] true b
  | .arrLit t es => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerExprs es) fun _ => checked_emitDef _
  | .fill t e => by
    simp only [lowerExpr]
    exact CheckedRun.bind (checked_lowerExpr e) fun _ => checked_emitDef _

theorem checked_lowerExprs : ∀ es : List Expr, CheckedRun (lowerExprs es)
  | [] => by simp only [lowerExprs]; exact CheckedRun.pure _
  | e :: rest => by
    simp only [lowerExprs]
    exact CheckedRun.bind (checked_lowerExpr e) fun _ => CheckedRun.bind (checked_lowerExprs rest) fun _ => CheckedRun.pure _

theorem checked_lowerArg : ∀ a : Arg, CheckedRun (lowerArg a)
  | .byVal e => by simp only [lowerArg]; exact checked_lowerExpr e
  | .byRef m p => by
    simp only [lowerArg]
    exact CheckedRun.bind (checked_lowerPlace p) fun r => checked_freezeTo m r

theorem checked_lowerArgs : ∀ as : List Arg, CheckedRun (lowerArgs as)
  | [] => by simp only [lowerArgs]; exact CheckedRun.pure _
  | a :: rest => by
    simp only [lowerArgs]
    exact CheckedRun.bind (checked_lowerArg a) fun _ => CheckedRun.bind (checked_lowerArgs rest) fun _ => CheckedRun.pure _

theorem checked_lowerPlace : ∀ p : Place, CheckedRun (lowerPlace p)
  | .field owner i => by
    simp only [lowerPlace]
    exact CheckedRun.bind (checked_lowerPlace owner) fun _ => checked_emitDef _
  | .var x => by simp only [lowerPlace]; exact checked_emitDef _
  | .global g => by simp only [lowerPlace]; exact checked_emitDef _
  | .deref e => by simp only [lowerPlace]; exact checked_lowerExpr e
  | .elem v i org => by
    simp only [lowerPlace]
    exact CheckedRun.bind (checked_lowerView v) fun _ => CheckedRun.bind (checked_lowerExpr i) fun _ => checked_emitDef _

theorem checked_lowerView : ∀ v : View, CheckedRun (lowerView v)
  | .of p => by
    simp only [lowerView]
    exact CheckedRun.bind (checked_lowerPlace p) fun _ => checked_emitDef _
  | .val e => by
    simp only [lowerView]
    exact CheckedRun.bind (checked_lowerExpr e) fun _ => checked_emitDef _

theorem checked_lowerBound : ∀ b : Bound, CheckedRun (lowerBound b)
  | .omitted => by simp only [lowerBound]; exact CheckedRun.pure _
  | .expr e => by
    simp only [lowerBound]
    exact CheckedRun.bind (checked_lowerExpr e) fun _ => CheckedRun.pure _
  | .fromEnd e => by
    simp only [lowerBound]
    exact CheckedRun.bind (checked_lowerExpr e) fun _ => CheckedRun.pure _

theorem checked_lowerEachSource : ∀ v : View, CheckedRun (lowerEachSource v)
  | .of p => by
    simp only [lowerEachSource]
    exact CheckedRun.bind (checked_lowerPlace p) fun _ => CheckedRun.bind (checked_emitDef _) fun _ => CheckedRun.pure _
  | .val e => by
    simp only [lowerEachSource]
    exact CheckedRun.bind (checked_lowerExpr e) fun _ => CheckedRun.bind (checked_emitDef _) fun _ => CheckedRun.pure _

theorem checked_lowerBlockValue (want : Bool) : ∀ v : Option Expr, CheckedRun (lowerBlockValue want v)
  | some e => by simp only [lowerBlockValue]; exact checked_lowerExpr e
  | none => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact CheckedRun.pure _
    · simp only [lowerBlockValue, ↓reduceIte]; exact checked_emitDef _

theorem checked_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, CheckedRun (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    simp only [lowerBlock]
    exact CheckedRun.bind (checked_emitEffect _) fun _ => checked_inScope sc
      (CheckedRun.bind (checked_initSlots _) fun _ => CheckedRun.bind (checked_lowerStmts lc stmts) fun _ =>
        CheckedRun.bind (checked_lowerBlockValue want value) fun _ => CheckedRun.bind (checked_emitEffect _) fun _ =>
        CheckedRun.pure _)

theorem checked_lowerStmts (lc : Option LoopCtx) : ∀ ss : List Stmt, CheckedRun (lowerStmts lc ss)
  | [] => by simp only [lowerStmts]; exact CheckedRun.pure _
  | s :: rest => by
    simp only [lowerStmts]
    refine CheckedRun.bind checked_isLive fun live => ?_
    cases live
    · exact CheckedRun.pure _
    · exact CheckedRun.bind (checked_lowerStmt lc s) fun _ => checked_lowerStmts lc rest

theorem checked_lowerPrintArgs : ∀ as : List PrintArg, CheckedRun (lowerPrintArgs as)
  | [] => by simp only [lowerPrintArgs]; exact CheckedRun.pure _
  | .text s :: rest => by
    simp only [lowerPrintArgs]
    exact CheckedRun.bind (checked_lowerPrintArgs rest) fun _ => CheckedRun.pure _
  | .expr e :: rest => by
    simp only [lowerPrintArgs]
    exact CheckedRun.bind (checked_lowerExpr e) fun _ => CheckedRun.bind (checked_lowerPrintArgs rest) fun _ => CheckedRun.pure _

theorem checked_lowerStmt (lc : Option LoopCtx) : ∀ s : Stmt, CheckedRun (lowerStmt lc s)
  | .letS x e org => by
    simp only [lowerStmt]
    exact CheckedRun.bind (checked_lowerExpr e) fun value =>
      CheckedRun.bind (checked_coerceSlot x value org) fun _ => checked_emitEffect _
  | .assign p e org => by
    simp only [lowerStmt]
    exact CheckedRun.bind (checked_lowerPlace p) fun _ => CheckedRun.bind (checked_lowerExpr e) fun _ => checked_emitEffect _
  | .assignOp op p e org => by
    simp only [lowerStmt]
    exact CheckedRun.bind (checked_lowerPlace p) fun _ => CheckedRun.bind (checked_emitDef _) fun _ =>
      CheckedRun.bind (checked_lowerExpr e) fun _ => CheckedRun.bind (checked_intTyOf _) fun _ =>
      CheckedRun.bind (checked_emitDef _) fun _ => checked_emitEffect _
  | .rebind x e org => by
    simp only [lowerStmt]
    exact CheckedRun.bind (checked_lowerExpr e) fun value =>
      CheckedRun.bind (checked_coerceSlot x value org) fun _ =>
        CheckedRun.bind (checked_emitDef _) fun _ => checked_emitEffect _
  | .expr e _ => by
    simp only [lowerStmt]
    exact CheckedRun.bind (checked_lowerExpr e) fun _ => CheckedRun.pure _
  | .append owner src org => by
    simp only [lowerStmt]
    exact CheckedRun.bind (checked_lowerPlace owner) fun _ => CheckedRun.bind (checked_lowerView src) fun _ =>
      checked_emitEffect _
  | .popN owner count org => by
    simp only [lowerStmt]
    exact CheckedRun.bind (checked_lowerPlace owner) fun r => CheckedRun.bind (checked_lowerExpr count) fun n =>
      checked_emitEffect (.popN r n (some org))
  | .resize owner size none org => by
    simp only [lowerStmt]
    exact CheckedRun.bind (checked_lowerPlace owner) fun r => CheckedRun.bind (checked_lowerExpr size) fun n =>
      CheckedRun.bind (CheckedRun.pure _) fun fill => checked_emitEffect (.resize r n fill (some org))
  | .resize owner size (some fill) org => by
    simp only [lowerStmt]
    exact CheckedRun.bind (checked_lowerPlace owner) fun r => CheckedRun.bind (checked_lowerExpr size) fun n =>
      CheckedRun.bind (checked_lowerExpr fill) fun v =>
        checked_emitEffect (.resize r n (some v) (some org))
  | .clear owner org => by
    simp only [lowerStmt]
    exact CheckedRun.bind (checked_lowerPlace owner) fun r => checked_emitEffect (.clear r (some org))
  | .assignWhole owner replacement org => by
    simp only [lowerStmt]
    exact CheckedRun.bind (checked_lowerPlace owner) fun r =>
      CheckedRun.bind (checked_emitEffect (.clear r (some org))) fun _ =>
      CheckedRun.bind (checked_lowerExpr replacement) fun run =>
        checked_emitEffect (.replace r run (some org))
  | .ifS c t f _ => by
    cases f with
    | none =>
      simp only [lowerStmt]
      exact CheckedRun.bind (checked_lowerExpr c) fun cv => checked_ifS_none_core cv (checked_lowerBlock lc [] false t)
    | some fb =>
      simp only [lowerStmt]
      exact CheckedRun.bind (checked_lowerExpr c) fun cv =>
        checked_ifS_some_core cv (checked_lowerBlock lc [] false t) (checked_lowerBlock lc [] false fb)
  | .while c body _ => by
    simp only [lowerStmt]
    exact checked_header0 (tail := fun hb => lowerWhile hb (lowerExpr c)
        (fun d xb => lowerBlock (some ⟨d, xb, .jump hb⟩) [] false body))
      (fun hb => checked_lowerWhile hb (checked_lowerExpr c) (fun d xb => checked_lowerBlock _ _ _ body))
  | .forRange x lo hi body org => by
    simp only [lowerStmt]
    refine CheckedRun.bind (checked_lowerExpr lo) fun a => CheckedRun.bind (checked_lowerExpr hi) fun b =>
      checked_whenLive _ fun _ => CheckedRun.bind (checked_intTyOf a) fun t => ?_
    exact checked_header1 (.data (.int t)) a (tail := fun hb i => lowerRange t i b hb (fun d xb =>
        lowerBlock (some ⟨d, xb, .next hb t i⟩) [(x, i, org)] false body))
      (fun hb i => checked_lowerRange t i b hb (fun d xb => checked_lowerBlock _ _ _ body))
  | .forEach x idx v byRef body org => by
    simp only [lowerStmt]
    refine CheckedRun.bind (checked_lowerEachSource v) fun ov => CheckedRun.bind (checked_regrowOf _) fun regrow =>
      CheckedRun.bind (checked_eachSampled _ _) fun sampled => CheckedRun.bind (checked_emitDef _) fun startAt =>
      checked_whenLive _ fun _ => ?_
    exact checked_header1 (.data (.int .i64)) startAt (tail := fun hb i =>
        lowerEach regrow ov.1 sampled hb i (fun d xb => do
          let elem ← emitDef (.refElem ov.2 i)
          let ev ← eachElemValue x byRef elem
          let pre := (x, ev, org) :: (match idx with
            | some j => [(j, i, org)]
            | none => [])
          lowerBlock (some ⟨d, xb, .next hb .i64 i⟩) pre false body))
      (fun hb i => checked_lowerEach regrow ov.1 sampled hb i (fun d xb =>
        CheckedRun.bind (checked_emitDef _) fun elem => CheckedRun.bind (checked_eachElemValue _ _ _) fun ev =>
          checked_lowerBlock _ _ _ body))
  | .ret e org => by
    cases e with
    | some e =>
      simp only [lowerStmt]
      exact CheckedRun.bind (checked_lowerExpr e) fun value =>
        CheckedRun.bind (checked_coerceResult value org) fun _ =>
          CheckedRun.bind (CheckedRun.pure _) fun _ =>
            CheckedRun.bind (checked_leaveTo 0) fun _ => checked_emitTerm _
    | none =>
      simp only [lowerStmt]
      exact CheckedRun.bind (CheckedRun.pure _) fun _ => CheckedRun.bind (checked_leaveTo 0) fun _ => checked_emitTerm _
  | .brk _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact CheckedRun.pure _
    | some l =>
      simp only [lowerStmt]
      exact CheckedRun.bind (checked_leaveTo _) fun _ => checked_emitTerm _
  | .cont _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact CheckedRun.pure _
    | some l =>
      cases hk : l.cont with
      | jump h =>
        simp only [lowerStmt, hk]
        exact CheckedRun.bind (checked_leaveTo _) fun _ => checked_emitTerm _
      | next h t i =>
        simp only [lowerStmt, hk]
        exact CheckedRun.bind (checked_leaveTo _) fun _ => CheckedRun.bind (checked_emitDef _) fun _ => checked_emitTerm _
  | .print args org => by
    simp only [lowerStmt]
    exact CheckedRun.bind (checked_lowerPrintArgs args) fun _ => checked_emitEffect _
  | .assertS e org => by
    simp only [lowerStmt]
    exact CheckedRun.bind (checked_lowerExpr e) fun cv => checked_assert_core cv org
  | .abort _ org => by
    simp only [lowerStmt]
    exact checked_emitTerm _
  | .exit e org => by
    simp only [lowerStmt]
    exact CheckedRun.bind (checked_lowerExpr e) fun _ => checked_emitTerm _

end


theorem checked_finishFunction (impl : Impl) (value : ValueId) :
    CheckedRun (finishFunction impl value) := by
  unfold finishFunction
  refine CheckedRun.bind checked_read fun le =>
    CheckedRun.bind checked_isLive fun live => ?_
  cases live
  · exact CheckedRun.pure _
  · by_cases sink : (!impl.results.isEmpty && impl.body.value.isNone &&
        impl.body.diverges le.mod.noReturn) = true
    · simp only [sink, ↓reduceIte]
      exact CheckedRun.bind (checked_newBlock _) fun ⟨_, _⟩ =>
        CheckedRun.bind (checked_emitTerm _) fun _ =>
        CheckedRun.bind (checked_setCur _) fun _ => checked_emitTerm _
    · simp only [sink, ↓reduceIte]
      exact checked_emitTerm _

def Func.CheckedIndices (func : Func) : Prop :=
  ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts, Inst.CheckedIndex inst

theorem checked_finishBlocks {state : LS} (checked : CheckedIndices state) :
    ∀ block ∈ (finishBlocks state.blocks).toList, ∀ inst ∈ block.insts, Inst.CheckedIndex inst := by
  intro block blockMember inst instructionMember
  simp only [finishBlocks, Array.toList_map, List.mem_map] at blockMember
  obtain ⟨original, originalMember, rfl⟩ := blockMember
  exact checked inst (List.mem_flatMap.mpr ⟨original, originalMember, instructionMember⟩)

theorem checked_initState : CheckedIndices initState := by
  simp [CheckedIndices, initState, LS.insts]

theorem lowerImpl_checkedIndices (module : Core.Module) (impl : Impl) :
    Func.CheckedIndices (lowerImpl module impl) := by
  let action : B Unit := do
    let (b0, params) ← newBlock (impl.params.toList.map fun param => .data (tyOfVar impl param.var))
    setCur (some b0)
    let pre := (impl.params.toList.zip params).map fun (param, value) =>
      (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
    let value ← lowerBlock none pre false impl.body
    finishFunction impl value
  have preservation : CheckedRun action := by
    exact CheckedRun.bind (checked_newBlock _) fun ⟨_, _⟩ =>
      CheckedRun.bind (checked_setCur _) fun _ =>
      CheckedRun.bind (checked_lowerBlock _ _ _ _) fun _ => checked_finishFunction _ _
  let output := action (lowerEnv module impl.vars impl.results.toList) initState
  have checked := preservation (lowerEnv module impl.vars impl.results.toList) initState output.1 output.2 rfl checked_initState
  exact checked_finishBlocks checked

theorem lowerGlobal_checkedIndices (module : Core.Module) (global : Core.Global) :
    Func.CheckedIndices (lowerGlobal module global).init := by
  let action : B Unit := do
    let (b0, _) ← newBlock []
    setCur (some b0)
    let value ← lowerExpr global.init
    emitTerm (.ret [value] (some global.org))
  have preservation : CheckedRun action := by
    exact CheckedRun.bind (checked_newBlock _) fun ⟨_, _⟩ =>
      CheckedRun.bind (checked_setCur _) fun _ =>
      CheckedRun.bind (checked_lowerExpr _) fun _ => checked_emitTerm _
  let output := action (lowerEnv module #[] [global.ty]) initState
  have checked := preservation (lowerEnv module #[] [global.ty]) initState output.1 output.2 rfl checked_initState
  exact checked_finishBlocks checked

theorem Func.noProvenIndex {func : Func} (checked : Func.CheckedIndices func) :
    hasProvenIndex func = false := by
  apply Array.any_eq_false.mpr
  intro index bound
  intro proven
  obtain ⟨inst, member, isProven⟩ := List.any_eq_true.mp proven
  have instruction := checked _ (Array.mem_toList_iff.mpr (Array.getElem_mem bound)) inst member
  cases inst with
  | «def» value op => cases op <;> simp_all [Inst.CheckedIndex, Op.CheckedIndex]
  | eff effect => simp at isProven
  | term term => simp at isProven

theorem lowerImpl_checkEvidence (module : Core.Module) (impl : Impl)
    (values : Array (Option VTy)) :
    checkEvidence (lower module) (lowerImpl module impl) values = .ok () := by
  have noProven := Func.noProvenIndex (lowerImpl_checkedIndices module impl)
  have certificate : (lowerImpl module impl).certificate = none := rfl
  simp [checkEvidence, certificate, noProven, pure, Except.pure]

theorem lowerGlobal_checkEvidence (module : Core.Module) (global : Core.Global)
    (values : Array (Option VTy)) :
    checkEvidence (lower module) (lowerGlobal module global).init values = .ok () := by
  have noProven := Func.noProvenIndex (lowerGlobal_checkedIndices module global)
  have certificate : (lowerGlobal module global).init.certificate = none := rfl
  simp [checkEvidence, certificate, noProven, pure, Except.pure]

theorem lower_checkedIndices (module : Core.Module) (func : Func)
    (member : func ∈ (lower module).funcs.toList ++ (lower module).globals.toList.map (·.init)) :
    Func.CheckedIndices func := by
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
      simp [Func.CheckedIndices, invalidContextFunction]
    | some impl =>
      simp only [source, Option.map_some] at equality
      subst func
      exact lowerImpl_checkedIndices module impl
  · obtain ⟨global, globalMember, rfl⟩ := List.mem_map.mp initializer
    change global ∈ (module.globals.map (lowerGlobal module)).toList at globalMember
    simp only [Array.toList_map, List.mem_map] at globalMember
    obtain ⟨source, _, rfl⟩ := globalMember
    exact lowerGlobal_checkedIndices _ _

theorem lower_certificate_none (module : Core.Module) (func : Func)
    (member : func ∈ (lower module).funcs.toList ++ (lower module).globals.toList.map (·.init)) :
    func.certificate = none := by
  rcases List.mem_append.mp member with implementation | initializer
  · change func ∈ (module.contexts.map fun ctx =>
        match (module.impls.map fun impl => (impl, lowerImpl module impl))[ctx.impl]? with
        | some (impl, body) => { body with roots := lowerContextRootInfo ctx impl }
        | none => invalidContextFunction ctx).toList at implementation
    simp only [Array.toList_map, List.mem_map] at implementation
    obtain ⟨ctx, _, equality⟩ := implementation
    rw [Array.getElem?_map] at equality
    cases source : module.impls[ctx.impl]? <;>
      simp only [source, Option.map_none, Option.map_some] at equality <;>
      subst func <;> rfl
  · obtain ⟨global, globalMember, rfl⟩ := List.mem_map.mp initializer
    change global ∈ (module.globals.map (lowerGlobal module)).toList at globalMember
    simp only [Array.toList_map, List.mem_map] at globalMember
    obtain ⟨source, _, rfl⟩ := globalMember
    rfl

theorem lower_checkEvidence_of_info (module : Core.Module) (info : FnInfo)
    (member : info ∈ (lower module).infos) :
    asCheck .v080 info.label (checkEvidence (lower module) info.f info.vt) = .ok () := by
  simp only [Module.infos, List.mem_map] at member
  obtain ⟨⟨label, func⟩, labelledMember, rfl⟩ := member
  have functionMember : func ∈ (lower module).funcs.toList ++
      (lower module).globals.toList.map (·.init) := by
    simp only [Module.labelled, List.mem_append, List.mem_map] at labelledMember
    rcases labelledMember with ⟨source, sourceMember, equality⟩ | ⟨source, sourceMember, equality⟩
    · have functionEquality := congrArg Prod.snd equality
      simp only at functionEquality
      subst func
      exact List.mem_append.mpr (Or.inl sourceMember)
    · have functionEquality := congrArg Prod.snd equality
      simp only at functionEquality
      subst func
      exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨source, sourceMember, rfl⟩))
  have noProven := Func.noProvenIndex (lower_checkedIndices module func functionMember)
  have certificate := lower_certificate_none module func functionMember
  simp [checkEvidence, certificate, noProven, asCheck, pure, Except.pure]

theorem lower_checkEvidence (module : Core.Module) :
    (checkAll (lower module).infos fun info =>
      asCheck .v080 info.label (checkEvidence (lower module) info.f info.vt)) = .ok () := by
  have all : ∀ infos : List FnInfo,
      (∀ info ∈ infos, asCheck .v080 info.label
        (checkEvidence (lower module) info.f info.vt) = .ok ()) →
      (checkAll infos fun info =>
        asCheck .v080 info.label (checkEvidence (lower module) info.f info.vt)) = .ok () := by
    intro infos each
    induction infos with
    | nil => rfl
    | cons info rest inductionHypothesis =>
      unfold checkAll
      rw [each info (by simp)]
      apply inductionHypothesis
      intro next member
      exact each next (by simp [member])
  exact all _ (lower_checkEvidence_of_info module)

end Goose.Lower.Validation
