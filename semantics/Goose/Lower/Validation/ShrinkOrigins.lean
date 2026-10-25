import Goose.Lower.Validation.Typing
import Goose.Lower.Validation.PushOrigins
import Goose.Lower.Validation.Origins

namespace Goose.Lower.Validation.ShrinkOrigins

open Goose.Core Goose.GIR

def Op.OriginPresent (op : Op) : Prop :=
  (Inst.def 0 op).needsOriginIn .shrink = true → op.origin.isSome = true

def Inst.OriginPresent (inst : Inst) : Prop :=
  inst.needsOriginIn .shrink = true → inst.origin.isSome = true

def PresentOrigins (state : LS) : Prop :=
  ∀ inst ∈ state.insts, Inst.OriginPresent inst

def OriginRun (action : B α) : Prop :=
  ∀ le before result after, action le before = (result, after) →
    PresentOrigins before → PresentOrigins after

theorem OriginRun.pure (value : α) : OriginRun (pure value) := by
  intro le before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact checked

theorem OriginRun.bind {action : B α} {next : α → B β}
    (first : OriginRun action) (second : ∀ value, OriginRun (next value)) :
    OriginRun (action >>= next) := by
  intro le before result after run checked
  obtain ⟨value, mid, firstRun, secondRun⟩ := bind_eq.mp run
  exact second value _ _ _ _ secondRun (first _ _ _ _ firstRun checked)

theorem OriginRun.of_unchanged {action : B α}
    (unchanged : ∀ le state, (action le state).2.insts = state.insts) : OriginRun action := by
  intro le before result after run checked
  have equality := unchanged le before
  rw [run] at equality
  simpa only [PresentOrigins, equality] using checked

theorem origins_recordValueRootRecipe (value : ValueId) (sourceScope : ScopeId) :
    OriginRun (recordValueRootRecipe value sourceScope) := by
  apply OriginRun.of_unchanged
  intro le state
  rw [recordValueRootRecipe_run]
  rfl

theorem origins_recordReadValueRootRecipe (value : ValueId) (place : Place) :
    OriginRun (recordReadValueRootRecipe value place) := by
  apply OriginRun.of_unchanged
  intro le state
  cases place <;>
    simp [recordReadValueRootRecipe_run, recordValueRootSource_run] <;>
    (try split) <;> rfl

theorem origins_appendInst {before : LS} (checked : PresentOrigins before)
    (block : BlockId) (inst : Inst) (instruction : Inst.OriginPresent inst) :
    PresentOrigins (before.appendInst block inst) := by
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

theorem origins_emitDef (op : Op) (instruction : Op.OriginPresent op := by
      simp [Op.OriginPresent, Inst.needsOriginIn, Inst.needsOrigin, Op.origin]) :
    OriginRun (emitDef op) := by
  intro le before result after run checked
  cases current : before.cur with
  | none =>
    rw [emitDef_none op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitDef_run op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    have appended := origins_appendInst checked block (.def before.vals.size op) (by cases op <;> simp_all [Inst.OriginPresent, Inst.origin, Inst.needsOriginIn, Inst.needsOrigin, Op.OriginPresent])
    simpa only [PresentOrigins, LS.insts, LS.appendInst] using appended

theorem origins_newBlock (types : List VTy) : OriginRun (newBlock types) := by
  apply OriginRun.of_unchanged
  intro le state
  rw [newBlock_run_general]
  simp [LS.insts]

theorem origins_emitEffect (effect : Effect)
    (instruction : Inst.OriginPresent (.eff effect) := by
      simp [Inst.OriginPresent, Inst.needsOriginIn, Inst.needsOrigin, Inst.origin, Effect.origin]) : OriginRun (emitEffect effect) := by
  intro le before result after run checked
  cases current : before.cur with
  | none =>
    rw [emitEffect_none effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitEffect_run effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact origins_appendInst checked block (.eff effect) instruction

theorem origins_setCur (block : Option BlockId) : OriginRun (setCur block) := by
  apply OriginRun.of_unchanged
  intro le state
  rw [setCur_run]
  rfl

theorem origins_patchTerm (block : BlockId) (term : Term)
    (instruction : Inst.OriginPresent (.term term) := by
      simp [Inst.OriginPresent, Inst.needsOriginIn, Inst.needsOrigin, Inst.origin, Term.origin]) : OriginRun (patchTerm block term) := by
  intro le before result after run checked
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  exact origins_appendInst checked block (.term term) instruction

theorem origins_emitTerm (term : Term)
    (instruction : Inst.OriginPresent (.term term) := by
      simp [Inst.OriginPresent, Inst.needsOriginIn, Inst.needsOrigin, Inst.origin, Term.origin]) : OriginRun (emitTerm term) := by
  intro le before result after run checked
  cases current : before.cur with
  | none =>
    rw [emitTerm_none term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitTerm_run term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    have appended := origins_appendInst checked block (.term term) instruction
    simpa only [PresentOrigins, LS.insts, LS.appendInst] using appended

theorem origins_curBlock : OriginRun curBlock := by
  apply OriginRun.of_unchanged
  intro le state
  rw [curBlock_run]

theorem origins_get : OriginRun (get : B LS) := by
  apply OriginRun.of_unchanged
  intros
  rfl

theorem origins_read : OriginRun (read : B LEnv) := by
  apply OriginRun.of_unchanged
  intros
  rfl

theorem origins_valTy (value : ValueId) : OriginRun (valTy value) := by
  apply OriginRun.of_unchanged
  intro le state
  rw [valTy_run]

theorem origins_pushScope (scope : ScopeId) : OriginRun (pushScope scope) := by
  apply OriginRun.of_unchanged
  intro le state
  rw [pushScope_run]
  rfl

theorem origins_popScope : OriginRun popScope := by
  apply OriginRun.of_unchanged
  intro le state
  rw [popScope_run]
  rfl

theorem origins_inScope (scope : ScopeId) {action : B α} (typed : OriginRun action) :
    OriginRun (inScope scope action) := by
  unfold inScope
  exact OriginRun.bind (origins_pushScope _) fun _ =>
    OriginRun.bind typed fun _ => OriginRun.bind origins_popScope fun _ => OriginRun.pure _

theorem origins_whenLive (default : α) {action : BlockId → B α}
    (typed : ∀ block, OriginRun (action block)) : OriginRun (whenLive default action) := by
  unfold whenLive
  refine OriginRun.bind origins_curBlock fun current => ?_
  cases current
  · exact OriginRun.pure _
  · exact typed _

theorem origins_intTyOf (v : ValueId) : OriginRun (intTyOf v) := by
  unfold intTyOf
  refine OriginRun.bind (origins_valTy v) fun t => ?_
  cases t with
  | data t => cases t <;> exact OriginRun.pure _
  | view _ _ => exact OriginRun.pure _

theorem origins_freezeTo (m : Mutability) (r : ValueId) : OriginRun (freezeTo m r) := by
  unfold freezeTo
  refine OriginRun.bind (origins_valTy r) fun t => ?_
  cases m <;> cases t <;> first
    | exact OriginRun.pure _
    | (rename_i t; cases t <;> first | exact OriginRun.pure _ | (rename_i m' _; cases m' <;> first | exact OriginRun.pure _ | exact origins_emitDef _))

theorem origins_borrowTo (m : Mutability) (r : ValueId) : OriginRun (borrowTo m r) := by
  intro le before result after run
  rcases borrowTo_cases run with frozen | borrowed
  · exact origins_freezeTo m r le before result after frozen
  · exact origins_emitDef (.ownerBorrow r) (by simp [Op.OriginPresent, Inst.needsOriginIn, Inst.needsOrigin]) le before result after borrowed

theorem origins_coerceTo (target : Ty) (r : ValueId) (org : OriginId) : OriginRun (coerceTo target r org) := by
  unfold coerceTo
  refine OriginRun.bind (origins_valTy r) fun source => ?_
  split
  · exact origins_emitDef _
  · exact OriginRun.bind (origins_emitDef _) (fun _ => origins_emitDef _)
  · exact OriginRun.pure _

theorem origins_coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) :
    OriginRun (coerceSlot slot value org) := by
  unfold coerceSlot
  refine OriginRun.bind origins_read fun le => ?_
  cases le.slots[slot]? with
  | none => exact OriginRun.pure _
  | some destination => exact origins_coerceTo destination.ty value org

theorem origins_coerceResult (value : ValueId) (org : OriginId) :
    OriginRun (coerceResult value org) := by
  unfold coerceResult
  refine OriginRun.bind origins_read fun le => ?_
  cases le.results.head? with
  | none => exact OriginRun.pure _
  | some destination => exact origins_coerceTo destination value org

theorem origins_growOwner (r : ValueId) : OriginRun (growOwner r) := by
  unfold growOwner
  refine OriginRun.bind (origins_valTy r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact OriginRun.pure _ | (rename_i m' t'; cases t' <;> exact OriginRun.pure _)
  | view _ _ => exact OriginRun.pure _

theorem origins_leaveAll : ∀ scs, OriginRun (leaveAll scs)
  | [] => OriginRun.pure _
  | sc :: rest => by
    unfold leaveAll
    exact OriginRun.bind (origins_emitEffect _) fun _ => origins_leaveAll rest

theorem origins_leaveTo (d : Nat) : OriginRun (leaveTo d) := by
  unfold leaveTo
  exact OriginRun.bind origins_get fun _ => origins_leaveAll _

theorem origins_initSlots : ∀ ps, OriginRun (initSlots ps)
  | [] => OriginRun.pure _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact OriginRun.bind (origins_emitEffect _) fun _ => origins_initSlots rest

theorem origins_isLive : OriginRun isLive := by
  unfold isLive
  exact OriginRun.bind origins_curBlock fun _ => OriginRun.pure _

theorem origins_eachElemValue (x : VarId) (byRef : Bool) (elem : ValueId) :
    OriginRun (eachElemValue x byRef elem) := by
  unfold eachElemValue
  cases byRef
  · exact origins_emitDef _
  · refine OriginRun.bind origins_read fun le => ?_
    cases le.vars[x]? with
    | none => exact OriginRun.pure _
    | some lv =>
      dsimp only
      cases lv.ty with
      | ref m t => exact origins_borrowTo m elem
      | _ => exact OriginRun.pure _

theorem origins_regrowOf (o : Option ValueId) : OriginRun (regrowOf o) := by
  cases o with
  | none => exact OriginRun.pure _
  | some r => exact origins_growOwner r

theorem origins_eachSampled (regrow : Bool) (vw : ValueId) : OriginRun (eachSampled regrow vw) := by
  unfold eachSampled
  cases regrow
  · exact origins_emitDef _
  · exact OriginRun.pure _

theorem origins_eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    OriginRun (eachLen regrow owner sampled) := by
  unfold eachLen
  cases regrow
  · exact OriginRun.pure _
  · exact origins_emitDef _

theorem origins_fork (condition : ValueId) : OriginRun (fork condition) := by
  unfold fork
  exact OriginRun.bind (origins_newBlock _) fun ⟨thenBlock, _⟩ =>
    OriginRun.bind (origins_newBlock _) fun ⟨elseBlock, _⟩ =>
    OriginRun.bind (origins_emitTerm _) fun _ => OriginRun.pure _

theorem origins_patchBrs (target : BlockId) : ∀ incoming, OriginRun (patchBrs target incoming)
  | [] => OriginRun.pure _
  | (block, value) :: rest => by
    unfold patchBrs
    exact OriginRun.bind (origins_patchTerm _ _) fun _ => origins_patchBrs target rest

theorem origins_patchBrs0 (target : BlockId) : ∀ incoming, OriginRun (patchBrs0 target incoming)
  | [] => OriginRun.pure _
  | block :: rest => by
    unfold patchBrs0
    exact OriginRun.bind (origins_patchTerm _ _) fun _ => origins_patchBrs0 target rest

theorem origins_joinValue (endT : Option BlockId) (vt : ValueId) (endF : Option BlockId) (vf : ValueId) :
    OriginRun (joinValue endT vt endF vf) := by
  unfold joinValue
  cases endT <;> cases endF
  · exact OriginRun.bind (origins_setCur _) fun _ => OriginRun.pure _
  all_goals
    exact OriginRun.bind (origins_valTy _) fun _ =>
      OriginRun.bind (origins_newBlock _) fun ⟨_, _⟩ =>
      OriginRun.bind (origins_patchBrs _ _) fun _ =>
      OriginRun.bind (origins_setCur _) fun _ => OriginRun.pure _

theorem origins_joinArms (endT endF : Option BlockId) : OriginRun (joinArms endT endF) := by
  unfold joinArms
  cases endT <;> cases endF
  · exact origins_setCur _
  all_goals
    exact OriginRun.bind (origins_newBlock _) fun ⟨_, _⟩ =>
      OriginRun.bind (origins_patchBrs0 _ _) fun _ => origins_setCur _

theorem origins_scFork (isAnd : Bool) (value : ValueId) : OriginRun (scFork isAnd value) := by
  unfold scFork
  refine OriginRun.bind (origins_newBlock _) fun ⟨_, _⟩ =>
    OriginRun.bind (origins_newBlock _) fun ⟨_, _⟩ => ?_
  cases isAnd <;> exact OriginRun.bind (origins_emitTerm _) fun _ => OriginRun.pure _

theorem origins_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (typed : OriginRun rhs) : OriginRun (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  exact origins_whenLive _ fun _ =>
    OriginRun.bind (origins_scFork _ _) fun ⟨_, _, _⟩ =>
    OriginRun.bind (origins_setCur _) fun _ => OriginRun.bind typed fun _ =>
    OriginRun.bind (origins_emitTerm _) fun _ =>
    OriginRun.bind (origins_setCur _) fun _ => OriginRun.pure _

theorem origins_loopBody (cv : ValueId) {body : Nat → BlockId → B ValueId} {back : B Unit}
    (hbody : ∀ depth exitBlock, OriginRun (body depth exitBlock)) (hback : OriginRun back) :
    OriginRun (loopBody cv body back) := by
  unfold loopBody
  exact OriginRun.bind origins_get fun _ =>
    OriginRun.bind (origins_fork _) fun ⟨_, _⟩ =>
    OriginRun.bind (origins_setCur _) fun _ => OriginRun.bind (hbody _ _) fun _ =>
    OriginRun.bind hback fun _ => origins_setCur _

theorem origins_rangeBack (t : IntTy) (i : ValueId) (hb : BlockId) : OriginRun (rangeBack t i hb) := by
  unfold rangeBack
  refine OriginRun.bind origins_isLive fun live => ?_
  cases live
  · exact OriginRun.pure _
  · exact OriginRun.bind (origins_emitDef _) fun _ => origins_emitTerm _


theorem origins_lowerWhile (hb : BlockId) {cond : B ValueId} {body : Nat → BlockId → B ValueId}
    (hc : OriginRun cond) (hbody : ∀ d xb, OriginRun (body d xb)) : OriginRun (lowerWhile hb cond body) := by
  unfold lowerWhile
  exact OriginRun.bind hc fun cv => origins_whenLive _ fun _ =>
    origins_loopBody cv hbody (origins_emitTerm _)

theorem origins_lowerRange (t : IntTy) (i b : ValueId) (hb : BlockId) {body : Nat → BlockId → B ValueId}
    (hbody : ∀ d xb, OriginRun (body d xb)) : OriginRun (lowerRange t i b hb body) := by
  unfold lowerRange
  exact OriginRun.bind (origins_emitDef _) fun c => origins_loopBody c hbody (origins_rangeBack _ _ _)

theorem origins_lowerEach (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (hb : BlockId)
    (i : ValueId) {body : Nat → BlockId → B ValueId} (hbody : ∀ d xb, OriginRun (body d xb)) :
    OriginRun (lowerEach regrow owner sampled hb i body) := by
  unfold lowerEach
  exact OriginRun.bind (origins_eachLen _ _ _) fun n => OriginRun.bind (origins_emitDef _) fun c =>
    origins_loopBody c hbody (origins_rangeBack _ _ _)

theorem origins_ifE_core (cv : ValueId) (sourceScope : ScopeId) {a1 a2 : B ValueId} (h1 : OriginRun a1) (h2 : OriginRun a2) :
    OriginRun (whenLive 0 fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let vt ← a1
      let endT ← curBlock
      setCur (some eb)
      let vf ← a2
      let endF ← curBlock
      let result ← joinValue endT vt endF vf
      recordValueRootRecipe result sourceScope
      pure result) := by
  exact origins_whenLive _ fun _ =>
    OriginRun.bind (origins_fork _) fun ⟨_, _⟩ =>
    OriginRun.bind (origins_setCur _) fun _ => OriginRun.bind h1 fun _ =>
    OriginRun.bind origins_curBlock fun _ => OriginRun.bind (origins_setCur _) fun _ =>
    OriginRun.bind h2 fun _ => OriginRun.bind origins_curBlock fun _ =>
    OriginRun.bind (origins_joinValue _ _ _ _) fun result =>
    OriginRun.bind (origins_recordValueRootRecipe result sourceScope) fun _ => OriginRun.pure result

theorem origins_ifS_some_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : OriginRun a1) (h2 : OriginRun a2) :
    OriginRun (whenLive () fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let _ ← a1
      let endT ← curBlock
      setCur (some eb)
      let _ ← a2
      let endF ← curBlock
      joinArms endT endF) := by
  exact origins_whenLive _ fun _ =>
    OriginRun.bind (origins_fork _) fun ⟨_, _⟩ =>
    OriginRun.bind (origins_setCur _) fun _ => OriginRun.bind h1 fun _ =>
    OriginRun.bind origins_curBlock fun _ => OriginRun.bind (origins_setCur _) fun _ =>
    OriginRun.bind h2 fun _ => OriginRun.bind origins_curBlock fun _ => origins_joinArms _ _

theorem origins_ifS_none_core (cv : ValueId) {a1 : B ValueId} (h1 : OriginRun a1) :
    OriginRun (whenLive () fun _ => do
      let (tb, jb) ← fork cv
      setCur (some tb)
      let _ ← a1
      emitTerm (.br jb [])
      setCur (some jb)) := by
  exact origins_whenLive _ fun _ =>
    OriginRun.bind (origins_fork _) fun ⟨_, _⟩ =>
    OriginRun.bind (origins_setCur _) fun _ => OriginRun.bind h1 fun _ =>
    OriginRun.bind (origins_emitTerm _) fun _ => origins_setCur _

theorem origins_assert_core (cv : ValueId) (org : OriginId) :
    OriginRun (whenLive () fun _ => do
      let (pb, fb) ← fork cv
      setCur (some fb)
      emitTerm (.abort .assert (some org))
      setCur (some pb)) := by
  exact origins_whenLive _ fun _ =>
    OriginRun.bind (origins_fork _) fun ⟨_, _⟩ =>
    OriginRun.bind (origins_setCur _) fun _ => OriginRun.bind (origins_emitTerm _) fun _ => origins_setCur _

theorem origins_header0 {tail : BlockId → B Unit} (ht : ∀ h, OriginRun (tail h)) :
    OriginRun (do
      let (hb, _) ← newBlock []
      emitTerm (.br hb [])
      setCur (some hb)
      tail hb) := by
  exact OriginRun.bind (origins_newBlock _) fun ⟨_, _⟩ =>
    OriginRun.bind (origins_emitTerm _) fun _ => OriginRun.bind (origins_setCur _) fun _ => ht _

theorem origins_header1 (ty : VTy) (a : ValueId) {tail : BlockId → ValueId → B Unit}
    (ht : ∀ h i, OriginRun (tail h i)) :
    OriginRun (do
      let (hb, hs) ← newBlock [ty]
      let i := hs.headD 0
      emitTerm (.br hb [a])
      setCur (some hb)
      tail hb i) := by
  exact OriginRun.bind (origins_newBlock _) fun ⟨_, _⟩ =>
    OriginRun.bind (origins_emitTerm _) fun _ => OriginRun.bind (origins_setCur _) fun _ => ht _ _

mutual

theorem origins_lowerExpr (e : Expr)
    (source : PushOrigins.Present (e.pushOrigins) := by solve_by_elim [And.left, And.right]) :
    OriginRun (lowerExpr e) := by
  cases e with
  | structLit t es =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerExprs es) fun _ => origins_emitDef _
  | lit t n =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]; exact origins_emitDef _
  | bool b =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]; exact origins_emitDef _
  | read p =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerPlace p) fun _ =>
      OriginRun.bind (origins_emitDef _) fun value =>
        OriginRun.bind (origins_recordReadValueRootRecipe value p) fun _ => OriginRun.pure value
  | ref m p =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerPlace p) fun r => origins_borrowTo m r
  | slice m v lo hi org =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerView v) fun _ => OriginRun.bind (origins_lowerBound lo) fun _ =>
      OriginRun.bind (origins_lowerBound hi) fun _ => origins_emitDef _
  | len v =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerView v) fun _ => origins_emitDef _
  | un op e org =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerExpr e) fun a => OriginRun.bind (origins_intTyOf a) fun _ => origins_emitDef _
  | bin op a b org =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerExpr a) fun x => OriginRun.bind (origins_lowerExpr b) fun y =>
      OriginRun.bind (origins_intTyOf x) fun _ => origins_emitDef _
  | cmp op a b =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    refine OriginRun.bind (origins_lowerExpr a) fun x => OriginRun.bind (origins_lowerExpr b) fun y =>
      OriginRun.bind (origins_valTy x) fun t => ?_
    cases t with
    | data t => cases t <;> exact origins_emitDef _
    | view _ _ => exact origins_emitDef _
  | and a b =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerExpr a) fun x => origins_shortCircuit true x (origins_lowerExpr b)
  | or a b =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerExpr a) fun x => origins_shortCircuit false x (origins_lowerExpr b)
  | not e =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerExpr e) fun _ => origins_emitDef _
  | conv k target e org =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerExpr e) fun a => OriginRun.bind (origins_intTyOf a) fun _ => origins_emitDef _
  | call c args org =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerArgs args) fun _ =>
      OriginRun.bind (origins_emitDef _) fun r => OriginRun.bind origins_read fun le => by
        cases le.mod.noReturn c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact OriginRun.pure _ | exact OriginRun.bind (origins_emitTerm _) fun _ => OriginRun.pure _
  | push owner e org =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerPlace owner) fun r => OriginRun.bind (origins_lowerExpr e) fun v =>
      origins_emitDef (.push r v org) (by
        simp [Op.OriginPresent, Inst.needsOriginIn, Op.origin, source.1])
  | pop owner org =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerPlace owner) fun _ => origins_emitDef _
  | ifE c t f =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerExpr c) fun cv =>
      origins_ifE_core cv (sourceBlockScope t) (origins_lowerBlock none [] true t) (origins_lowerBlock none [] true f)
  | blockE b =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact origins_lowerBlock none [] true b
  | arrLit t es =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerExprs es) fun _ => origins_emitDef _
  | fill t e =>
    try simp [Expr.pushOrigins] at source
    simp only [lowerExpr]
    exact OriginRun.bind (origins_lowerExpr e) fun _ => origins_emitDef _

theorem origins_lowerExprs (es : List Expr)
    (source : PushOrigins.Present (es.flatMap Expr.pushOrigins) := by solve_by_elim [And.left, And.right]) :
    OriginRun (lowerExprs es) := by
  cases es with
  | nil =>
    try simp at source
    simp only [lowerExprs]; exact OriginRun.pure _
  | cons e rest =>
    try simp at source
    simp only [lowerExprs]
    exact OriginRun.bind (origins_lowerExpr e) fun _ => OriginRun.bind (origins_lowerExprs rest) fun _ => OriginRun.pure _

theorem origins_lowerArg (a : Arg)
    (source : PushOrigins.Present (a.pushOrigins) := by solve_by_elim [And.left, And.right]) :
    OriginRun (lowerArg a) := by
  cases a with
  | byVal e =>
    try simp [Arg.pushOrigins] at source
    simp only [lowerArg]; exact origins_lowerExpr e
  | byRef m p =>
    try simp [Arg.pushOrigins] at source
    simp only [lowerArg]
    exact OriginRun.bind (origins_lowerPlace p) fun r => origins_borrowTo m r

theorem origins_lowerArgs (args : List Arg)
    (source : PushOrigins.Present (args.flatMap Arg.pushOrigins) := by solve_by_elim [And.left, And.right]) :
    OriginRun (lowerArgs args) := by
  cases args with
  | nil =>
    try simp at source
    simp only [lowerArgs]; exact OriginRun.pure _
  | cons a rest =>
    try simp at source
    simp only [lowerArgs]
    exact OriginRun.bind (origins_lowerArg a) fun _ => OriginRun.bind (origins_lowerArgs rest) fun _ => OriginRun.pure _

theorem origins_lowerPlace (p : Place)
    (source : PushOrigins.Present (p.pushOrigins) := by solve_by_elim [And.left, And.right]) :
    OriginRun (lowerPlace p) := by
  cases p with
  | field owner i =>
    try simp [Place.pushOrigins] at source
    simp only [lowerPlace]
    exact OriginRun.bind (origins_lowerPlace owner) fun _ => origins_emitDef _
  | var x =>
    try simp [Place.pushOrigins] at source
    simp only [lowerPlace]; exact origins_emitDef _
  | global g =>
    try simp [Place.pushOrigins] at source
    simp only [lowerPlace]; exact origins_emitDef _
  | deref e =>
    try simp [Place.pushOrigins] at source
    simp only [lowerPlace]; exact origins_lowerExpr e
  | elem v i org =>
    try simp [Place.pushOrigins] at source
    simp only [lowerPlace]
    exact OriginRun.bind (origins_lowerView v) fun _ => OriginRun.bind (origins_lowerExpr i) fun _ => origins_emitDef _

theorem origins_lowerView (v : View)
    (source : PushOrigins.Present (v.pushOrigins) := by solve_by_elim [And.left, And.right]) :
    OriginRun (lowerView v) := by
  cases v with
  | of p =>
    try simp [View.pushOrigins] at source
    simp only [lowerView]
    exact OriginRun.bind (origins_lowerPlace p) fun _ => origins_emitDef _
  | val e =>
    try simp [View.pushOrigins] at source
    simp only [lowerView]
    exact OriginRun.bind (origins_lowerExpr e) fun _ => origins_emitDef _

theorem origins_lowerBound (b : Bound)
    (source : PushOrigins.Present (b.pushOrigins) := by solve_by_elim [And.left, And.right]) :
    OriginRun (lowerBound b) := by
  cases b with
  | omitted =>
    try simp [Bound.pushOrigins] at source
    simp only [lowerBound]; exact OriginRun.pure _
  | expr e =>
    try simp [Bound.pushOrigins] at source
    simp only [lowerBound]
    exact OriginRun.bind (origins_lowerExpr e) fun _ => OriginRun.pure _
  | fromEnd e =>
    try simp [Bound.pushOrigins] at source
    simp only [lowerBound]
    exact OriginRun.bind (origins_lowerExpr e) fun _ => OriginRun.pure _

theorem origins_lowerEachSource (v : View)
    (source : PushOrigins.Present (v.pushOrigins) := by solve_by_elim [And.left, And.right]) :
    OriginRun (lowerEachSource v) := by
  cases v with
  | of p =>
    try simp [View.pushOrigins] at source
    simp only [lowerEachSource]
    exact OriginRun.bind (origins_lowerPlace p) fun _ => OriginRun.bind (origins_emitDef _) fun _ => OriginRun.pure _
  | val e =>
    try simp [View.pushOrigins] at source
    simp only [lowerEachSource]
    exact OriginRun.bind (origins_lowerExpr e) fun _ => OriginRun.bind (origins_emitDef _) fun _ => OriginRun.pure _

theorem origins_lowerBlockValue (want : Bool) (v : Option Expr)
    (source : PushOrigins.Present (match v with | none => [] | some e => e.pushOrigins) := by solve_by_elim [And.left, And.right]) :
    OriginRun (lowerBlockValue want v) := by
  cases v with
  | some e =>
    try simp at source
    simp only [lowerBlockValue]; exact origins_lowerExpr e
  | none =>
    try simp at source
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact OriginRun.pure _
    · simp only [lowerBlockValue, ↓reduceIte]; exact origins_emitDef _

theorem origins_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) (b : Core.Block)
    (source : PushOrigins.Present (b.pushOrigins) := by solve_by_elim [And.left, And.right]) :
    OriginRun (lowerBlock lc pre want b) := by
  cases b with
  | mk sc stmts value =>
    cases value <;> simp only [Core.Block.pushOrigins, PushOrigins.present_append] at source
    all_goals
      simp only [lowerBlock]
      exact OriginRun.bind (origins_emitEffect _) fun _ => origins_inScope sc
        (OriginRun.bind (origins_initSlots _) fun _ => OriginRun.bind (origins_lowerStmts lc stmts source.1) fun _ =>
          OriginRun.bind (origins_lowerBlockValue want _ source.2) fun _ => OriginRun.bind (origins_emitEffect _) fun _ =>
          OriginRun.pure _)

theorem origins_lowerStmts (lc : Option LoopCtx) (ss : List Stmt)
    (source : PushOrigins.Present (ss.flatMap Stmt.pushOrigins) := by solve_by_elim [And.left, And.right]) :
    OriginRun (lowerStmts lc ss) := by
  cases ss with
  | nil =>
    try simp at source
    simp only [lowerStmts]; exact OriginRun.pure _
  | cons s rest =>
    try simp at source
    simp only [lowerStmts]
    refine OriginRun.bind origins_isLive fun live => ?_
    cases live
    · exact OriginRun.pure _
    · exact OriginRun.bind (origins_lowerStmt lc s) fun _ => origins_lowerStmts lc rest

theorem origins_lowerPrintArgs (args : List PrintArg)
    (source : PushOrigins.Present (args.flatMap PrintArg.pushOrigins) := by solve_by_elim [And.left, And.right]) :
    OriginRun (lowerPrintArgs args) := by
  cases args with
  | nil => simp only [lowerPrintArgs]; exact OriginRun.pure _
  | cons arg rest =>
    cases arg with
    | text text =>
      simp only [List.flatMap_cons, PrintArg.pushOrigins, List.nil_append] at source
      simp only [lowerPrintArgs]
      exact OriginRun.bind (origins_lowerPrintArgs rest source) fun _ => OriginRun.pure _
    | expr expr =>
      simp only [List.flatMap_cons, PrintArg.pushOrigins, PushOrigins.present_append] at source
      simp only [lowerPrintArgs]
      exact OriginRun.bind (origins_lowerExpr expr source.1) fun _ =>
        OriginRun.bind (origins_lowerPrintArgs rest source.2) fun _ => OriginRun.pure _

theorem origins_lowerStmt (lc : Option LoopCtx) (s : Stmt)
    (source : PushOrigins.Present (s.pushOrigins) := by solve_by_elim [And.left, And.right]) :
    OriginRun (lowerStmt lc s) := by
  cases s with
  | letS x e org =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    exact OriginRun.bind (origins_lowerExpr e) fun value =>
      OriginRun.bind (origins_coerceSlot x value org) fun _ => origins_emitEffect _
  | assign p e org =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    exact OriginRun.bind (origins_lowerPlace p) fun _ => OriginRun.bind (origins_lowerExpr e) fun _ => origins_emitEffect _
  | assignOp op p e org =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    exact OriginRun.bind (origins_lowerPlace p) fun _ => OriginRun.bind (origins_emitDef _) fun _ =>
      OriginRun.bind (origins_lowerExpr e) fun _ => OriginRun.bind (origins_intTyOf _) fun _ =>
      OriginRun.bind (origins_emitDef _) fun _ => origins_emitEffect _
  | rebind x e org =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    exact OriginRun.bind (origins_lowerExpr e) fun value =>
      OriginRun.bind (origins_coerceSlot x value org) fun _ =>
        OriginRun.bind (origins_emitDef _) fun _ => origins_emitEffect _
  | expr e _ =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    exact OriginRun.bind (origins_lowerExpr e) fun _ => OriginRun.pure _
  | append owner src org =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    exact OriginRun.bind (origins_lowerPlace owner) fun _ => OriginRun.bind (origins_lowerView src) fun _ =>
      origins_emitEffect _
  | popN owner count org =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    exact OriginRun.bind (origins_lowerPlace owner) fun r => OriginRun.bind (origins_lowerExpr count) fun n =>
      origins_emitEffect (.popN r n (some org))
  | resize owner size fill org =>
    cases fill with
    | none =>
      simp only [Stmt.pushOrigins, List.append_nil, PushOrigins.present_append] at source
      simp only [lowerStmt]
      exact OriginRun.bind (origins_lowerPlace owner source.1) fun r =>
        OriginRun.bind (origins_lowerExpr size source.2) fun n =>
          OriginRun.bind (OriginRun.pure _) fun fill => origins_emitEffect (.resize r n fill (some org))
    | some fill =>
      simp only [Stmt.pushOrigins, PushOrigins.present_append] at source
      simp only [lowerStmt]
      exact OriginRun.bind (origins_lowerPlace owner source.1.1) fun r =>
        OriginRun.bind (origins_lowerExpr size source.1.2) fun n =>
          OriginRun.bind (origins_lowerExpr fill source.2) fun v =>
            origins_emitEffect (.resize r n (some v) (some org))
  | clear owner org =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    exact OriginRun.bind (origins_lowerPlace owner) fun r => origins_emitEffect (.clear r (some org))
  | assignWhole owner replacement org =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    exact OriginRun.bind (origins_lowerPlace owner) fun r =>
      OriginRun.bind (origins_emitEffect (.clear r (some org))) fun _ =>
      OriginRun.bind (origins_lowerExpr replacement) fun run =>
        origins_emitEffect (.replace r run (some org))
  | ifS c t f _ =>
    cases f with
    | none =>
      simp only [Stmt.pushOrigins, List.append_nil, PushOrigins.present_append] at source
      simp only [lowerStmt]
      exact OriginRun.bind (origins_lowerExpr c source.1) fun cv =>
        origins_ifS_none_core cv (origins_lowerBlock lc [] false t source.2)
    | some fb =>
      simp only [Stmt.pushOrigins, PushOrigins.present_append] at source
      simp only [lowerStmt]
      exact OriginRun.bind (origins_lowerExpr c source.1.1) fun cv =>
        origins_ifS_some_core cv (origins_lowerBlock lc [] false t source.1.2)
          (origins_lowerBlock lc [] false fb source.2)
  | «while» c body _ =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    exact origins_header0 (tail := fun hb => lowerWhile hb (lowerExpr c)
        (fun d xb => lowerBlock (some ⟨d, xb, .jump hb⟩) [] false body))
      (fun hb => origins_lowerWhile hb (origins_lowerExpr c) (fun d xb => origins_lowerBlock _ _ _ body))
  | forRange x lo hi body org =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    refine OriginRun.bind (origins_lowerExpr lo) fun a => OriginRun.bind (origins_lowerExpr hi) fun b =>
      origins_whenLive _ fun _ => OriginRun.bind (origins_intTyOf a) fun t => ?_
    exact origins_header1 (.data (.int t)) a (tail := fun hb i => lowerRange t i b hb (fun d xb =>
        lowerBlock (some ⟨d, xb, .next hb t i⟩) [(x, i, org)] false body))
      (fun hb i => origins_lowerRange t i b hb (fun d xb => origins_lowerBlock _ _ _ body))
  | forEach x idx v byRef body org =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    refine OriginRun.bind (origins_lowerEachSource v) fun ov => OriginRun.bind (origins_regrowOf _) fun regrow =>
      OriginRun.bind (origins_eachSampled _ _) fun sampled => OriginRun.bind (origins_emitDef _) fun startAt =>
      origins_whenLive _ fun _ => ?_
    exact origins_header1 (.data (.int .i64)) startAt (tail := fun hb i =>
        lowerEach regrow ov.1 sampled hb i (fun d xb => do
          let elem ← emitDef (.refElem ov.2 i)
          let ev ← eachElemValue x byRef elem
          let pre := (x, ev, org) :: (match idx with
            | some j => [(j, i, org)]
            | none => [])
          lowerBlock (some ⟨d, xb, .next hb .i64 i⟩) pre false body))
      (fun hb i => origins_lowerEach regrow ov.1 sampled hb i (fun d xb =>
        OriginRun.bind (origins_emitDef _) fun elem => OriginRun.bind (origins_eachElemValue _ _ _) fun ev =>
          origins_lowerBlock _ _ _ body))
  | ret e org =>
    cases e with
    | some e =>
      simp only [Stmt.pushOrigins] at source
      simp only [lowerStmt]
      exact OriginRun.bind (origins_lowerExpr e source) fun value =>
        OriginRun.bind (origins_coerceResult value org) fun _ =>
          OriginRun.bind (OriginRun.pure _) fun _ =>
            OriginRun.bind (origins_leaveTo 0) fun _ => origins_emitTerm _
    | none =>
      simp only [lowerStmt]
      exact OriginRun.bind (OriginRun.pure _) fun _ => OriginRun.bind (origins_leaveTo 0) fun _ => origins_emitTerm _
  | brk _ =>
    try simp [Stmt.pushOrigins] at source
    cases lc with
    | none => simp only [lowerStmt]; exact OriginRun.pure _
    | some l =>
      simp only [lowerStmt]
      exact OriginRun.bind (origins_leaveTo _) fun _ => origins_emitTerm _
  | cont _ =>
    try simp [Stmt.pushOrigins] at source
    cases lc with
    | none => simp only [lowerStmt]; exact OriginRun.pure _
    | some l =>
      cases hk : l.cont with
      | jump h =>
        simp only [lowerStmt, hk]
        exact OriginRun.bind (origins_leaveTo _) fun _ => origins_emitTerm _
      | next h t i =>
        simp only [lowerStmt, hk]
        exact OriginRun.bind (origins_leaveTo _) fun _ => OriginRun.bind (origins_emitDef _) fun _ => origins_emitTerm _
  | print args org =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    exact OriginRun.bind (origins_lowerPrintArgs args) fun _ => origins_emitEffect _
  | assertS e org =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    exact OriginRun.bind (origins_lowerExpr e) fun cv => origins_assert_core cv org
  | abort _ org =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    exact origins_emitTerm _
  | exit e org =>
    try simp [Stmt.pushOrigins] at source
    simp only [lowerStmt]
    exact OriginRun.bind (origins_lowerExpr e) fun _ => origins_emitTerm _

end


theorem origins_finishFunction (impl : Impl) (value : ValueId) :
    OriginRun (finishFunction impl value) := by
  unfold finishFunction
  refine OriginRun.bind origins_read fun le =>
    OriginRun.bind origins_isLive fun live => ?_
  cases live
  · exact OriginRun.pure _
  · by_cases sink : (!impl.results.isEmpty && impl.body.value.isNone &&
        impl.body.diverges le.mod.noReturn) = true
    · simp only [sink, ↓reduceIte]
      exact OriginRun.bind (origins_newBlock _) fun ⟨_, _⟩ =>
        OriginRun.bind (origins_emitTerm _) fun _ =>
        OriginRun.bind (origins_setCur _) fun _ => origins_emitTerm _
    · simp only [sink, ↓reduceIte]
      exact origins_emitTerm _

def Func.PresentOrigins (func : Func) : Prop :=
  ∀ block ∈ func.blocks.toList, ∀ inst ∈ block.insts, Inst.OriginPresent inst

theorem origins_finishBlocks {state : LS} (checked : PresentOrigins state) :
    ∀ block ∈ (finishBlocks state.blocks).toList, ∀ inst ∈ block.insts, Inst.OriginPresent inst := by
  intro block blockMember inst instructionMember
  simp only [finishBlocks, Array.toList_map, List.mem_map] at blockMember
  obtain ⟨original, originalMember, rfl⟩ := blockMember
  exact checked inst (List.mem_flatMap.mpr ⟨original, originalMember, instructionMember⟩)

theorem origins_initState : PresentOrigins initState := by
  simp [PresentOrigins, initState, LS.insts]

theorem lowerImpl_presentOrigins (module : Core.Module) (impl : Impl)
    (source : PushOrigins.Present impl.body.pushOrigins) :
    Func.PresentOrigins (lowerImpl module impl) := by
  let action : B Unit := do
    let (b0, params) ← newBlock (impl.params.toList.map fun param => .data (tyOfVar impl param.var))
    setCur (some b0)
    let pre := (impl.params.toList.zip params).map fun (param, value) =>
      (param.var, value, (impl.vars[param.var]?.map (·.org)).getD 0)
    let value ← lowerBlock none pre false impl.body
    finishFunction impl value
  have preservation : OriginRun action := by
    exact OriginRun.bind (origins_newBlock _) fun ⟨_, _⟩ =>
      OriginRun.bind (origins_setCur _) fun _ =>
      OriginRun.bind (origins_lowerBlock _ _ _ _) fun _ => origins_finishFunction _ _
  let output := action (lowerEnv module impl.vars impl.results.toList) initState
  have checked := preservation (lowerEnv module impl.vars impl.results.toList) initState output.1 output.2 rfl origins_initState
  exact origins_finishBlocks checked

theorem lowerGlobal_presentOrigins (module : Core.Module) (global : Core.Global)
    (source : PushOrigins.Present global.init.pushOrigins) :
    Func.PresentOrigins (lowerGlobal module global).init := by
  let action : B Unit := do
    let (b0, _) ← newBlock []
    setCur (some b0)
    let value ← lowerExpr global.init
    emitTerm (.ret [value] (some global.org))
  have preservation : OriginRun action := by
    exact OriginRun.bind (origins_newBlock _) fun ⟨_, _⟩ =>
      OriginRun.bind (origins_setCur _) fun _ =>
      OriginRun.bind (origins_lowerExpr _) fun _ => origins_emitTerm _
  let output := action (lowerEnv module #[] [global.ty]) initState
  have checked := preservation (lowerEnv module #[] [global.ty]) initState output.1 output.2 rfl origins_initState
  exact origins_finishBlocks checked



theorem lower_presentOrigins (module : Core.Module)
    (implementations : ∀ impl ∈ module.impls.toList, PushOrigins.Present impl.body.pushOrigins)
    (initializers : ∀ global ∈ module.globals.toList, PushOrigins.Present global.init.pushOrigins)
    (func : Func)
    (member : func ∈ (lower module).funcs.toList ++ (lower module).globals.toList.map (·.init)) :
    Func.PresentOrigins func := by
  rcases List.mem_append.mp member with implementation | initializer
  · simp only [lower, Array.toList_map, List.mem_map] at implementation
    obtain ⟨ctx, _, equality⟩ := implementation
    rw [Array.getElem?_map] at equality
    cases source : module.impls[ctx.impl]? with
    | none =>
      simp only [source, Option.map_none] at equality
      subst func
      simp [Func.PresentOrigins, invalidContextFunction]
    | some impl =>
      simp only [source, Option.map_some] at equality
      subst func
      exact lowerImpl_presentOrigins module impl
        (implementations impl (Array.mem_toList_iff.mpr (Array.mem_of_getElem? source)))
  · obtain ⟨global, globalMember, rfl⟩ := List.mem_map.mp initializer
    change global ∈ (module.globals.map (lowerGlobal module)).toList at globalMember
    simp only [Array.toList_map, List.mem_map] at globalMember
    obtain ⟨source, sourceMember, rfl⟩ := globalMember
    exact lowerGlobal_presentOrigins _ _ (initializers source sourceMember)

theorem Func.checkOrigins_shrink {func : Func} (present : Func.PresentOrigins func)
    (label : String) : checkOrigins .shrink label func = .ok () := by
  apply Origins.checkAll_ok_of_forall
  intro block blockMember
  apply Origins.checkAll_ok_of_forall
  intro inst instMember
  have required := present block blockMember inst instMember
  unfold checkOrigin
  cases needed : inst.needsOriginIn .shrink with
  | false => rfl
  | true =>
    have hasOrigin := required needed
    cases origin : inst.origin with
    | none => simp [origin] at hasOrigin
    | some value => simp [pure, Except.pure]

theorem lower_checkOrigins_shrink (module : Core.Module)
    (implementations : ∀ impl ∈ module.impls.toList, PushOrigins.Present impl.body.pushOrigins)
    (initializers : ∀ global ∈ module.globals.toList, PushOrigins.Present global.init.pushOrigins) :
    (checkAll (lower module).infos fun info => checkOrigins .shrink info.label info.f) = .ok () := by
  apply Origins.checkAll_ok_of_forall
  intro info member
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
  exact Func.checkOrigins_shrink (lower_presentOrigins module implementations initializers func functionMember) label

end Goose.Lower.Validation.ShrinkOrigins
