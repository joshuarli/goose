import Goose.Lower.Validation.Typing

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def TypePrefix (before after : LS) : Prop :=
  ∀ (value : ValueId) (ty : VTy), before.vals[value]? = some (some ty) → after.vals[value]? = some (some ty)

theorem TypePrefix.refl (state : LS) : TypePrefix state state := fun _ _ typed => typed

theorem TypePrefix.trans {before mid after : LS}
    (first : TypePrefix before mid) (second : TypePrefix mid after) :
    TypePrefix before after := fun value ty typed => second value ty (first value ty typed)

def TypeRun (action : B α) : Prop :=
  ∀ le before result after, action le before = (result, after) → TypePrefix before after

theorem TypeRun.pure (value : α) : TypeRun (pure value) := by
  intro le before result after run
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact .refl before

theorem TypeRun.bind {action : B α} {next : α → B β}
    (first : TypeRun action) (second : ∀ value, TypeRun (next value)) :
    TypeRun (action >>= next) := by
  intro le before result after run
  obtain ⟨value, mid, firstRun, secondRun⟩ := bind_eq.mp run
  exact (first _ _ _ _ firstRun).trans (second value _ _ _ _ secondRun)

theorem TypeRun.of_unchanged {action : B α}
    (unchanged : ∀ le state, (action le state).2.vals = state.vals) : TypeRun action := by
  intro le before result after run value ty typed
  have equality := unchanged le before
  rw [run] at equality
  rw [equality]
  exact typed

theorem types_recordValueRootRecipe (value : ValueId) (sourceScope : ScopeId) :
    TypeRun (recordValueRootRecipe value sourceScope) := by
  apply TypeRun.of_unchanged
  intro le state
  rw [recordValueRootRecipe_run]

theorem types_recordReadValueRootRecipe (value : ValueId) (place : Place) :
    TypeRun (recordReadValueRootRecipe value place) := by
  apply TypeRun.of_unchanged
  intro le state
  cases place <;>
    simp [recordReadValueRootRecipe_run, recordValueRootSource_run] <;>
    (try split) <;> rfl

theorem types_emitDef (op : Op) : TypeRun (emitDef op) := by
  intro le before result after run value ty typed
  cases current : before.cur with
  | none =>
    rw [emitDef_none op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact typed
  | some block =>
    rw [emitDef_run op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    have bound : value < before.vals.size := (Array.getElem?_eq_some_iff.mp typed).1
    simp [Array.getElem?_push, Nat.ne_of_lt bound, typed]

theorem types_newBlock (types : List VTy) : TypeRun (newBlock types) := by
  intro le before result after run value ty typed
  rw [newBlock_run_general] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  have bound : value < before.vals.size := (Array.getElem?_eq_some_iff.mp typed).1
  exact (pushParamTypes_preserves_lookup _ _ _ bound).trans typed

theorem types_emitEffect (effect : Effect) : TypeRun (emitEffect effect) := by
  apply TypeRun.of_unchanged
  intro le state
  cases current : state.cur <;>
    simp [emitEffect, curBlock, current, bind_run, pure_run, pushInst,
      modify, modifyGet, MonadStateOf.modifyGet]

theorem types_setCur (block : Option BlockId) : TypeRun (setCur block) := by
  apply TypeRun.of_unchanged
  intro le state
  rw [setCur_run]

theorem types_emitTerm (term : Term) : TypeRun (emitTerm term) := by
  apply TypeRun.of_unchanged
  intro le state
  cases current : state.cur with
  | none => rw [emitTerm_none term le current]
  | some block => rw [emitTerm_run term le current]

theorem types_patchTerm (block : BlockId) (term : Term) : TypeRun (patchTerm block term) := by
  apply TypeRun.of_unchanged
  intro le state
  rw [patchTerm_run]

theorem types_curBlock : TypeRun curBlock := by
  apply TypeRun.of_unchanged
  intro le state
  rw [curBlock_run]

theorem types_get : TypeRun (get : B LS) := by
  apply TypeRun.of_unchanged
  intros
  rfl

theorem types_read : TypeRun (read : B LEnv) := by
  apply TypeRun.of_unchanged
  intros
  rfl

theorem types_valTy (value : ValueId) : TypeRun (valTy value) := by
  apply TypeRun.of_unchanged
  intro le state
  rw [valTy_run]

theorem types_pushScope (scope : ScopeId) : TypeRun (pushScope scope) := by
  apply TypeRun.of_unchanged
  intro le state
  rw [pushScope_run]

theorem types_popScope : TypeRun popScope := by
  apply TypeRun.of_unchanged
  intro le state
  rw [popScope_run]

theorem types_inScope (scope : ScopeId) {action : B α} (typed : TypeRun action) :
    TypeRun (inScope scope action) := by
  unfold inScope
  exact TypeRun.bind (types_pushScope _) fun _ =>
    TypeRun.bind typed fun _ => TypeRun.bind types_popScope fun _ => TypeRun.pure _

theorem types_whenLive (default : α) {action : BlockId → B α}
    (typed : ∀ block, TypeRun (action block)) : TypeRun (whenLive default action) := by
  unfold whenLive
  refine TypeRun.bind types_curBlock fun current => ?_
  cases current
  · exact TypeRun.pure _
  · exact typed _

theorem types_intTyOf (v : ValueId) : TypeRun (intTyOf v) := by
  unfold intTyOf
  refine TypeRun.bind (types_valTy v) fun t => ?_
  cases t with
  | data t => cases t <;> exact TypeRun.pure _
  | view _ _ => exact TypeRun.pure _

theorem types_freezeTo (m : Mutability) (r : ValueId) : TypeRun (freezeTo m r) := by
  unfold freezeTo
  refine TypeRun.bind (types_valTy r) fun t => ?_
  cases m <;> cases t <;> first
    | exact TypeRun.pure _
    | (rename_i t; cases t <;> first | exact TypeRun.pure _ | (rename_i m' _; cases m' <;> first | exact TypeRun.pure _ | exact types_emitDef _))

theorem types_borrowTo (m : Mutability) (r : ValueId) : TypeRun (borrowTo m r) := by
  intro le before result after run
  rcases borrowTo_cases run with frozen | borrowed
  · exact types_freezeTo m r le before result after frozen
  · exact types_emitDef _ le before result after borrowed

theorem types_coerceTo (target : Ty) (r : ValueId) (org : OriginId) : TypeRun (coerceTo target r org) := by
  unfold coerceTo
  refine TypeRun.bind (types_valTy r) fun source => ?_
  split
  · exact types_emitDef _
  · exact TypeRun.bind (types_emitDef _) (fun _ => types_emitDef _)
  · exact TypeRun.pure _

theorem types_coerceSlot (slot : SlotId) (value : ValueId) (org : OriginId) :
    TypeRun (coerceSlot slot value org) := by
  unfold coerceSlot
  refine TypeRun.bind types_read fun le => ?_
  cases le.slots[slot]? with
  | none => exact TypeRun.pure _
  | some destination => exact types_coerceTo destination.ty value org

theorem types_coerceResult (value : ValueId) (org : OriginId) :
    TypeRun (coerceResult value org) := by
  unfold coerceResult
  refine TypeRun.bind types_read fun le => ?_
  cases le.results.head? with
  | none => exact TypeRun.pure _
  | some destination => exact types_coerceTo destination value org

theorem types_growOwner (r : ValueId) : TypeRun (growOwner r) := by
  unfold growOwner
  refine TypeRun.bind (types_valTy r) fun t => ?_
  cases t with
  | data t => cases t <;> first | exact TypeRun.pure _ | (rename_i m' t'; cases t' <;> exact TypeRun.pure _)
  | view _ _ => exact TypeRun.pure _

theorem types_leaveAll : ∀ scs, TypeRun (leaveAll scs)
  | [] => TypeRun.pure _
  | sc :: rest => by
    unfold leaveAll
    exact TypeRun.bind (types_emitEffect _) fun _ => types_leaveAll rest

theorem types_leaveTo (d : Nat) : TypeRun (leaveTo d) := by
  unfold leaveTo
  exact TypeRun.bind types_get fun _ => types_leaveAll _

theorem types_initSlots : ∀ ps, TypeRun (initSlots ps)
  | [] => TypeRun.pure _
  | (s, v, o) :: rest => by
    unfold initSlots
    exact TypeRun.bind (types_emitEffect _) fun _ => types_initSlots rest

theorem types_isLive : TypeRun isLive := by
  unfold isLive
  exact TypeRun.bind types_curBlock fun _ => TypeRun.pure _

theorem types_eachElemValue (x : VarId) (byRef : Bool) (elem : ValueId) :
    TypeRun (eachElemValue x byRef elem) := by
  unfold eachElemValue
  cases byRef
  · exact types_emitDef _
  · refine TypeRun.bind types_read fun le => ?_
    cases le.vars[x]? with
    | none => exact TypeRun.pure _
    | some lv =>
      dsimp only
      cases lv.ty with
      | ref m t => exact types_borrowTo m elem
      | _ => exact TypeRun.pure _

theorem types_regrowOf (o : Option ValueId) : TypeRun (regrowOf o) := by
  cases o with
  | none => exact TypeRun.pure _
  | some r => exact types_growOwner r

theorem types_eachSampled (regrow : Bool) (vw : ValueId) : TypeRun (eachSampled regrow vw) := by
  unfold eachSampled
  cases regrow
  · exact types_emitDef _
  · exact TypeRun.pure _

theorem types_eachLen (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    TypeRun (eachLen regrow owner sampled) := by
  unfold eachLen
  cases regrow
  · exact TypeRun.pure _
  · exact types_emitDef _

theorem types_fork (condition : ValueId) : TypeRun (fork condition) := by
  unfold fork
  exact TypeRun.bind (types_newBlock _) fun ⟨thenBlock, _⟩ =>
    TypeRun.bind (types_newBlock _) fun ⟨elseBlock, _⟩ =>
    TypeRun.bind (types_emitTerm _) fun _ => TypeRun.pure _

theorem types_patchBrs (target : BlockId) : ∀ incoming, TypeRun (patchBrs target incoming)
  | [] => TypeRun.pure _
  | (block, value) :: rest => by
    unfold patchBrs
    exact TypeRun.bind (types_patchTerm _ _) fun _ => types_patchBrs target rest

theorem types_patchBrs0 (target : BlockId) : ∀ incoming, TypeRun (patchBrs0 target incoming)
  | [] => TypeRun.pure _
  | block :: rest => by
    unfold patchBrs0
    exact TypeRun.bind (types_patchTerm _ _) fun _ => types_patchBrs0 target rest

theorem types_joinValue (endT : Option BlockId) (vt : ValueId) (endF : Option BlockId) (vf : ValueId) :
    TypeRun (joinValue endT vt endF vf) := by
  unfold joinValue
  cases endT <;> cases endF
  · exact TypeRun.bind (types_setCur _) fun _ => TypeRun.pure _
  all_goals
    exact TypeRun.bind (types_valTy _) fun _ =>
      TypeRun.bind (types_newBlock _) fun ⟨_, _⟩ =>
      TypeRun.bind (types_patchBrs _ _) fun _ =>
      TypeRun.bind (types_setCur _) fun _ => TypeRun.pure _

theorem types_joinArms (endT endF : Option BlockId) : TypeRun (joinArms endT endF) := by
  unfold joinArms
  cases endT <;> cases endF
  · exact types_setCur _
  all_goals
    exact TypeRun.bind (types_newBlock _) fun ⟨_, _⟩ =>
      TypeRun.bind (types_patchBrs0 _ _) fun _ => types_setCur _

theorem types_scFork (isAnd : Bool) (value : ValueId) : TypeRun (scFork isAnd value) := by
  unfold scFork
  refine TypeRun.bind (types_newBlock _) fun ⟨_, _⟩ =>
    TypeRun.bind (types_newBlock _) fun ⟨_, _⟩ => ?_
  cases isAnd <;> exact TypeRun.bind (types_emitTerm _) fun _ => TypeRun.pure _

theorem types_shortCircuit (isAnd : Bool) (value : ValueId) {rhs : B ValueId}
    (typed : TypeRun rhs) : TypeRun (shortCircuit isAnd value rhs) := by
  unfold shortCircuit
  exact types_whenLive _ fun _ =>
    TypeRun.bind (types_scFork _ _) fun ⟨_, _, _⟩ =>
    TypeRun.bind (types_setCur _) fun _ => TypeRun.bind typed fun _ =>
    TypeRun.bind (types_emitTerm _) fun _ =>
    TypeRun.bind (types_setCur _) fun _ => TypeRun.pure _

theorem types_loopBody (cv : ValueId) {body : Nat → BlockId → B ValueId} {back : B Unit}
    (hbody : ∀ depth exitBlock, TypeRun (body depth exitBlock)) (hback : TypeRun back) :
    TypeRun (loopBody cv body back) := by
  unfold loopBody
  exact TypeRun.bind types_get fun _ =>
    TypeRun.bind (types_fork _) fun ⟨_, _⟩ =>
    TypeRun.bind (types_setCur _) fun _ => TypeRun.bind (hbody _ _) fun _ =>
    TypeRun.bind hback fun _ => types_setCur _

theorem types_rangeBack (t : IntTy) (i : ValueId) (hb : BlockId) : TypeRun (rangeBack t i hb) := by
  unfold rangeBack
  refine TypeRun.bind types_isLive fun live => ?_
  cases live
  · exact TypeRun.pure _
  · exact TypeRun.bind (types_emitDef _) fun _ => types_emitTerm _


theorem types_lowerWhile (hb : BlockId) {cond : B ValueId} {body : Nat → BlockId → B ValueId}
    (hc : TypeRun cond) (hbody : ∀ d xb, TypeRun (body d xb)) : TypeRun (lowerWhile hb cond body) := by
  unfold lowerWhile
  exact TypeRun.bind hc fun cv => types_whenLive _ fun _ =>
    types_loopBody cv hbody (types_emitTerm _)

theorem types_lowerRange (t : IntTy) (i b : ValueId) (hb : BlockId) {body : Nat → BlockId → B ValueId}
    (hbody : ∀ d xb, TypeRun (body d xb)) : TypeRun (lowerRange t i b hb body) := by
  unfold lowerRange
  exact TypeRun.bind (types_emitDef _) fun c => types_loopBody c hbody (types_rangeBack _ _ _)

theorem types_lowerEach (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (hb : BlockId)
    (i : ValueId) {body : Nat → BlockId → B ValueId} (hbody : ∀ d xb, TypeRun (body d xb)) :
    TypeRun (lowerEach regrow owner sampled hb i body) := by
  unfold lowerEach
  exact TypeRun.bind (types_eachLen _ _ _) fun n => TypeRun.bind (types_emitDef _) fun c =>
    types_loopBody c hbody (types_rangeBack _ _ _)

theorem types_ifE_core (cv : ValueId) (sourceScope : ScopeId) {a1 a2 : B ValueId} (h1 : TypeRun a1) (h2 : TypeRun a2) :
    TypeRun (whenLive 0 fun _ => do
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
  exact types_whenLive _ fun _ =>
    TypeRun.bind (types_fork _) fun ⟨_, _⟩ =>
    TypeRun.bind (types_setCur _) fun _ => TypeRun.bind h1 fun _ =>
    TypeRun.bind types_curBlock fun _ => TypeRun.bind (types_setCur _) fun _ =>
    TypeRun.bind h2 fun _ => TypeRun.bind types_curBlock fun _ =>
    TypeRun.bind (types_joinValue _ _ _ _) fun result =>
    TypeRun.bind (types_recordValueRootRecipe result sourceScope) fun _ => TypeRun.pure result

theorem types_ifS_some_core (cv : ValueId) {a1 a2 : B ValueId} (h1 : TypeRun a1) (h2 : TypeRun a2) :
    TypeRun (whenLive () fun _ => do
      let (tb, eb) ← fork cv
      setCur (some tb)
      let _ ← a1
      let endT ← curBlock
      setCur (some eb)
      let _ ← a2
      let endF ← curBlock
      joinArms endT endF) := by
  exact types_whenLive _ fun _ =>
    TypeRun.bind (types_fork _) fun ⟨_, _⟩ =>
    TypeRun.bind (types_setCur _) fun _ => TypeRun.bind h1 fun _ =>
    TypeRun.bind types_curBlock fun _ => TypeRun.bind (types_setCur _) fun _ =>
    TypeRun.bind h2 fun _ => TypeRun.bind types_curBlock fun _ => types_joinArms _ _

theorem types_ifS_none_core (cv : ValueId) {a1 : B ValueId} (h1 : TypeRun a1) :
    TypeRun (whenLive () fun _ => do
      let (tb, jb) ← fork cv
      setCur (some tb)
      let _ ← a1
      emitTerm (.br jb [])
      setCur (some jb)) := by
  exact types_whenLive _ fun _ =>
    TypeRun.bind (types_fork _) fun ⟨_, _⟩ =>
    TypeRun.bind (types_setCur _) fun _ => TypeRun.bind h1 fun _ =>
    TypeRun.bind (types_emitTerm _) fun _ => types_setCur _

theorem types_assert_core (cv : ValueId) (org : OriginId) :
    TypeRun (whenLive () fun _ => do
      let (pb, fb) ← fork cv
      setCur (some fb)
      emitTerm (.abort .assert (some org))
      setCur (some pb)) := by
  exact types_whenLive _ fun _ =>
    TypeRun.bind (types_fork _) fun ⟨_, _⟩ =>
    TypeRun.bind (types_setCur _) fun _ => TypeRun.bind (types_emitTerm _) fun _ => types_setCur _

theorem types_header0 {tail : BlockId → B Unit} (ht : ∀ h, TypeRun (tail h)) :
    TypeRun (do
      let (hb, _) ← newBlock []
      emitTerm (.br hb [])
      setCur (some hb)
      tail hb) := by
  exact TypeRun.bind (types_newBlock _) fun ⟨_, _⟩ =>
    TypeRun.bind (types_emitTerm _) fun _ => TypeRun.bind (types_setCur _) fun _ => ht _

theorem types_header1 (ty : VTy) (a : ValueId) {tail : BlockId → ValueId → B Unit}
    (ht : ∀ h i, TypeRun (tail h i)) :
    TypeRun (do
      let (hb, hs) ← newBlock [ty]
      let i := hs.headD 0
      emitTerm (.br hb [a])
      setCur (some hb)
      tail hb i) := by
  exact TypeRun.bind (types_newBlock _) fun ⟨_, _⟩ =>
    TypeRun.bind (types_emitTerm _) fun _ => TypeRun.bind (types_setCur _) fun _ => ht _ _

mutual

theorem types_lowerExpr : ∀ e : Expr, TypeRun (lowerExpr e)
  | .structLit t es => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerExprs es) fun _ => types_emitDef _
  | .lit t n => by simp only [lowerExpr]; exact types_emitDef _
  | .bool b => by simp only [lowerExpr]; exact types_emitDef _
  | .read p => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerPlace p) fun _ =>
      TypeRun.bind (types_emitDef _) fun value =>
        TypeRun.bind (types_recordReadValueRootRecipe value p) fun _ => TypeRun.pure value
  | .ref m p => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerPlace p) fun r => types_borrowTo m r
  | .slice m v lo hi org => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerView v) fun _ => TypeRun.bind (types_lowerBound lo) fun _ =>
      TypeRun.bind (types_lowerBound hi) fun _ => types_emitDef _
  | .len v => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerView v) fun _ => types_emitDef _
  | .un op e org => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerExpr e) fun a => TypeRun.bind (types_intTyOf a) fun _ => types_emitDef _
  | .bin op a b org => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerExpr a) fun x => TypeRun.bind (types_lowerExpr b) fun y =>
      TypeRun.bind (types_intTyOf x) fun _ => types_emitDef _
  | .cmp op a b => by
    simp only [lowerExpr]
    refine TypeRun.bind (types_lowerExpr a) fun x => TypeRun.bind (types_lowerExpr b) fun y =>
      TypeRun.bind (types_valTy x) fun t => ?_
    cases t with
    | data t => cases t <;> exact types_emitDef _
    | view _ _ => exact types_emitDef _
  | .and a b => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerExpr a) fun x => types_shortCircuit true x (types_lowerExpr b)
  | .or a b => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerExpr a) fun x => types_shortCircuit false x (types_lowerExpr b)
  | .not e => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerExpr e) fun _ => types_emitDef _
  | .conv k target e org => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerExpr e) fun a => TypeRun.bind (types_intTyOf a) fun _ => types_emitDef _
  | .call c args org => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerArgs args) fun _ =>
      TypeRun.bind (types_emitDef _) fun r => TypeRun.bind types_read fun le => by
        cases le.mod.noReturn c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          first | exact TypeRun.pure _ | exact TypeRun.bind (types_emitTerm _) fun _ => TypeRun.pure _
  | .push owner e org => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerPlace owner) fun r => TypeRun.bind (types_lowerExpr e) fun v =>
      types_emitDef (.push r v org)
  | .pop owner org => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerPlace owner) fun _ => types_emitDef _
  | .ifE c t f => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerExpr c) fun cv =>
      types_ifE_core cv (sourceBlockScope t) (types_lowerBlock none [] true t) (types_lowerBlock none [] true f)
  | .blockE b => by
    simp only [lowerExpr]
    exact types_lowerBlock none [] true b
  | .arrLit t es => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerExprs es) fun _ => types_emitDef _
  | .fill t e => by
    simp only [lowerExpr]
    exact TypeRun.bind (types_lowerExpr e) fun _ => types_emitDef _

theorem types_lowerExprs : ∀ es : List Expr, TypeRun (lowerExprs es)
  | [] => by simp only [lowerExprs]; exact TypeRun.pure _
  | e :: rest => by
    simp only [lowerExprs]
    exact TypeRun.bind (types_lowerExpr e) fun _ => TypeRun.bind (types_lowerExprs rest) fun _ => TypeRun.pure _

theorem types_lowerArg : ∀ a : Arg, TypeRun (lowerArg a)
  | .byVal e => by simp only [lowerArg]; exact types_lowerExpr e
  | .byRef m p => by
    simp only [lowerArg]
    exact TypeRun.bind (types_lowerPlace p) fun r => types_borrowTo m r

theorem types_lowerArgs : ∀ as : List Arg, TypeRun (lowerArgs as)
  | [] => by simp only [lowerArgs]; exact TypeRun.pure _
  | a :: rest => by
    simp only [lowerArgs]
    exact TypeRun.bind (types_lowerArg a) fun _ => TypeRun.bind (types_lowerArgs rest) fun _ => TypeRun.pure _

theorem types_lowerPlace : ∀ p : Place, TypeRun (lowerPlace p)
  | .field owner i => by
    simp only [lowerPlace]
    exact TypeRun.bind (types_lowerPlace owner) fun _ => types_emitDef _
  | .var x => by simp only [lowerPlace]; exact types_emitDef _
  | .global g => by simp only [lowerPlace]; exact types_emitDef _
  | .deref e => by simp only [lowerPlace]; exact types_lowerExpr e
  | .elem v i org => by
    simp only [lowerPlace]
    exact TypeRun.bind (types_lowerView v) fun _ => TypeRun.bind (types_lowerExpr i) fun _ => types_emitDef _

theorem types_lowerView : ∀ v : View, TypeRun (lowerView v)
  | .of p => by
    simp only [lowerView]
    exact TypeRun.bind (types_lowerPlace p) fun _ => types_emitDef _
  | .val e => by
    simp only [lowerView]
    exact TypeRun.bind (types_lowerExpr e) fun _ => types_emitDef _

theorem types_lowerBound : ∀ b : Bound, TypeRun (lowerBound b)
  | .omitted => by simp only [lowerBound]; exact TypeRun.pure _
  | .expr e => by
    simp only [lowerBound]
    exact TypeRun.bind (types_lowerExpr e) fun _ => TypeRun.pure _
  | .fromEnd e => by
    simp only [lowerBound]
    exact TypeRun.bind (types_lowerExpr e) fun _ => TypeRun.pure _

theorem types_lowerEachSource : ∀ v : View, TypeRun (lowerEachSource v)
  | .of p => by
    simp only [lowerEachSource]
    exact TypeRun.bind (types_lowerPlace p) fun _ => TypeRun.bind (types_emitDef _) fun _ => TypeRun.pure _
  | .val e => by
    simp only [lowerEachSource]
    exact TypeRun.bind (types_lowerExpr e) fun _ => TypeRun.bind (types_emitDef _) fun _ => TypeRun.pure _

theorem types_lowerBlockValue (want : Bool) : ∀ v : Option Expr, TypeRun (lowerBlockValue want v)
  | some e => by simp only [lowerBlockValue]; exact types_lowerExpr e
  | none => by
    cases want
    · simp only [lowerBlockValue, Bool.false_eq_true, ↓reduceIte]; exact TypeRun.pure _
    · simp only [lowerBlockValue, ↓reduceIte]; exact types_emitDef _

theorem types_lowerBlock (lc : Option LoopCtx) (pre : List (SlotId × ValueId × OriginId)) (want : Bool) :
    ∀ b : Core.Block, TypeRun (lowerBlock lc pre want b)
  | .mk sc stmts value => by
    simp only [lowerBlock]
    exact TypeRun.bind (types_emitEffect _) fun _ => types_inScope sc
      (TypeRun.bind (types_initSlots _) fun _ => TypeRun.bind (types_lowerStmts lc stmts) fun _ =>
        TypeRun.bind (types_lowerBlockValue want value) fun _ => TypeRun.bind (types_emitEffect _) fun _ =>
        TypeRun.pure _)

theorem types_lowerStmts (lc : Option LoopCtx) : ∀ ss : List Stmt, TypeRun (lowerStmts lc ss)
  | [] => by simp only [lowerStmts]; exact TypeRun.pure _
  | s :: rest => by
    simp only [lowerStmts]
    refine TypeRun.bind types_isLive fun live => ?_
    cases live
    · exact TypeRun.pure _
    · exact TypeRun.bind (types_lowerStmt lc s) fun _ => types_lowerStmts lc rest

theorem types_lowerPrintArgs : ∀ as : List PrintArg, TypeRun (lowerPrintArgs as)
  | [] => by simp only [lowerPrintArgs]; exact TypeRun.pure _
  | .text s :: rest => by
    simp only [lowerPrintArgs]
    exact TypeRun.bind (types_lowerPrintArgs rest) fun _ => TypeRun.pure _
  | .expr e :: rest => by
    simp only [lowerPrintArgs]
    exact TypeRun.bind (types_lowerExpr e) fun _ => TypeRun.bind (types_lowerPrintArgs rest) fun _ => TypeRun.pure _

theorem types_lowerStmt (lc : Option LoopCtx) : ∀ s : Stmt, TypeRun (lowerStmt lc s)
  | .letS x e org => by
    simp only [lowerStmt]
    exact TypeRun.bind (types_lowerExpr e) fun value =>
      TypeRun.bind (types_coerceSlot x value org) fun _ => types_emitEffect _
  | .assign p e org => by
    simp only [lowerStmt]
    exact TypeRun.bind (types_lowerPlace p) fun _ => TypeRun.bind (types_lowerExpr e) fun _ => types_emitEffect _
  | .assignOp op p e org => by
    simp only [lowerStmt]
    exact TypeRun.bind (types_lowerPlace p) fun _ => TypeRun.bind (types_emitDef _) fun _ =>
      TypeRun.bind (types_lowerExpr e) fun _ => TypeRun.bind (types_intTyOf _) fun _ =>
      TypeRun.bind (types_emitDef _) fun _ => types_emitEffect _
  | .rebind x e org => by
    simp only [lowerStmt]
    exact TypeRun.bind (types_lowerExpr e) fun value =>
      TypeRun.bind (types_coerceSlot x value org) fun _ =>
        TypeRun.bind (types_emitDef _) fun _ => types_emitEffect _
  | .expr e _ => by
    simp only [lowerStmt]
    exact TypeRun.bind (types_lowerExpr e) fun _ => TypeRun.pure _
  | .append owner src org => by
    simp only [lowerStmt]
    exact TypeRun.bind (types_lowerPlace owner) fun _ => TypeRun.bind (types_lowerView src) fun _ =>
      types_emitEffect _
  | .popN owner count org => by
    simp only [lowerStmt]
    exact TypeRun.bind (types_lowerPlace owner) fun r => TypeRun.bind (types_lowerExpr count) fun n =>
      types_emitEffect (.popN r n (some org))
  | .resize owner size none org => by
    simp only [lowerStmt]
    exact TypeRun.bind (types_lowerPlace owner) fun r => TypeRun.bind (types_lowerExpr size) fun n =>
      TypeRun.bind (TypeRun.pure _) fun fill => types_emitEffect (.resize r n fill (some org))
  | .resize owner size (some fill) org => by
    simp only [lowerStmt]
    exact TypeRun.bind (types_lowerPlace owner) fun r => TypeRun.bind (types_lowerExpr size) fun n =>
      TypeRun.bind (types_lowerExpr fill) fun v =>
        types_emitEffect (.resize r n (some v) (some org))
  | .clear owner org => by
    simp only [lowerStmt]
    exact TypeRun.bind (types_lowerPlace owner) fun r => types_emitEffect (.clear r (some org))
  | .assignWhole owner replacement org => by
    simp only [lowerStmt]
    exact TypeRun.bind (types_lowerPlace owner) fun r =>
      TypeRun.bind (types_emitEffect (.clear r (some org))) fun _ =>
      TypeRun.bind (types_lowerExpr replacement) fun run =>
        types_emitEffect (.replace r run (some org))
  | .ifS c t f _ => by
    cases f with
    | none =>
      simp only [lowerStmt]
      exact TypeRun.bind (types_lowerExpr c) fun cv => types_ifS_none_core cv (types_lowerBlock lc [] false t)
    | some fb =>
      simp only [lowerStmt]
      exact TypeRun.bind (types_lowerExpr c) fun cv =>
        types_ifS_some_core cv (types_lowerBlock lc [] false t) (types_lowerBlock lc [] false fb)
  | .while c body _ => by
    simp only [lowerStmt]
    exact types_header0 (tail := fun hb => lowerWhile hb (lowerExpr c)
        (fun d xb => lowerBlock (some ⟨d, xb, .jump hb⟩) [] false body))
      (fun hb => types_lowerWhile hb (types_lowerExpr c) (fun d xb => types_lowerBlock _ _ _ body))
  | .forRange x lo hi body org => by
    simp only [lowerStmt]
    refine TypeRun.bind (types_lowerExpr lo) fun a => TypeRun.bind (types_lowerExpr hi) fun b =>
      types_whenLive _ fun _ => TypeRun.bind (types_intTyOf a) fun t => ?_
    exact types_header1 (.data (.int t)) a (tail := fun hb i => lowerRange t i b hb (fun d xb =>
        lowerBlock (some ⟨d, xb, .next hb t i⟩) [(x, i, org)] false body))
      (fun hb i => types_lowerRange t i b hb (fun d xb => types_lowerBlock _ _ _ body))
  | .forEach x idx v byRef body org => by
    simp only [lowerStmt]
    refine TypeRun.bind (types_lowerEachSource v) fun ov => TypeRun.bind (types_regrowOf _) fun regrow =>
      TypeRun.bind (types_eachSampled _ _) fun sampled => TypeRun.bind (types_emitDef _) fun startAt =>
      types_whenLive _ fun _ => ?_
    exact types_header1 (.data (.int .i64)) startAt (tail := fun hb i =>
        lowerEach regrow ov.1 sampled hb i (fun d xb => do
          let elem ← emitDef (.refElem ov.2 i)
          let ev ← eachElemValue x byRef elem
          let pre := (x, ev, org) :: (match idx with
            | some j => [(j, i, org)]
            | none => [])
          lowerBlock (some ⟨d, xb, .next hb .i64 i⟩) pre false body))
      (fun hb i => types_lowerEach regrow ov.1 sampled hb i (fun d xb =>
        TypeRun.bind (types_emitDef _) fun elem => TypeRun.bind (types_eachElemValue _ _ _) fun ev =>
          types_lowerBlock _ _ _ body))
  | .ret e org => by
    cases e with
    | some e =>
      simp only [lowerStmt]
      exact TypeRun.bind (types_lowerExpr e) fun value =>
        TypeRun.bind (types_coerceResult value org) fun _ =>
          TypeRun.bind (TypeRun.pure _) fun _ =>
            TypeRun.bind (types_leaveTo 0) fun _ => types_emitTerm _
    | none =>
      simp only [lowerStmt]
      exact TypeRun.bind (TypeRun.pure _) fun _ => TypeRun.bind (types_leaveTo 0) fun _ => types_emitTerm _
  | .brk _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact TypeRun.pure _
    | some l =>
      simp only [lowerStmt]
      exact TypeRun.bind (types_leaveTo _) fun _ => types_emitTerm _
  | .cont _ => by
    cases lc with
    | none => simp only [lowerStmt]; exact TypeRun.pure _
    | some l =>
      cases hk : l.cont with
      | jump h =>
        simp only [lowerStmt, hk]
        exact TypeRun.bind (types_leaveTo _) fun _ => types_emitTerm _
      | next h t i =>
        simp only [lowerStmt, hk]
        exact TypeRun.bind (types_leaveTo _) fun _ => TypeRun.bind (types_emitDef _) fun _ => types_emitTerm _
  | .print args org => by
    simp only [lowerStmt]
    exact TypeRun.bind (types_lowerPrintArgs args) fun _ => types_emitEffect _
  | .assertS e org => by
    simp only [lowerStmt]
    exact TypeRun.bind (types_lowerExpr e) fun cv => types_assert_core cv org
  | .abort _ org => by
    simp only [lowerStmt]
    exact types_emitTerm _
  | .exit e org => by
    simp only [lowerStmt]
    exact TypeRun.bind (types_lowerExpr e) fun _ => types_emitTerm _

end


end Goose.Lower.Validation
