import Goose.Lower.Eventual
import Goose.Lower.Claims
import Goose.Lower.Return
import Goose.Core.Sound.Invert
import Goose.Core.Sound.Spec
import Goose.Lower.LoopFlow
import Goose.Lower.RuntimeSim

namespace Goose.Lower

open Goose.Core Goose.GIR

def EachSourceCells (owner : Option ValueId) (view : ValueId) (vw : ViewVal) :
    List (ValueId × RVal) :=
  (view, .view vw) :: owner.toList.map (fun r => (r, .val (.ref vw.loc)))

def eachSourceRegrows (access : AccessEnv) : View → Bool
  | .val _ => false
  | .of place => match access.placeType? place with
    | some (.grow _) | some (.growshrink _) => true
    | _ => false

theorem eachSourceRegrows_of_aliases {m : Core.Module} {world : Core.Sound.World}
    {penv : PEnv} {env : Env} {store : Store} {source : View} {vw : ViewVal} {element : Ty}
    (h : Core.Sound.ViewAliases m world penv env store source vw element) :
    eachSourceRegrows penv.access source = vw.resizable := by
  cases h with
  | fixed hresize hclass _ =>
    rcases hclass with ⟨expr, rfl⟩ | ⟨place, count, rfl, htype⟩
    · exact hresize.symm
    · simp [eachSourceRegrows, htype, hresize]
  | limited hresize place capacity hsource htype _ _ =>
    simp [eachSourceRegrows, hsource, htype, hresize]
  | owner hresize place owner hsource howner htype _ _ =>
    rcases howner with rfl | rfl
    all_goals simp [eachSourceRegrows, hsource, htype, hresize]

theorem lowerEachSource_of_sim (n : Nat) (ihp : ∀ p, PlaceClaim n p) (p : Place)
    (hok : placeOk p = true) (le : LEnv) (ls ls' : LS)
    (owner : Option ValueId) (view : ValueId) (pt : Pt) (cfg : Cfg) (env : Env)
    (cx : FnCtx) (fr : Frame)
    (hlow : lowerEachSource (.of p) le ls = ((owner, view), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls) :
    SimG cx pt fr (evalView (n + 1) cfg env (.of p))
      (fun vw pt' fr' => owner.isSome = true ∧
        Post cfg env cx ls fr ls' fr' pt' (EachSourceCells owner view vw)) := by
  simp only [lowerEachSource, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, rv, ls2, h2, h3⟩ := hlow
  rw [pure_run] at h3
  obtain ⟨hp, rfl⟩ := Prod.mk.inj h3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
  have hext1 := hext.of_adv (adv_emitDef h2)
  simp only [evalView]
  refine SimG.bind (ihp p hok le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel)
    fun l pt1 fr1 P1 => ?_
  have hc : fr1.vals[rp]? = some (.val (.ref l)) := P1.has (rp, _) (by simp)
  have hop : execPure cx fr1 (.snapshot
      (match p with | .var _ | .global _ => .owner | _ => .borrowed) rp) =
      (readLoc l >>= expectArray) >>= fun lr => pure (RVal.view ⟨l, 0, lr.1, lr.2⟩) := by
    simp [execPure, getVal_of hc, Goose.Core.expectRef, bind_assoc]
  rw [← bind_assoc]
  change SimG cx pt1 fr1 ((readLoc l >>= expectArray) >>= fun lr =>
    pure (⟨l, 0, lr.1, lr.2⟩ : ViewVal)) _
  refine SimG.bind (leaf_def_keep (c := readLoc l >>= expectArray) P1 h2 hext (by simp)
    (fun lr => RVal.view ⟨l, 0, lr.1, lr.2⟩) hop) fun lr pt' fr' P => ?_
  exact SimG.ret ⟨rfl, by simpa [EachSourceCells] using P⟩

theorem lowerEachSource_val_sim (n : Nat) (ihe : ∀ e, ExprClaim n e) (e : Expr)
    (hok : exprOk e = true) (le : LEnv) (ls ls' : LS)
    (owner : Option ValueId) (view : ValueId) (pt : Pt) (cfg : Cfg) (env : Env)
    (cx : FnCtx) (fr : Frame)
    (hlow : lowerEachSource (.val e) le ls = ((owner, view), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls) :
    SimG cx pt fr (evalView (n + 1) cfg env (.val e))
      (fun vw pt' fr' => owner = none ∧ vw.resizable = false ∧
        Post cfg env cx ls fr ls' fr' pt' (EachSourceCells owner view vw)) := by
  simp only [lowerEachSource, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, rv, ls2, h2, h3⟩ := hlow
  rw [pure_run] at h3
  obtain ⟨hp, rfl⟩ := Prod.mk.inj h3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
  have hext1 := hext.of_adv (adv_emitDef h2)
  simp only [evalView]
  refine SimG.bind (ihe e hok le ls rp ls1 pt cfg env cx fr h1 hpp hext1 hrel)
    fun va pt1 fr1 P1 => ?_
  refine SimG.expectSlice fun l start len hva => ?_
  subst hva
  have hc : fr1.vals[rp]? = some (.val (.slice l start len)) :=
    P1.has (rp, _) (by simp)
  have hop : execPure cx fr1 (.sliceView rp) =
      (pure (RVal.view ⟨l, start, len, false⟩) : M RVal) := by
    simp [execPure, getVal_of hc, Goose.Core.expectSlice]
  have hs : SimG cx pt1 fr1 (pure () >>= fun _ => pure (⟨l, start, len, false⟩ : ViewVal))
      (fun vw pt' fr' => True ∧ vw.resizable = false ∧
        Post cfg env cx ls fr ls2 fr' pt' (EachSourceCells none rv vw)) := by
    refine SimG.bind (leaf_def (c := pure ()) P1 h2 hext
      (by simp) (fun _ => RVal.view ⟨l, start, len, false⟩) (by simpa using hop))
      fun _ pt' fr' P => ?_
    exact SimG.ret ⟨by trivial, rfl, P⟩
  simpa only [pure_bind] using hs

theorem execPure_eachElem {cx : FnCtx} {fr : Frame} {view counter : ValueId}
    {vw : ViewVal} {i : Nat}
    (hview : fr.vals[view]? = some (.view vw))
    (hcounter : fr.vals[counter]? = some (.val (.int .i64 i))) :
    execPure cx fr (.refElem view counter) =
      pure (.val (.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)) := by
  simp [execPure, getView_of hview, getVal_of hcounter, Goose.Core.expectInt]

theorem execPure_eachSampled {cx : FnCtx} {fr : Frame} {view : ValueId} {vw : ViewVal}
    (hview : fr.vals[view]? = some (.view vw)) :
    execPure cx fr (.viewLen view) = pure (.val (.int .i64 vw.len)) := by
  simp [execPure, getView_of hview]

theorem arrayLen_eventual {cx : FnCtx} {fr : Frame} {owner : ValueId} {loc : Loc}
    (howner : fr.vals[owner]? = some (.val (.ref loc))) (s : St) :
    EventualM (lengthLoc loc >>= fun n => pure (RVal.val (.int .i64 n)))
      (fun k => execOp k cx fr (.arrayLen owner)) s := by
  have hOp : ∀ k, execOp k cx fr (.arrayLen owner) =
      (readLoc loc >>= expectArray) >>= fun lr => pure (RVal.val (.int .i64 lr.1)) := by
    intro k
    simp [execOp, execPure, getVal_of howner, Goose.Core.expectRef, bind_assoc]
  constructor
  · intro value state hc
    simp only [bind_apply] at hc
    cases hr : s.store.read loc with
    | error err => simp [lengthLoc, Store.length, hr, pure_apply] at hc
    | ok v =>
      cases v <;> simp [lengthLoc, Store.length, hr, pure_apply] at hc
      all_goals
        obtain ⟨rfl, rfl⟩ := hc
        exact ⟨0, fun k _ => by simp [hOp, readLoc, hr, expectArray, bind_apply, pure_apply]⟩
  · intro err state hc hf
    simp only [bind_apply] at hc
    cases hr : s.store.read loc with
    | error fault =>
      simp [lengthLoc, Store.length, hr, pure_apply] at hc
      obtain ⟨rfl, _⟩ := hc
      cases hf
    | ok v =>
      cases v <;> simp [lengthLoc, Store.length, hr, pure_apply] at hc
      all_goals
        obtain ⟨rfl, _⟩ := hc
        cases hf

theorem eachLen_grow_sim {cfg : Cfg} {env : Env} {cx : FnCtx} {le : LEnv}
    {ls ls' : LS} {fr : Frame} {pt : Pt} {owner : Option ValueId}
    {sampled result : ValueId} {loc : Loc}
    (howner : fr.vals[owner.getD 0]? = some (.val (.ref loc)))
    (hlow : eachLen true owner sampled le ls = (result, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks)
    (hrel : Rel cfg env cx fr ls) :
    SimE cx pt fr (lengthLoc loc)
      (fun len pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(result, .val (.int .i64 len))]) := by
  simp only [eachLen, ite_true] at hlow
  have P := Post.init hrel hpp
  have hi := (Post.def_leaf P hlow hext (.val .unit)).2
  refine (SimE.def_step (c := lengthLoc loc) (fun (n : Nat) => .val (.int .i64 n)) hi (arrayLen_eventual howner)).mono
    fun n pt' fr' h => ?_
  obtain ⟨rfl, rfl⟩ := h
  exact (Post.def_leaf P hlow hext (.val (.int .i64 n))).1

theorem eachLen_sampled_sim {cfg : Cfg} {env : Env} {cx : FnCtx} {le : LEnv}
    {ls ls' : LS} {fr : Frame} {pt : Pt} {owner : Option ValueId}
    {sampled result : ValueId} {len : Nat}
    (hsampled : fr.vals[sampled]? = some (.val (.int .i64 len)))
    (hlt : sampled < ls.vals.size)
    (hlow : eachLen false owner sampled le ls = (result, ls'))
    (hpp : ls.pp = some pt) (hrel : Rel cfg env cx fr ls) :
    SimE cx pt fr (pure len)
      (fun len pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(result, .val (.int .i64 len))]) := by
  simp only [eachLen, Bool.false_eq_true, ite_false, pure_run] at hlow
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlow
  exact SimE.ret ⟨hpp, by simpa using hsampled, by simpa using hlt,
    Nat.le_refl _, Same.refl _ _, hrel⟩

theorem regrowOf_none (le : LEnv) (ls : LS) : regrowOf none le ls = (false, ls) := rfl

theorem regrowOf_state (owner : Option ValueId) (le : LEnv) (ls : LS) :
    (regrowOf owner le ls).2 = ls := by
  cases owner with
  | none => rfl
  | some r =>
    simp only [regrowOf, growOwner, bind_run]
    have hs := valTy_run r le ls
    cases hv : valTy r le ls with
    | mk ty state =>
      rw [hv] at hs
      simp only at hs ⊢
      subst state
      cases ty with
      | data ty => cases ty <;> rfl
      | view _ _ => rfl

theorem regrowOf_some {le : LEnv} {ls : LS} {owner : ValueId} {mu : Mutability} {ty : Ty}
    (h : ls.vals[owner]? = some (some (.data (.ref mu ty)))) :
    regrowOf (some owner) le ls =
      ((match ty with | .grow _ | .growshrink _ => true | _ => false), ls) := by
  simp only [regrowOf, growOwner, valTy, bind_run, get_apply, pure_run, h]
  cases ty <;> rfl

theorem eachSourceMode_val {le : LEnv} {ls output : LS} {expr : Expr}
    {owner : Option ValueId} {view : ValueId} (access : AccessEnv)
    (h : lowerEachSource (.val expr) le ls = ((owner, view), output)) :
    (regrowOf owner le output).1 = eachSourceRegrows access (.val expr) := by
  simp only [lowerEachSource, bind_eq] at h
  obtain ⟨_, _, _, _, _, _, h⟩ := h
  rw [pure_run] at h
  have ho := (Prod.mk.inj (Prod.mk.inj h).1).1
  cases ho
  rfl

theorem eachSourceMode_global {le : LEnv} {ls output : LS} {g block : Nat}
    {owner : Option ValueId} {view : ValueId} {ty : Ty} {kind : VarKind}
    (access : AccessEnv) (global : Core.Global)
    (hglobal : le.globals[g]? = some (ty, kind))
    (haccess : access.mod.globals[g]? = some global) (htype : global.ty = ty)
    (hcur : ls.cur = some block)
    (h : lowerEachSource (.of (.global g)) le ls = ((owner, view), output)) :
    (regrowOf owner le output).1 = eachSourceRegrows access (.of (.global g)) := by
  simp only [lowerEachSource, lowerPlace, bind_eq] at h
  obtain ⟨r, withOwner, howner, vw, withView, hview, hresult⟩ := h
  rw [pure_run] at hresult
  obtain ⟨hpair, rfl⟩ := Prod.mk.inj hresult
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
  have hOp : ∃ mu, (Op.globalAddr g).resultTy (tyEnv le ls) = .ok (.data (.ref mu ty)) := by
    simp only [Op.resultTy, tyEnv, hglobal]
    exact ⟨_, rfl⟩
  obtain ⟨mu, hOp⟩ := hOp
  have hOwnerRun := howner
  rw [emitDef_run _ le hcur] at hOwnerRun
  obtain ⟨hId, hOwnerState⟩ := Prod.mk.inj hOwnerRun
  have hcurOwner : withOwner.cur = some block := by
    simpa using (congrArg LS.cur hOwnerState).symm.trans hcur
  have hOwnerTy : withOwner.vals[r]? = some (some (.data
      (.ref mu ty))) := by
    rw [← hId, ← hOwnerState]
    simp [hOp]
    rfl
  have hViewRun := hview
  rw [emitDef_run _ le hcurOwner] at hViewRun
  obtain ⟨_, hViewState⟩ := Prod.mk.inj hViewRun
  have hOwnerBound : r < withOwner.vals.size := (Array.getElem?_eq_some_iff.mp hOwnerTy).1
  have hOutputTy : withView.vals[r]? = some (some (.data
      (.ref mu ty))) := by
    rw [← hViewState]
    exact (getElem?_push_lt hOwnerBound).trans hOwnerTy
  rw [regrowOf_some hOutputTy]
  simp only [eachSourceRegrows, AccessEnv.placeType?, haccess, Option.map_some, htype]
  cases ty <;> rfl

theorem eachSourceMode_var {le : LEnv} {ls output : LS} {x block : Nat}
    {owner : Option ValueId} {view : ValueId} {ty : Ty}
    (access : AccessEnv) (localVar : Core.LocalVar) (slot : GIR.Slot)
    (hslot : le.slots[x]? = some slot) (hslotType : slot.ty = ty)
    (haccess : access.impl.vars[x]? = some localVar) (htype : localVar.ty = ty)
    (hcur : ls.cur = some block)
    (h : lowerEachSource (.of (.var x)) le ls = ((owner, view), output)) :
    (regrowOf owner le output).1 = eachSourceRegrows access (.of (.var x)) := by
  simp only [lowerEachSource, lowerPlace, bind_eq] at h
  obtain ⟨r, withOwner, howner, vw, withView, hview, hresult⟩ := h
  rw [pure_run] at hresult
  obtain ⟨hpair, rfl⟩ := Prod.mk.inj hresult
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
  have hOp : ∃ mu, (Op.slotAddr x).resultTy (tyEnv le ls) = .ok (.data (.ref mu ty)) := by
    simp only [Op.resultTy, tyEnv, hslot, hslotType]
    exact ⟨_, rfl⟩
  obtain ⟨mu, hOp⟩ := hOp
  have hOwnerRun := howner
  rw [emitDef_run _ le hcur] at hOwnerRun
  obtain ⟨hId, hOwnerState⟩ := Prod.mk.inj hOwnerRun
  have hcurOwner : withOwner.cur = some block := by
    simpa using (congrArg LS.cur hOwnerState).symm.trans hcur
  have hOwnerTy : withOwner.vals[r]? = some (some (.data
      (.ref mu ty))) := by
    rw [← hId, ← hOwnerState]
    simp [hOp]
    rfl
  have hViewRun := hview
  rw [emitDef_run _ le hcurOwner] at hViewRun
  obtain ⟨_, hViewState⟩ := Prod.mk.inj hViewRun
  have hOwnerBound : r < withOwner.vals.size := (Array.getElem?_eq_some_iff.mp hOwnerTy).1
  have hOutputTy : withView.vals[r]? = some (some (.data
      (.ref mu ty))) := by
    rw [← hViewState]
    exact (getElem?_push_lt hOwnerBound).trans hOwnerTy
  rw [regrowOf_some hOutputTy]
  simp only [eachSourceRegrows, AccessEnv.placeType?, haccess, Option.map_some, htype]
  cases ty <;> rfl

theorem eachSourceMode_var_lowerEnv {m : Core.Module} {vars : Array Core.LocalVar}
    {results : List Ty} {ls output : LS} {x block : Nat} {owner : Option ValueId} {view : ValueId}
    (access : AccessEnv) (localVar : Core.LocalVar) (hvars : access.impl.vars = vars)
    (hlocal : vars[x]? = some localVar) (hcur : ls.cur = some block)
    (h : lowerEachSource (.of (.var x)) (lowerEnv m vars results) ls = ((owner, view), output)) :
    (regrowOf owner (lowerEnv m vars results) output).1 =
      eachSourceRegrows access (.of (.var x)) := by
  apply eachSourceMode_var access localVar
    (⟨localVar.ty, localVar.kind, localVar.scope, x⟩ : GIR.Slot)
  · simp [lowerEnv, Array.getElem?_mapIdx, hlocal]
  · rfl
  · simpa [hvars] using hlocal
  · rfl
  · exact hcur
  · exact h

theorem eachSourceMode_global_lowerEnv {m : Core.Module} {vars : Array Core.LocalVar}
    {results : List Ty} {ls output : LS} {g block : Nat} {owner : Option ValueId} {view : ValueId}
    (access : AccessEnv) (global : Core.Global) (hmodule : access.mod = m)
    (hglobal : m.globals[g]? = some global) (hcur : ls.cur = some block)
    (h : lowerEachSource (.of (.global g)) (lowerEnv m vars results) ls = ((owner, view), output)) :
    (regrowOf owner (lowerEnv m vars results) output).1 =
      eachSourceRegrows access (.of (.global g)) := by
  apply eachSourceMode_global (ty := global.ty) (kind := global.kind) access global
  · simp [lowerEnv, hglobal]
  · simpa [hmodule] using hglobal
  · rfl
  · exact hcur
  · exact h

theorem eachSourceMode_of_placeType {le : LEnv} {ls output : LS} {place : Place}
    {owner : Option ValueId} {view : ValueId} {ty : Ty} (access : AccessEnv)
    (htype : access.placeType? place = some ty)
    (hplace : ∀ r input, lowerPlace place le ls = (r, input) →
      ∃ mu block, input.vals[r]? = some (some (.data (.ref mu ty))) ∧ input.cur = some block)
    (h : lowerEachSource (.of place) le ls = ((owner, view), output)) :
    (regrowOf owner le output).1 = eachSourceRegrows access (.of place) := by
  simp only [lowerEachSource, bind_eq] at h
  obtain ⟨r, withOwner, howner, vw, withView, hview, hresult⟩ := h
  rw [pure_run] at hresult
  obtain ⟨hpair, rfl⟩ := Prod.mk.inj hresult
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
  obtain ⟨mu, block, hOwnerTy, hcurOwner⟩ := hplace r withOwner howner
  have hViewRun := hview
  rw [emitDef_run _ le hcurOwner] at hViewRun
  obtain ⟨_, hViewState⟩ := Prod.mk.inj hViewRun
  have hOwnerBound : r < withOwner.vals.size := (Array.getElem?_eq_some_iff.mp hOwnerTy).1
  have hOutputTy : withView.vals[r]? = some (some (.data (.ref mu ty))) := by
    rw [← hViewState]
    exact (getElem?_push_lt hOwnerBound).trans hOwnerTy
  rw [regrowOf_some hOutputTy]
  simp only [eachSourceRegrows, htype]
  cases ty <;> rfl

theorem eachSampled_sim {cfg : Cfg} {env : Env} {cx : FnCtx} {le : LEnv}
    {ls lsk ls' : LS} {fr frk : Frame} {pt : Pt} {cells : List (ValueId × RVal)}
    {view result : ValueId} {vw : ViewVal}
    (P : Post cfg env cx ls fr lsk frk pt cells)
    (hview : frk.vals[view]? = some (.view vw)) (regrow : Bool)
    (hlow : eachSampled regrow view le lsk = (result, ls'))
    (hext : ExtT ls' cx.fn.blocks) :
    SimG cx pt frk (pure ())
      (fun _ pt' fr' => Post cfg env cx ls fr ls' fr' pt'
        (if regrow then cells else (result, .val (.int .i64 vw.len)) :: cells)) := by
  cases regrow with
  | true =>
    simp only [eachSampled, ite_true, pure_run] at hlow
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlow
    exact SimG.ret P
  | false =>
    simp only [eachSampled, Bool.false_eq_true, ite_false] at hlow
    exact leaf_def_keep P hlow hext (by simp) (fun _ => .val (.int .i64 vw.len))
      (by simpa using execPure_eachSampled hview)

theorem eachElemValue_ref_cases {x : VarId} {elem value : ValueId} {le : LEnv}
    {ls ls' : LS} (h : eachElemValue x true elem le ls = (value, ls')) :
    (value = elem ∧ ls' = ls) ∨ emitDef (.refFreeze elem) le ls = (value, ls') := by
  simp only [eachElemValue, ite_true, bind_eq] at h
  obtain ⟨le', state, hr, h⟩ := h
  change (le, ls) = (le', state) at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
  cases hv : le.vars[x]? with
  | none =>
    simp only [hv, pure_run] at h
    exact Or.inl ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩
  | some lv =>
    simp only [hv] at h
    cases ht : lv.ty <;> simp only [ht] at h
    all_goals first
      | exact freezeTo_cases h
      | exact Or.inl ⟨(Prod.mk.inj h).1.symm, (Prod.mk.inj h).2.symm⟩

theorem eachElemValue_sim {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls lsk ls' : LS} {fr frk : Frame} {pt : Pt} {elem value : ValueId} {loc : Loc}
    (P : Post cfg env cx ls fr lsk frk pt [(elem, .val (.ref loc))])
    (x : VarId) (byRef : Bool) (le : LEnv)
    (h : eachElemValue x byRef elem le lsk = (value, ls'))
    (hext : ExtT ls' cx.fn.blocks) :
    SimG cx pt frk (if byRef then pure (Val.ref loc) else readLoc loc)
      (fun v pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(value, .val v)]) := by
  have hc : frk.vals[elem]? = some (.val (.ref loc)) := P.has (elem, _) (by simp)
  cases byRef with
  | false =>
    simp only [eachElemValue, Bool.false_eq_true, ite_false] at h ⊢
    refine leaf_def P h hext (by simp) RVal.val ?_
    simp [execPure, getVal_of hc, Goose.Core.expectRef]
  | true =>
    simp only [ite_true]
    rcases eachElemValue_ref_cases h with ⟨rfl, rfl⟩ | hf
    · exact SimG.ret P
    · have hs : SimG cx pt frk (pure () >>= fun _ => pure (Val.ref loc))
          (fun v pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(value, .val v)]) := by
        refine SimG.bind (leaf_def (c := pure ()) P hf hext (by simp)
          (fun _ => RVal.val (.ref loc)) ?_) fun _ pt' fr' P' => SimG.ret P'
        simp [execPure, getVal_of hc, Goose.Core.expectRef]
      simpa only [pure_bind] using hs

def eachIRPre (x : VarId) (idx : Option VarId) (value counter : ValueId) (org : OriginId) :
    List (SlotId × ValueId × OriginId) :=
  (x, value, org) :: (match idx with | some j => [(j, counter, org)] | none => [])

def eachCorePre (x : VarId) (idx : Option VarId) (value : Val) (i : Nat) : List (VarId × Val) :=
  (x, value) :: (match idx with | some j => [(j, Val.int .i64 i)] | none => [])

theorem eachIteration_sim (n : Nat) (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv)
    (input withElem withValue output : LS) (fr : Frame) (pt : Pt)
    (view counter elem value result : ValueId) (vw : ViewVal) (i : Nat)
    (x : VarId) (idx : Option VarId) (byRef : Bool) (block : Core.Block)
    (loop : LoopCtx) (org : OriginId) (post : Flow → Pt → Frame → Prop)
    (hElem : emitDef (.refElem view counter) le input = (elem, withElem))
    (hValue : eachElemValue x byRef elem le withElem = (value, withValue))
    (hBlock : lowerBlock (some loop)
      (eachIRPre x idx value counter org)
      false block le withValue = (result, output))
    (hpp : input.pp = some pt) (hext : ExtT output cx.fn.blocks)
    (hrel : Rel cfg env cx fr input)
    (hview : fr.vals[view]? = some (.view vw))
    (hcounter : fr.vals[counter]? = some (.val (.int .i64 i)))
    (hc : counter < input.vals.size)
    (hbody : ∀ ev pt' fr',
      Post cfg env cx input fr withValue fr' pt' [(value, .val ev)] →
      PreRel fr' (eachIRPre x idx value counter org)
        (eachCorePre x idx ev i) →
      SimE cx pt' fr' (execBlock n cfg env
        (eachCorePre x idx ev i) block >>=
        prepareReturn env) post) :
    SimE cx pt fr
      ((if byRef then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
        else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) >>= fun ev =>
      execBlock n cfg env (eachCorePre x idx ev i) block >>= prepareReturn env) post := by
  have aBlock := advB_lowerBlock (some loop)
    (eachIRPre x idx value counter org)
    false block le withValue result output hBlock
  have hextValue := hext.of_adv aBlock
  have hextElem := hextValue.of_adv (advB_eachElemValue x byRef elem le withElem value withValue hValue)
  have hop := execPure_eachElem (cx := cx) hview hcounter
  have hElemSim := leaf_def (c := pure ()) (Post.init hrel hpp) hElem hextElem (by simp)
    (fun _ => RVal.val (.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)) (by simpa using hop)
  have hunit :
      ((if byRef then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
        else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) >>= fun ev =>
      execBlock n cfg env (eachCorePre x idx ev i) block >>= prepareReturn env) =
      (pure () >>= fun _ =>
      (if byRef then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
        else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) >>= fun ev =>
      execBlock n cfg env (eachCorePre x idx ev i) block >>= prepareReturn env) := by simp
  rw [hunit]
  refine SimE.bind (SimE.of_simG hElemSim) fun _ ptElem frElem PElem => ?_
  refine SimE.bind (SimE.of_simG (eachElemValue_sim PElem x byRef le hValue hextValue))
    fun ev ptValue frValue PValue => ?_
  have hcounterValue : frValue.vals[counter]? = some (.val (.int .i64 i)) := by
    rw [PValue.same counter hc]
    exact hcounter
  have hpre : PreRel frValue
      (eachIRPre x idx value counter org)
      (eachCorePre x idx ev i) := by
    have hval := PValue.has (value, .val ev) (by simp)
    cases idx <;> simp [PreRel, eachIRPre, eachCorePre, hval, hcounterValue]
  exact hbody ev ptValue frValue PValue hpre

theorem tyStmt_each_scopes (env : TEnv) (sc : Nat) (x : VarId) (idx : Option VarId)
    (source : View) (byRef : Bool) (body : Core.Block) (org : OriginId)
    (next next' : Nat) (env' : TEnv)
    (h : tyStmt env sc (.forEach x idx source byRef body org) next = .ok (env', next')) :
    (∃ lv, env.vars[x]? = some lv ∧ lv.scope = body.scope) ∧
      (∀ j, idx = some j → ∃ lv, env.vars[j]? = some lv ∧ lv.scope = body.scope ∧
        lv.ty = .int .i64) := by
  rw [tyStmt] at h
  obtain ⟨_, middle, _, h⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp h
  obtain ⟨lv, after, hd, h⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp h
  obtain ⟨_, afterIndex, hi, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp h
  obtain ⟨_, hvar, hscope, _, _⟩ := Core.Sound.declare_ok env x body.scope middle (lv, after) hd
  obtain ⟨_, hidx⟩ := Core.Sound.declareIndex_ok env body.scope idx after ((), afterIndex) hi
  refine ⟨⟨lv, hvar, hscope⟩, ?_⟩
  intro j hj
  obtain ⟨_, lj, hv, hs, ht⟩ := hidx j hj
  exact ⟨lj, hv, hs, ht⟩

theorem eachIRPre_scopes_of_typed (sourceEnv : TEnv) (env : Env) (sc : Nat)
    (x : VarId) (idx : Option VarId) (source : View) (byRef : Bool) (body : Core.Block)
    (org : OriginId) (next next' value counter : Nat) (after : TEnv)
    (hvars : sourceEnv.vars = env.vars)
    (htype : tyStmt sourceEnv sc (.forEach x idx source byRef body org) next = .ok (after, next')) :
    ∀ p ∈ eachIRPre x idx value counter org,
      ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = body.scope := by
  have hscope := tyStmt_each_scopes sourceEnv sc x idx source byRef body org next next' after htype
  rw [hvars] at hscope
  intro p hp
  cases hi : idx with
  | none =>
    simp only [eachIRPre, hi, List.mem_singleton] at hp
    subst p
    exact hscope.1
  | some j =>
    simp only [eachIRPre, hi, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hscope.1
    · obtain ⟨lv, hvar, hsc, _⟩ := hscope.2 j hi
      exact ⟨lv, hvar, hsc⟩

def preparedEach (n : Nat) (cfg : Cfg) (env : Env) (x : VarId) (idx : Option VarId)
    (byRef : Bool) (body : Core.Block) (vw : ViewVal) (i : Nat) : M Flow :=
  (if vw.resizable then lengthLoc vw.loc else pure vw.len) >>= fun len =>
    if i < len then
      (if byRef then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
        else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) >>= fun ev =>
      (execBlock n cfg env ((x, ev) :: (match idx with
        | some j => [(j, Val.int .i64 i)] | none => [])) body >>= prepareReturn env) >>= fun flow =>
        match flow with
        | .normal _ | .cont => execEach n cfg env x idx byRef body vw (i + 1) >>= prepareReturn env
        | .brk => pure (.normal .unit)
        | .ret v => pure (.ret v)
    else pure (.normal .unit)

private theorem each_step (n : Nat) (cfg : Cfg) (env : Env) (x : VarId)
    (idx : Option VarId) (byRef : Bool) (body : Core.Block) (vw : ViewVal) (i : Nat) :
    execEach (n + 1) cfg env x idx byRef body vw i =
      ((if vw.resizable then lengthLoc vw.loc else pure vw.len) >>= fun len =>
        if i < len then
          ((if byRef then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
            else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) >>= fun ev =>
          execBlock n cfg env ((x, ev) :: (match idx with
              | some j => [(j, Val.int .i64 i)] | none => [])) body >>= fun fl =>
            match fl with
            | .normal _ | .cont => execEach n cfg env x idx byRef body vw (i + 1)
            | .brk => pure (.normal .unit)
            | .ret v => pure (.ret v))
        else pure (.normal .unit)) := by
  conv => lhs; unfold execEach
  cases vw.resizable <;> cases byRef <;> rfl

theorem prepareReturn_execEach (n : Nat) (cfg : Cfg) (env : Env) (x : VarId)
    (idx : Option VarId) (byRef : Bool) (body : Core.Block) (vw : ViewVal) (i : Nat) :
    (execEach (n + 1) cfg env x idx byRef body vw i >>= prepareReturn env) =
      preparedEach n cfg env x idx byRef body vw i := by
  rw [each_step]
  simp only [preparedEach, bind_assoc]
  congr 1
  funext len
  by_cases hi : i < len
  · simp only [hi, ite_true, bind_assoc]
    congr 1
    funext ev
    congr 1
    funext flow
    cases flow <;> simp [prepareReturn, bind_assoc, pure_bind]
  · simp [hi, prepareReturn]

def EachBranch (cx : FnCtx) (vw : ViewVal) (header body : Pt)
    (headerInv bodyInv : Nat → Frame → Prop) (post : Flow → Pt → Frame → Prop) : Prop :=
  ∀ i fr, headerInv i fr →
    SimE cx header fr (if vw.resizable then lengthLoc vw.loc else pure vw.len)
      (fun len pt' fr' => if i < len then pt' = body ∧ bodyInv i fr'
        else post (.normal .unit) pt' fr')

def EachBodyAt (n : Nat) (cx : FnCtx) (cfg : Cfg) (env : Env) (x : VarId) (idx : Option VarId)
    (byRef : Bool) (block : Core.Block) (vw : ViewVal) (header body : Pt)
    (headerInv bodyInv : Nat → Frame → Prop) (post : Flow → Pt → Frame → Prop) : Prop :=
  ∀ i fr, bodyInv i fr →
    SimE cx body fr
      ((if byRef then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
        else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) >>= fun ev =>
      execBlock n cfg env ((x, ev) :: (match idx with
        | some j => [(j, Val.int .i64 i)] | none => [])) block >>= prepareReturn env)
      (fun flow pt' fr' => match flow with
        | .normal _ | .cont => ∃ frh, headerInv (i + 1) frh ∧ Goes cx pt' fr' header frh
        | .brk => post (.normal .unit) pt' fr'
        | .ret value => post (.ret value) pt' fr')

def EachBody (cx : FnCtx) (cfg : Cfg) (env : Env) (x : VarId) (idx : Option VarId)
    (byRef : Bool) (block : Core.Block) (vw : ViewVal) (header body : Pt)
    (headerInv bodyInv : Nat → Frame → Prop) (post : Flow → Pt → Frame → Prop) : Prop :=
  ∀ n, EachBodyAt n cx cfg env x idx byRef block vw header body headerInv bodyInv post

theorem each_sim_bounded (n : Nat) (cx : FnCtx) (cfg : Cfg) (env : Env)
    (x : VarId) (idx : Option VarId) (byRef : Bool) (block : Core.Block) (vw : ViewVal)
    (header body : Pt) (headerInv bodyInv : Nat → Frame → Prop)
    (post : Flow → Pt → Frame → Prop)
    (hbranch : EachBranch cx vw header body headerInv bodyInv post)
    (hbody : ∀ k, k < n → EachBodyAt k cx cfg env x idx byRef block vw
      header body headerInv bodyInv post) :
    ∀ i fr, headerInv i fr →
      SimE cx header fr (execEach n cfg env x idx byRef block vw i >>= prepareReturn env) post := by
  induction n with
  | zero =>
    intro i fr _
    simp only [execEach]
    exact SimE.of_timeout_bind
  | succ n ih =>
    intro i fr hinv
    rw [prepareReturn_execEach]
    unfold preparedEach
    refine SimE.bind (hbranch i fr hinv) fun len pt1 fr1 hlen => ?_
    by_cases hi : i < len
    · simp only [hi, ite_true] at hlen ⊢
      obtain ⟨rfl, hinvBody⟩ := hlen
      rw [← bind_assoc]
      refine SimE.bind (hbody n (Nat.lt_succ_self n) i fr1 hinvBody)
        fun flow pt2 fr2 hflow => ?_
      cases flow with
      | normal value | cont =>
        obtain ⟨frh, hinvh, hgo⟩ := hflow
        exact SimE.goes hgo (ih (fun k hk => hbody k (Nat.lt_trans hk (Nat.lt_succ_self n)))
          (i + 1) frh hinvh)
      | brk => exact SimE.ret hflow
      | ret value => exact SimE.ret hflow
    · simp only [hi, ite_false] at hlen ⊢
      exact SimE.ret hlen

theorem each_sim (cx : FnCtx) (cfg : Cfg) (env : Env) (x : VarId) (idx : Option VarId)
    (byRef : Bool) (block : Core.Block) (vw : ViewVal) (header body : Pt)
    (headerInv bodyInv : Nat → Frame → Prop) (post : Flow → Pt → Frame → Prop)
    (hbranch : EachBranch cx vw header body headerInv bodyInv post)
    (hbody : EachBody cx cfg env x idx byRef block vw header body headerInv bodyInv post) :
    ∀ n i fr, headerInv i fr →
      SimE cx header fr (execEach n cfg env x idx byRef block vw i >>= prepareReturn env) post := by
  intro n i fr hinv
  exact each_sim_bounded n cx cfg env x idx byRef block vw header body headerInv bodyInv post
    hbranch (fun k _ => hbody k) i fr hinv

theorem lowerEach_unfold {regrow : Bool} {owner : Option ValueId}
    {sampled hb i : Nat} {body : Nat → BlockId → B ValueId} {le : LEnv} {ls ls' : LS}
    (h : lowerEach regrow owner sampled hb i body le ls = ((), ls')) :
    ∃ len lsLen c lsCmp tb xb lsf lsBody rBody lsBodyEnd lsBack,
      eachLen regrow owner sampled le ls = (len, lsLen) ∧
      emitDef (.cmp .lt .i64 i len) le lsLen = (c, lsCmp) ∧
      fork c le lsCmp = ((tb, xb), lsf) ∧
      lsBody = { lsf with cur := some tb } ∧
      body lsCmp.stack.length xb le lsBody = (rBody, lsBodyEnd) ∧
      rangeBack .i64 i hb le lsBodyEnd = ((), lsBack) ∧
      ls' = { lsBack with cur := some xb } := by
  unfold lowerEach loopBody at h
  simp only [bind_eq] at h
  obtain ⟨len, lsLen, hlen, c, lsCmp, hcmp, d, lsG, hg, ⟨tb, xb⟩, lsf, hf,
    u1, lsBody, hs, rBody, lsBodyEnd, hbdy, u2, lsBack, hback, hexit⟩ := h
  rw [get_apply] at hg
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hg
  rw [setCur_run] at hs hexit
  exact ⟨len, lsLen, c, lsCmp, tb, xb, lsf, lsBody, rBody, lsBodyEnd, lsBack,
    hlen, hcmp, hf, (Prod.mk.inj hs).2.symm, hbdy, hback, (Prod.mk.inj hexit).2.symm⟩

theorem lowerStmt_each_unfold (lc : Option LoopCtx) (x : VarId) (idx : Option VarId)
    (source : View) (byRef : Bool) (body : Core.Block) (org : OriginId)
    (le : LEnv) (ls ls' : LS)
    (h : lowerStmt lc (.forEach x idx source byRef body org) le ls = ((), ls')) :
    ∃ owner view lsSource regrow sampled lsSampled start lsStart,
      lowerEachSource source le ls = ((owner, view), lsSource) ∧
      regrowOf owner le lsSource = (regrow, lsSource) ∧
      eachSampled regrow view le lsSource = (sampled, lsSampled) ∧
      emitDef (.constInt .i64 0) le lsSampled = (start, lsStart) ∧
      whenLive () (fun _ => do
        let (hb, params) ← newBlock [.data (.int .i64)]
        let counter := params.headD 0
        emitTerm (.br hb [start])
        setCur (some hb)
        lowerEach regrow owner sampled hb counter (fun depth exit => do
          let elem ← emitDef (.refElem view counter)
          let value ← eachElemValue x byRef elem
          lowerBlock (some ⟨depth, exit, .next hb .i64 counter⟩)
            (eachIRPre x idx value counter org) false body)) le lsStart = ((), ls') := by
  simp only [lowerStmt, bind_eq] at h
  obtain ⟨⟨owner, view⟩, lsSource, hSource, regrow, lsRegrow, hRegrow,
    sampled, lsSampled, hSampled, start, lsStart, hStart, hLive⟩ := h
  have hs := regrowOf_state owner le lsSource
  rw [hRegrow] at hs
  simp only at hs
  subst lsRegrow
  exact ⟨owner, view, lsSource, regrow, sampled, lsSampled, start, lsStart,
    hSource, hRegrow, hSampled, hStart, hLive⟩

structure EachInv (cfg : Cfg) (env : Env) (cx : FnCtx) (ls : LS)
    (counter view sampled : ValueId) (owner : Option ValueId) (vw : ViewVal)
    (base : Frame) (i : Nat) (fr : Frame) : Prop where
  values : Same counter base fr
  counterValue : fr.vals[counter]? = some (.val (.int .i64 i))
  viewValue : fr.vals[view]? = some (.view vw)
  ownerValue : vw.resizable = true → fr.vals[owner.getD 0]? = some (.val (.ref vw.loc))
  sampledValue : vw.resizable = false → fr.vals[sampled]? = some (.val (.int .i64 vw.len))
  rel : Rel cfg env cx fr ls

theorem EachInv.of_post {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls' : LS}
    {counter view sampled : ValueId} {owner : Option ValueId} {vw : ViewVal}
    {base fr fr' : Frame} {i : Nat} {pt : Pt} {cells : List (ValueId × RVal)}
    (hinv : EachInv cfg env cx ls counter view sampled owner vw base i fr)
    (P : Post cfg env cx ls fr ls' fr' pt cells)
    (hc : counter < ls.vals.size) (hv : view < counter)
    (ho : vw.resizable = true → owner.getD 0 < counter)
    (hs : vw.resizable = false → sampled < counter) :
    EachInv cfg env cx ls' counter view sampled owner vw base i fr' := by
  refine ⟨hinv.values.trans P.same (Nat.le_of_lt hc), ?_, ?_, ?_, ?_, P.rel⟩
  · rw [P.same counter hc]
    exact hinv.counterValue
  · rw [P.same view (Nat.lt_trans hv hc)]
    exact hinv.viewValue
  · intro hr
    rw [P.same (owner.getD 0) (Nat.lt_trans (ho hr) hc)]
    exact hinv.ownerValue hr
  · intro hr
    rw [P.same sampled (Nat.lt_trans (hs hr) hc)]
    exact hinv.sampledValue hr

theorem EachInv.reentry {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls' : LS}
    {counter view sampled : ValueId} {owner : Option ValueId} {vw : ViewVal}
    {base fr fr' : Frame} {i : Nat}
    (hinv : EachInv cfg env cx ls counter view sampled owner vw base i fr)
    (hsame : Same counter fr fr')
    (hcounter : fr'.vals[counter]? = some (.val (.int .i64 (i + 1 : Nat))))
    (hrel : Rel cfg env cx fr' ls') (hv : view < counter)
    (ho : vw.resizable = true → owner.getD 0 < counter)
    (hs : vw.resizable = false → sampled < counter) :
    EachInv cfg env cx ls' counter view sampled owner vw base (i + 1) fr' := by
  refine ⟨hinv.values.trans hsame (Nat.le_refl _), hcounter, ?_, ?_, ?_, hrel⟩
  · rw [hsame view hv]
    exact hinv.viewValue
  · intro hr
    rw [hsame (owner.getD 0) (ho hr)]
    exact hinv.ownerValue hr
  · intro hr
    rw [hsame sampled (hs hr)]
    exact hinv.sampledValue hr

theorem eachBack_goes (cx : FnCtx) (le : LEnv) (ls ls' : LS) (pt : Pt) (fr : Frame)
    (counter hb : ValueId) (i : Nat)
    (hback : rangeBack .i64 counter hb le ls = ((), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks)
    (hc : counter < ls.vals.size)
    (hcounter : fr.vals[counter]? = some (.val (.int .i64 i)))
    (hheader : ∃ block, cx.fn.blocks[hb]? = some block ∧
      block.params = [(counter, .data (.int .i64))]) :
    ∃ fr', Goes cx pt fr (hb, 0) fr' ∧ Same counter fr fr' ∧
      fr'.vals[counter]? = some (.val (.int .i64 (i + 1 : Nat))) ∧
      fr'.act = fr.act ∧ fr'.scopes = fr.scopes ∧ fr'.depth = fr.depth := by
  obtain ⟨_, hcur, _, _⟩ := LS.pp_some hpp
  rw [rangeBack, bind_run, isLive_run hcur] at hback
  simp only [ite_true, bind_eq] at hback
  obtain ⟨next, lsNext, hnext, hterm⟩ := hback
  have hextNext := hext.of_adv (adv_emitTerm hterm)
  obtain ⟨hnextId, _, _, hppNext, hnextInst⟩ := emitDef_facts hnext hpp hextNext
  obtain ⟨_, _, _, htermInst⟩ := emitTerm_facts hterm hppNext hext
  have hiNext : instAt cx.fn pt = some (.def next (.next .i64 counter)) := by
    rw [instAt_eq]
    exact hnextInst
  have hnextPure : execPure cx fr (.next .i64 counter) =
      pure (.val (.int .i64 (i + 1 : Nat))) := by
    simp [execPure, getVal_of hcounter, expectInt]
  have gnext := Goes.def_pure hiNext (by simp) hnextPure
  have hiTerm : instAt cx.fn (pt.1, pt.2 + 1) = some (.term (.br hb [next])) := by
    rw [instAt_eq]
    exact htermInst
  obtain ⟨block, hblock, hparams⟩ := hheader
  have gback := goes_br1 hiTerm hblock hparams (Frame.set_get fr next (.val (.int .i64 (i + 1 : Nat))))
  let after := (fr.set next (.val (.int .i64 (i + 1 : Nat)))).set counter
    (.val (.int .i64 (i + 1 : Nat)))
  refine ⟨after, gnext.trans gback, ?_, Frame.set_get _ _ _, rfl, rfl, rfl⟩
  have hnextBound : counter ≤ next := by rw [hnextId]; exact Nat.le_of_lt hc
  exact (Same.set fr hnextBound _).trans (Same.set _ (Nat.le_refl counter) _) (Nat.le_refl _)

theorem eachLen_inv_sim {cfg : Cfg} {env : Env} {cx : FnCtx} {le : LEnv}
    {ls ls' : LS} {counter view sampled result : ValueId} {owner : Option ValueId}
    {vw : ViewVal} {base fr : Frame} {i : Nat} {pt : Pt}
    (hinv : EachInv cfg env cx ls counter view sampled owner vw base i fr)
    (hc : counter < ls.vals.size) (hv : view < counter)
    (ho : vw.resizable = true → owner.getD 0 < counter)
    (hs : vw.resizable = false → sampled < counter)
    (hlow : eachLen vw.resizable owner sampled le ls = (result, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) :
    SimE cx pt fr (if vw.resizable then lengthLoc vw.loc else pure vw.len)
      (fun len pt' fr' => Post cfg env cx ls fr ls' fr' pt' [(result, .val (.int .i64 len))] ∧
        EachInv cfg env cx ls' counter view sampled owner vw base i fr') := by
  cases hr : vw.resizable
  · simp only [hr, Bool.false_eq_true, ite_false] at hlow ⊢
    exact (eachLen_sampled_sim (hinv.sampledValue hr) (Nat.lt_trans (hs hr) hc)
      hlow hpp hinv.rel).mono (fun _ _ _ P => ⟨P, hinv.of_post P hc hv ho hs⟩)
  · simp only [hr, ite_true] at hlow ⊢
    exact (eachLen_grow_sim (hinv.ownerValue hr) hlow hpp hext hinv.rel).mono
      (fun _ _ _ P => ⟨P, hinv.of_post P hc hv ho hs⟩)

theorem lowerEach_branch_sim (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv)
    (ls lsLen lsCmp lsf lsBody lsBodyEnd lsBack ls' : LS)
    (counter view sampled len cmp hb tb xb : Nat) (owner : Option ValueId)
    (vw : ViewVal) (base : Frame) (body : Nat → BlockId → B ValueId) (rBody : ValueId)
    (hLen : eachLen vw.resizable owner sampled le ls = (len, lsLen))
    (hCmp : emitDef (.cmp .lt .i64 counter len) le lsLen = (cmp, lsCmp))
    (hFork : fork cmp le lsCmp = ((tb, xb), lsf))
    (hBodyState : lsBody = { lsf with cur := some tb })
    (hBody : body lsCmp.stack.length xb le lsBody = (rBody, lsBodyEnd))
    (hBodyAdv : lsBody.Adv lsBodyEnd)
    (hBack : rangeBack .i64 counter hb le lsBodyEnd = ((), lsBack))
    (hExit : ls' = { lsBack with cur := some xb })
    (hpp : ls.pp = some (hb, 0)) (hext : ExtT ls' cx.fn.blocks)
    (hc : counter < ls.vals.size) (hv : view < counter)
    (ho : vw.resizable = true → owner.getD 0 < counter)
    (hs : vw.resizable = false → sampled < counter) :
    EachBranch cx vw (hb, 0) (tb, 0)
      (EachInv cfg env cx ls counter view sampled owner vw base)
      (EachInv cfg env cx lsBody counter view sampled owner vw base)
      (fun flow pt' fr' => flow = .normal .unit ∧ ls'.pp = some pt' ∧
        Same counter base fr' ∧ Rel cfg env cx fr' ls') := by
  have aBack := advB_rangeBack .i64 counter hb le lsBodyEnd () lsBack hBack
  have hextBack : ExtT lsBack cx.fn.blocks := by simpa [hExit, ExtT] using hext
  have hextBody := (hextBack.of_adv aBack).of_adv hBodyAdv
  have hextFork : ExtT lsf cx.fn.blocks := by simpa [hBodyState, ExtT] using hextBody
  have aLen := advB_eachLen vw.resizable owner sampled le ls len lsLen hLen
  have aCmp := adv_emitDef hCmp
  obtain ⟨_, hcur, _, _⟩ := LS.pp_some hpp
  have hcurLen : lsLen.cur = some hb := by
    cases hr : vw.resizable <;> simp only [eachLen, hr, Bool.false_eq_true, ite_false, ite_true] at hLen
    · rw [pure_run] at hLen
      have he := (Prod.mk.inj hLen).2
      simpa [← he] using hcur
    · rw [emitDef_run _ le hcur] at hLen
      have he := (Prod.mk.inj hLen).2
      simpa using (congrArg LS.cur he).symm.trans hcur
  have hcurCmp : lsCmp.cur = some hb := by
    rw [emitDef_run _ le hcurLen] at hCmp
    have he := (Prod.mk.inj hCmp).2
    simpa using (congrArg LS.cur he).symm.trans hcurLen
  have aFork := adv_fork hcurCmp hFork
  have hextCmp := hextFork.of_adv aFork
  have hextLen := hextCmp.of_adv aCmp
  intro i fr hinv
  have heq : (if vw.resizable then lengthLoc vw.loc else pure vw.len) =
      ((if vw.resizable then lengthLoc vw.loc else pure vw.len) >>= fun n => pure n) := by
    simp
  rw [heq]
  refine SimE.bind (eachLen_inv_sim hinv hc hv ho hs hLen hpp hextLen)
    fun length ptLen frLen hlen => ?_
  obtain ⟨P, hinvLen⟩ := hlen
  have hcounter := hinvLen.counterValue
  have hlength : frLen.vals[len]? = some (.val (.int .i64 length)) := P.has (len, _) (by simp)
  have hop : execPure cx frLen (.cmp .lt .i64 counter len) =
      pure (.val (.bool ((i : Int) < (length : Int)))) := by
    have h := (execPure_cmp (cx := cx) (fr := frLen) (op := .lt) hcounter hlength).1 IntTy.i64
    rw [h]
    simp [expectComparable, expectSameTy, evalCmp]
  have hcmpSim := leaf_def (c := pure ()) P hCmp hextCmp (by simp)
    (fun _ => RVal.val (.bool ((i : Int) < (length : Int)))) (by simpa using hop)
  have hunit : (pure length : M Nat) = (pure () >>= fun _ => pure length) := by simp
  rw [hunit]
  refine SimE.bind (SimE.of_simG hcmpSim) fun _ ptCmp frCmp PCmp => ?_
  have hinvCmp := hinv.of_post PCmp hc hv ho hs
  obtain ⟨hcmpId, _, hcmpStack, hppCmp, _⟩ := emitDef_facts hCmp P.pp hextCmp
  obtain ⟨htb, hxb, _, hvalsFork, hstackFork, _, hterm, htb0, hxb0⟩ :=
    fork_facts hFork hppCmp hextFork
  obtain ⟨Ttb, hTtb, hTtbp⟩ := hextFork.params htb0
  obtain ⟨Txb, hTxb, hTxbp⟩ := hextFork.params hxb0
  have hinst : instAt cx.fn ptCmp = some (.term (.condbr cmp tb [] xb [])) := by
    rw [instAt_eq]
    have hpoint : ptCmp = (ptLen.1, ptLen.2 + 1) := Option.some.inj (PCmp.pp.symm.trans hppCmp)
    rw [hpoint]
    exact hterm
  have htest : frCmp.vals[cmp]? = some (.val (.bool ((i : Int) < (length : Int)))) :=
    PCmp.has (cmp, _) (by simp)
  by_cases hlt : i < length
  · simp only [hlt, ite_true]
    have htestTrue : frCmp.vals[cmp]? = some (.val (.bool true)) := by simpa [hlt] using htest
    have hgo := goes_condbr_then0 hinst htestTrue hTtb hTtbp rfl
    refine SimE.goes hgo (SimE.ret ?_)
    simp only [hlt, ite_true]
    exact ⟨by trivial, { hinvCmp with rel := hinvCmp.rel.stack_eq (by rw [hBodyState]; exact hstackFork) }⟩
  · simp only [hlt, ite_false]
    have htestFalse : frCmp.vals[cmp]? = some (.val (.bool false)) := by simpa [hlt] using htest
    have hgo := goes_condbr_else0 hinst htestFalse hTxb hTxbp rfl
    have hxbBack : lsBack.blocks[xb]? = some ⟨[], #[]⟩ := by
      refine (hBodyAdv.trans aBack).keep xb ⟨[], #[]⟩ ?_ ?_
      · rw [hBodyState]
        intro he
        have hb : tb = xb := Option.some.inj he
        nat_omega
      · rw [hBodyState]
        exact hxb0
    have hppOut : ls'.pp = some (xb, 0) := by rw [hExit]; exact LS.pp_cur hxbBack
    have hstackOut : ls'.stack = lsCmp.stack := by
      rw [hExit]
      exact aBack.stack.trans (hBodyAdv.stack.trans (by rw [hBodyState]; exact hstackFork))
    refine SimE.goes hgo (SimE.ret ?_)
    simp only [hlt, ite_false]
    exact ⟨by trivial, hppOut, hinvCmp.values, hinvCmp.rel.stack_eq hstackOut⟩

theorem lowerEach_sim (n : Nat) (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv)
    (ls ls' : LS) (counter view sampled hb : ValueId) (owner : Option ValueId)
    (vw : ViewVal) (base : Frame) (x : VarId) (idx : Option VarId) (byRef : Bool)
    (block : Core.Block) (body : Nat → BlockId → B ValueId)
    (post : Flow → Pt → Frame → Prop)
    (hlow : lowerEach vw.resizable owner sampled hb counter body le ls = ((), ls'))
    (hadv : ∀ d xb, AdvB (body d xb))
    (hpp : ls.pp = some (hb, 0)) (hext : ExtT ls' cx.fn.blocks)
    (hc : counter < ls.vals.size) (hv : view < counter)
    (ho : vw.resizable = true → owner.getD 0 < counter)
    (hs : vw.resizable = false → sampled < counter)
    (hexit : ∀ pt fr, ls'.pp = some pt → Same counter base fr → Rel cfg env cx fr ls' →
      post (.normal .unit) pt fr)
    (hbody : ∀ d xb input result output back tb,
      body d xb le input = (result, output) → input.pp = some (tb, 0) →
      rangeBack .i64 counter hb le output = ((), back) → ExtT back cx.fn.blocks →
      ExtT output cx.fn.blocks → counter < input.vals.size → input.stack = ls.stack →
      d = input.stack.length → ls'.pp = some (xb, 0) →
      (∃ block, cx.fn.blocks[xb]? = some block ∧ block.params = []) →
      ∀ fuel, fuel < n → EachBodyAt fuel cx cfg env x idx byRef block vw (hb, 0) (tb, 0)
        (EachInv cfg env cx ls counter view sampled owner vw base)
        (EachInv cfg env cx input counter view sampled owner vw base) post) :
    ∀ i fr, EachInv cfg env cx ls counter view sampled owner vw base i fr →
      SimE cx (hb, 0) fr (execEach n cfg env x idx byRef block vw i >>= prepareReturn env) post := by
  obtain ⟨len, lsLen, cmp, lsCmp, tb, xb, lsf, input, result, output, lsBack,
    hLen, hCmp, hFork, hInput, hBody, hBack, hExit⟩ := lowerEach_unfold hlow
  have aBody := hadv lsCmp.stack.length xb le input result output hBody
  have aBack := advB_rangeBack .i64 counter hb le output () lsBack hBack
  have hextBack : ExtT lsBack cx.fn.blocks := by simpa [hExit, ExtT] using hext
  have hextOutput := hextBack.of_adv aBack
  have hextInput := hextOutput.of_adv aBody
  have hextFork : ExtT lsf cx.fn.blocks := by simpa [hInput, ExtT] using hextInput
  have hbranch := lowerEach_branch_sim cfg env cx le ls lsLen lsCmp lsf input output lsBack ls'
    counter view sampled len cmp hb tb xb owner vw base body result
    hLen hCmp hFork hInput hBody aBody hBack hExit hpp hext hc hv ho hs
  have hbranch' : EachBranch cx vw (hb, 0) (tb, 0)
      (EachInv cfg env cx ls counter view sampled owner vw base)
      (EachInv cfg env cx input counter view sampled owner vw base) post := by
    intro i fr hinv
    exact (hbranch i fr hinv).mono fun length pt' fr' h => by
      by_cases hi : i < length
      · simpa only [hi, ite_true] using h
      · simp only [hi, ite_false] at h ⊢
        exact hexit pt' fr' h.2.1 h.2.2.1 h.2.2.2
  have aLen := advB_eachLen vw.resizable owner sampled le ls len lsLen hLen
  have aCmp := adv_emitDef hCmp
  obtain ⟨block0, hcur, hlookup, _⟩ := LS.pp_some hpp
  have hcurLen : lsLen.cur = some hb := by
    cases hr : vw.resizable <;> simp only [eachLen, hr, Bool.false_eq_true, ite_false, ite_true] at hLen
    · rw [pure_run] at hLen
      have he := (Prod.mk.inj hLen).2
      simpa [← he] using hcur
    · rw [emitDef_run _ le hcur] at hLen
      have he := (Prod.mk.inj hLen).2
      simpa using (congrArg LS.cur he).symm.trans hcur
  have hcurCmp : lsCmp.cur = some hb := by
    rw [emitDef_run _ le hcurLen] at hCmp
    have he := (Prod.mk.inj hCmp).2
    simpa using (congrArg LS.cur he).symm.trans hcurLen
  obtain ⟨blockCmp, hlookupCmp, _, _, _⟩ := (aLen.trans aCmp).ext.2 hb block0 hlookup
  have hextCmp := hextFork.of_adv (adv_fork hcurCmp hFork)
  have hfacts := fork_facts hFork (LS.pp_eq hcurCmp hlookupCmp) hextFork
  have hppInput : input.pp = some (tb, 0) := by
    rw [hInput]
    exact LS.pp_cur hfacts.2.2.2.2.2.2.2.1
  have hcounterInput : counter < input.vals.size := by
    rw [hInput]
    change counter < lsf.vals.size
    rw [hfacts.2.2.2.1]
    exact Nat.lt_of_lt_of_le hc (aLen.trans aCmp).vals
  have hstackInput : input.stack = ls.stack := by
    rw [hInput]
    exact hfacts.2.2.2.2.1.trans (aCmp.stack.trans aLen.stack)
  have hdepth : lsCmp.stack.length = input.stack.length := by
    rw [hInput]
    exact congrArg List.length hfacts.2.2.2.2.1.symm
  have hxbBack : lsBack.blocks[xb]? = some ⟨[], #[]⟩ := by
    refine (aBody.trans aBack).keep xb ⟨[], #[]⟩ ?_ ?_
    · rw [hInput]
      intro he
      have hb : tb = xb := Option.some.inj he
      have hids := fork_ids hFork
      have hpair := hids.1
      have ht := (Prod.mk.inj hpair).1
      have hx := (Prod.mk.inj hpair).2
      nat_omega
    · rw [hInput]
      exact hfacts.2.2.2.2.2.2.2.2
  have hppExit : ls'.pp = some (xb, 0) := by rw [hExit]; exact LS.pp_cur hxbBack
  obtain ⟨exitBlock, hExitBlock, hExitParams⟩ := hextBack.params hxbBack
  exact each_sim_bounded n cx cfg env x idx byRef block vw (hb, 0) (tb, 0)
    _ _ post hbranch' (hbody lsCmp.stack.length xb input result output lsBack tb hBody hppInput
      hBack hextBack hextOutput hcounterInput hstackInput hdepth hppExit
      ⟨exitBlock, hExitBlock, hExitParams⟩)

def eachBodyBuilder (x : VarId) (idx : Option VarId) (byRef : Bool) (block : Core.Block)
    (org : OriginId) (view counter hb : ValueId) (depth : Nat) (exit : BlockId) : B ValueId := do
  let elem ← emitDef (.refElem view counter)
  let value ← eachElemValue x byRef elem
  lowerBlock (some ⟨depth, exit, .next hb .i64 counter⟩)
    (eachIRPre x idx value counter org) false block

theorem lowerEach_normal_sim (n : Nat) (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv)
    (ls ls' : LS) (counter view sampled hb : ValueId) (owner : Option ValueId)
    (vw : ViewVal) (base : Frame) (x : VarId) (idx : Option VarId) (byRef : Bool)
    (block : Core.Block) (org : OriginId) (hok : blockOk block = true)
    (hscope : (∃ lv, env.vars[x]? = some lv ∧ lv.scope = block.scope) ∧
      (∀ j, idx = some j → ∃ lv, env.vars[j]? = some lv ∧ lv.scope = block.scope))
    (hlow : lowerEach vw.resizable owner sampled hb counter
      (eachBodyBuilder x idx byRef block org view counter hb) le ls = ((), ls'))
    (hpp : ls.pp = some (hb, 0)) (hext : ExtT ls' cx.fn.blocks)
    (hheader : ∃ header, cx.fn.blocks[hb]? = some header ∧
      header.params = [(counter, .data (.int .i64))])
    (hc : counter < ls.vals.size) (hv : view < counter)
    (ho : vw.resizable = true → owner.getD 0 < counter)
    (hs : vw.resizable = false → sampled < counter) :
    ∀ i fr, EachInv cfg env cx ls counter view sampled owner vw base i fr →
      SimE cx (hb, 0) fr (execEach n cfg env x idx byRef block vw i >>= prepareReturn env)
        (fun flow pt' fr' => flow = .normal .unit ∧ ls'.pp = some pt' ∧
          Same counter base fr' ∧ Rel cfg env cx fr' ls') := by
  apply lowerEach_sim n cfg env cx le ls ls' counter view sampled hb owner vw base x idx byRef block
    (eachBodyBuilder x idx byRef block org view counter hb) _ hlow
  · intro depth exit
    unfold eachBodyBuilder
    exact AdvB.bind (advB_emitDef _) fun elem =>
      AdvB.bind (advB_eachElemValue x byRef elem) fun value => advB_lowerBlock _ _ _ block
  · exact hpp
  · exact hext
  · exact hc
  · exact hv
  · exact ho
  · exact hs
  · intro pt fr hp hv hr
    exact ⟨rfl, hp, hv, hr⟩
  · intro depth exit input result output back tb hbodyLow hppInput hBack hextBack
      hextOutput hcounterInput hstackInput _ _ _ fuel _ i fr hinv
    unfold eachBodyBuilder at hbodyLow
    simp only [bind_eq] at hbodyLow
    obtain ⟨elem, withElem, hElem, value, withValue, hValue, hBlock⟩ := hbodyLow
    have aBlock := advB_lowerBlock (some ⟨depth, exit, .next hb .i64 counter⟩)
      (eachIRPre x idx value counter org) false block le withValue result output hBlock
    have aValue := advB_eachElemValue x byRef elem le withElem value withValue hValue
    have aElem := adv_emitDef hElem
    have hstackOutput : ls.stack = output.stack :=
      hstackInput.symm.trans ((aElem.trans (aValue.trans aBlock)).stack.symm)
    refine eachIteration_sim fuel cfg env cx le input withElem withValue output fr (tb, 0)
      view counter elem value result vw i x idx byRef block
      ⟨depth, exit, .next hb .i64 counter⟩ org _ hElem hValue hBlock hppInput hextOutput
      hinv.rel hinv.viewValue hinv.counterValue hcounterInput ?_
    intro ev ptValue frValue PValue hpre
    have hscopePre : ∀ p ∈ eachIRPre x idx value counter org,
        ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = block.scope := by
      intro p hp
      cases hi : idx with
      | none =>
        simp only [eachIRPre, hi, List.mem_singleton] at hp
        subst p
        exact hscope.1
      | some j =>
        simp only [eachIRPre, hi, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact hscope.1
        · exact hscope.2 j hi
    have hclaim := blockPreClaim fuel (some ⟨depth, exit, .next hb .i64 counter⟩)
      (eachIRPre x idx value counter org) (eachCorePre x idx ev i) false block cfg env hok hscopePre
      le withValue result output ptValue cx frValue hBlock PValue.pp hextOutput PValue.rel hpre
    refine SimE.bind (SimE.of_simG hclaim) fun flow ptBody frBody hresult => ?_
    obtain ⟨v, rfl, _, PBlock⟩ := hresult
    have P := PValue.comp PBlock
    have hinvBody := hinv.of_post P hcounterInput hv ho hs
    have hcounterBody : counter < output.vals.size := Nat.lt_of_lt_of_le hcounterInput P.mono
    obtain ⟨frHeader, hgo, hsame, hcell, hact, hscopes, hdepth⟩ := eachBack_goes cx le output back
      ptBody frBody counter hb i hBack PBlock.pp hextBack hcounterBody hinvBody.counterValue hheader
    have hrelHeader : Rel cfg env cx frHeader ls :=
      ⟨hinvBody.rel.prof, hinvBody.rel.slots, hact.trans hinvBody.rel.act,
        hscopes.trans hinvBody.rel.scopes, hdepth.trans hinvBody.rel.depth,
        hstackOutput.trans hinvBody.rel.stack⟩
    exact SimE.ret ⟨frHeader, hinvBody.reentry hsame hcell hrelHeader hv ho hs, hgo⟩

end Goose.Lower
