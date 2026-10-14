import Goose.Lower.Eventual
import Goose.Lower.Claims
import Goose.Lower.Return
import Goose.Core.Sound.Invert

namespace Goose.Lower

open Goose.Core Goose.GIR

def EachSourceCells (owner : Option ValueId) (view : ValueId) (vw : ViewVal) :
    List (ValueId × RVal) :=
  (view, .view vw) :: owner.toList.map (fun r => (r, .val (.ref vw.loc)))

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

def EachBody (cx : FnCtx) (cfg : Cfg) (env : Env) (x : VarId) (idx : Option VarId)
    (byRef : Bool) (block : Core.Block) (vw : ViewVal) (header body : Pt)
    (headerInv bodyInv : Nat → Frame → Prop) (post : Flow → Pt → Frame → Prop) : Prop :=
  ∀ n i fr, bodyInv i fr →
    SimE cx body fr
      ((if byRef then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
        else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) >>= fun ev =>
      execBlock n cfg env ((x, ev) :: (match idx with
        | some j => [(j, Val.int .i64 i)] | none => [])) block >>= prepareReturn env)
      (fun flow pt' fr' => match flow with
        | .normal _ | .cont => ∃ frh, headerInv (i + 1) frh ∧ Goes cx pt' fr' header frh
        | .brk => post (.normal .unit) pt' fr'
        | .ret value => post (.ret value) pt' fr')

theorem each_sim (cx : FnCtx) (cfg : Cfg) (env : Env) (x : VarId) (idx : Option VarId)
    (byRef : Bool) (block : Core.Block) (vw : ViewVal) (header body : Pt)
    (headerInv bodyInv : Nat → Frame → Prop) (post : Flow → Pt → Frame → Prop)
    (hbranch : EachBranch cx vw header body headerInv bodyInv post)
    (hbody : EachBody cx cfg env x idx byRef block vw header body headerInv bodyInv post) :
    ∀ n i fr, headerInv i fr →
      SimE cx header fr (execEach n cfg env x idx byRef block vw i >>= prepareReturn env) post := by
  intro n
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
      refine SimE.bind (hbody n i fr1 hinvBody) fun flow pt2 fr2 hflow => ?_
      cases flow with
      | normal value | cont =>
        obtain ⟨frh, hinvh, hgo⟩ := hflow
        exact SimE.goes hgo (ih (i + 1) frh hinvh)
      | brk => exact SimE.ret hflow
      | ret value => exact SimE.ret hflow
    · simp only [hi, ite_false] at hlen ⊢
      exact SimE.ret hlen

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

end Goose.Lower
