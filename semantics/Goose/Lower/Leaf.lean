import Goose.Lower.Sim

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem checkCapacityAtOrg_some (l : Loc) (count : Nat) (org : OriginId) :
    checkCapacityAtOrg l count (some org) = checkAppendCapacity l count org := by
  funext s
  cases hread : readLoc l s with
  | stop err state => simp [checkCapacityAtOrg, checkAppendCapacity, hread, bind_apply]
  | ok value state =>
    cases value <;>
      simp [checkCapacityAtOrg, checkAppendCapacity, hread, abortAtOrg, abortAt,
        M.stop, bind_apply, pure_apply, M.instMonad, M.bind', M.pure']

def BndSpec (len : Nat) (dflt : Int) : Bnd → Int → List (ValueId × RVal) → Prop
  | .omitted, k, cells => k = dflt ∧ cells = []
  | .val v, k, cells => ∃ t, cells = [(v, .val (.int t k))]
  | .fromEnd v, k, cells => ∃ t kk, k = (len : Int) - kk ∧ cells = [(v, .val (.int t kk))]

theorem evalBnd_of_spec {fr : Frame} {len : Nat} {dflt : Int} {bnd : Bnd} {k : Int}
    {cells : List (ValueId × RVal)} (hs : BndSpec len dflt bnd k cells)
    (hc : ∀ p ∈ cells, fr.vals[p.1]? = some p.2) : evalBnd fr len dflt bnd = pure k := by
  cases bnd with
  | omitted => obtain ⟨rfl, -⟩ := hs; rfl
  | val v =>
    obtain ⟨t, rfl⟩ := hs
    have := hc (v, .val (.int t k)) (by simp)
    simp only [evalBnd, getVal_of this, Goose.Core.expectInt, pure_bind]
  | fromEnd v =>
    obtain ⟨t, kk, rfl, rfl⟩ := hs
    have := hc (v, .val (.int t kk)) (by simp)
    simp only [evalBnd, getVal_of this, Goose.Core.expectInt, pure_bind]

theorem Post.init {cfg : Cfg} {env : Env} {cx : FnCtx} {ls : LS} {fr : Frame} {pt : Pt}
    (hrel : Rel cfg env cx fr ls) (hpp : ls.pp = some pt) : Post cfg env cx ls fr ls fr pt [] :=
  ⟨hpp, by simp, by simp, Nat.le_refl _, Same.refl _ _, hrel⟩


theorem Post.nil {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls' : LS} {fr fr' : Frame} {pt' : Pt}
    (hpp : ls'.pp = some pt') (hmono : ls.vals.size ≤ ls'.vals.size) (hsame : Same ls.vals.size fr fr')
    (hrel : Rel cfg env cx fr' ls') : Post cfg env cx ls fr ls' fr' pt' [] :=
  ⟨hpp, by simp, by simp, hmono, hsame, hrel⟩

theorem Post.comp {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls1 ls2 : LS} {fr fr1 fr2 : Frame}
    {pt1 pt2 : Pt} {c1 c2 : List (ValueId × RVal)}
    (h1 : Post cfg env cx ls fr ls1 fr1 pt1 c1) (h2 : Post cfg env cx ls1 fr1 ls2 fr2 pt2 c2) :
    Post cfg env cx ls fr ls2 fr2 pt2 (c1 ++ c2) := by
  refine ⟨h2.pp, fun p hp => ?_, fun p hp => ?_, Nat.le_trans h1.mono h2.mono,
    h1.same.trans h2.same h1.mono, h2.rel⟩
  · rcases List.mem_append.mp hp with hp | hp
    · rw [h2.same p.1 (h1.lt p hp)]
      exact h1.has p hp
    · exact h2.has p hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact Nat.lt_of_lt_of_le (h1.lt p hp) h2.mono
    · exact h2.lt p hp

theorem Post.sub {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls' : LS} {fr fr' : Frame} {pt : Pt}
    {cells cells' : List (ValueId × RVal)} (h : Post cfg env cx ls fr ls' fr' pt cells)
    (hsub : ∀ p ∈ cells', p ∈ cells) : Post cfg env cx ls fr ls' fr' pt cells' :=
  ⟨h.pp, fun p hp => h.has p (hsub p hp), fun p hp => h.lt p (hsub p hp), h.mono, h.same, h.rel⟩

theorem Post.has_mem {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls' : LS} {fr fr' : Frame} {pt : Pt}
    {cells : List (ValueId × RVal)} (h : Post cfg env cx ls fr ls' fr' pt cells)
    {i : ValueId} {x : RVal} (hm : (i, x) ∈ cells) : fr'.vals[i]? = some x := h.has (i, x) hm


theorem leaf_def {cfg : Cfg} {env : Env} {cx : FnCtx} {ls lsk ls1 : LS} {fr frk : Frame}
    {ptk : Pt} {cellsk : List (ValueId × RVal)}
    (hP : Post cfg env cx ls fr lsk frk ptk cellsk) {op : Op} {le : LEnv} {r : ValueId}
    (h : emitDef op le lsk = (r, ls1)) (hext : ExtT ls1 cx.fn.blocks)
    (hnc : ∀ f a o, op ≠ .call f a o) {α : Type} {c : M α} (inj : α → RVal)
    (hx : execPure cx frk op = c >>= fun a => pure (inj a)) :
    SimG cx ptk frk c (fun a pt' fr' => Post cfg env cx ls fr ls1 fr' pt' [(r, inj a)]) := by
  have hi : instAt cx.fn ptk = some (.def r op) := (Post.def_leaf hP h hext (.val .unit)).2
  refine (SimG.def_step (r := r) inj hi hnc hx).mono fun a pt' fr' ⟨hpt, hfr⟩ => ?_
  subst hpt; subst hfr
  exact (Post.def_leaf hP h hext (inj a)).1


theorem leaf_def_keep {cfg : Cfg} {env : Env} {cx : FnCtx} {ls lsk ls1 : LS} {fr frk : Frame}
    {ptk : Pt} {cellsk : List (ValueId × RVal)}
    (hP : Post cfg env cx ls fr lsk frk ptk cellsk) {op : Op} {le : LEnv} {r : ValueId}
    (h : emitDef op le lsk = (r, ls1)) (hext : ExtT ls1 cx.fn.blocks)
    (hnc : ∀ f a o, op ≠ .call f a o) {α : Type} {c : M α} (inj : α → RVal)
    (hx : execPure cx frk op = c >>= fun a => pure (inj a)) :
    SimG cx ptk frk c (fun a pt' fr' => Post cfg env cx ls fr ls1 fr' pt' ((r, inj a) :: cellsk)) := by
  have hi : instAt cx.fn ptk = some (.def r op) := (Post.def_leaf_keep hP h hext (.val .unit)).2
  refine (SimG.def_step (r := r) inj hi hnc hx).mono fun a pt' fr' ⟨hpt, hfr⟩ => ?_
  subst hpt; subst hfr
  exact (Post.def_leaf_keep hP h hext (inj a)).1

theorem slots_get {cfg : Cfg} {env : Env} {cx : FnCtx} {fr : Frame} {ls : LS}
    (hrel : Rel cfg env cx fr ls) (x : Nat) :
    cx.fn.slots[x]? = env.vars[x]?.map fun lv => (⟨lv.ty, lv.kind, lv.scope, x⟩ : Slot) := by
  rw [hrel.slots]
  simp [Array.getElem?_mapIdx]

theorem slotRoot_eq {cfg : Cfg} {env : Env} {cx : FnCtx} {fr : Frame} {ls : LS}
    (hrel : Rel cfg env cx fr ls) (x : Nat) : slotRoot cx.fn fr x = rootOf env x := by
  unfold slotRoot rootOf
  rw [slots_get hrel x]
  cases env.vars[x]? with
  | none => rfl
  | some lv =>
    simp only [Option.map_some, hrel.scopes, hrel.act]
    cases List.lookup lv.scope env.scopes <;> rfl

theorem Post.eff_leaf {cfg : Cfg} {env : Env} {cx : FnCtx} {ls lsk ls1 : LS} {fr frk : Frame}
    {ptk : Pt} {cellsk : List (ValueId × RVal)}
    (hP : Post cfg env cx ls fr lsk frk ptk cellsk) {e : Effect} {le : LEnv}
    (h : emitEffect e le lsk = ((), ls1)) (hext : ExtT ls1 cx.fn.blocks) :
    Post cfg env cx ls fr ls1 frk (ptk.1, ptk.2 + 1) [] ∧ instAt cx.fn ptk = some (.eff e) := by
  obtain ⟨hv, hst, hpp, hi⟩ := emitEffect_facts h hP.pp hext
  have hm := hP.mono
  exact ⟨⟨hpp, by simp, by simp, by nat_omega, hP.same, hP.rel.stack_eq hst⟩, hi⟩


theorem leaf_eff {cfg : Cfg} {env : Env} {cx : FnCtx} {ls lsk ls1 : LS} {fr frk : Frame}
    {ptk : Pt} {cellsk : List (ValueId × RVal)}
    (hP : Post cfg env cx ls fr lsk frk ptk cellsk) {e : Effect} {le : LEnv}
    (h : emitEffect e le lsk = ((), ls1)) (hext : ExtT ls1 cx.fn.blocks)
    {α β : Type} {c : M β} {c0 : M α} (a0 : β) (hc : c = c0 >>= fun _ => pure a0)
    (hx : execEff cx.fn frk e = c0 >>= fun _ => pure frk) :
    SimG cx ptk frk c (fun a pt' fr' => a = a0 ∧ Post cfg env cx ls fr ls1 fr' pt' []) := by
  subst hc
  obtain ⟨hP', hi⟩ := Post.eff_leaf hP h hext
  refine SimG.bind (SimG.eff_step (fun _ => frk) hi hx) fun _ pt' fr' ⟨hpt, hfr⟩ => ?_
  subst hpt; subst hfr
  exact SimG.ret ⟨rfl, hP'⟩


def cellsOf : List ValueId → List Val → List (ValueId × RVal)
  | r :: rs, v :: vs => (r, .val v) :: cellsOf rs vs
  | _, _ => []

theorem mapList_getVal_cells {fr : Frame} : ∀ {rs : List ValueId} {vs : List Val},
    rs.length = vs.length → (∀ p ∈ cellsOf rs vs, fr.vals[p.1]? = some p.2) →
    mapList (getVal fr) rs = pure vs
  | [], [], _, _ => rfl
  | r :: rs, v :: vs, hl, hc => by
    have h1 : fr.vals[r]? = some (.val v) := hc (r, .val v) (by simp [cellsOf])
    have h2 := mapList_getVal_cells (fr := fr) (rs := rs) (vs := vs) (by simpa using hl)
      (fun p hp => hc p (by simp [cellsOf, hp]))
    simp only [mapList, getVal_of h1, pure_bind, h2]
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)


theorem lowerExpr_call_split {c : ContextId} {args : List Arg} {org : OriginId}
    {le : LEnv} {ls ls' : LS} {r : ValueId}
    (h : lowerExpr (.call c args org) le ls = (r, ls')) :
    ∃ ids middle after,
      lowerArgs args le ls = (ids, middle) ∧
      emitDef (.call c ids (some org)) le middle =
        (r, after) ∧
      ((le.mod.noReturn c = true ∧ emitTerm .unreachable le after = ((), ls')) ∨
        (le.mod.noReturn c = false ∧ ls' = after)) := by
  simp only [lowerExpr, bind_eq] at h
  obtain ⟨ids, middle, ha, id, after, hd, reader, same, hr, ht⟩ := h
  rw [read_apply] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
  by_cases hn : le.mod.noReturn c = true
  · rw [ite_eq_left hn] at ht
    obtain ⟨u, last, hterm, hpure⟩ := bind_eq.mp ht
    rw [pure_run] at hpure
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpure
    exact ⟨ids, middle, after, ha, hd, Or.inl ⟨hn, by cases u; exact hterm⟩⟩
  · rw [ite_eq_right hn, pure_run] at ht
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj ht
    exact ⟨ids, middle, after, ha, hd, Or.inr ⟨Bool.eq_false_iff.mpr hn, rfl⟩⟩


theorem releaseSlots_eq {fn : Func} {vars : Array LocalVar}
    (hs : fn.slots = vars.mapIdx fun i lv => (⟨lv.ty, lv.kind, lv.scope, i⟩ : Slot))
    (act : ActId) (sc : Nat) (si : ScopeInst) :
    ∀ (n : Nat) (st : Store), releaseSlots fn act sc si n st = releaseVars vars act sc si n st
  | 0, st => rfl
  | n + 1, st => by
    simp only [releaseSlots, releaseVars, hs, Array.getElem?_mapIdx]
    cases vars[n]? with
    | none => exact releaseSlots_eq hs act sc si n st
    | some lv => simpa using releaseSlots_eq hs act sc si n _

theorem releaseScope_eq {cfg : Cfg} {env : Env} {cx : FnCtx} {fr : Frame} {ls : LS}
    (hrel : Rel cfg env cx fr ls) (sc : Nat) (si : ScopeInst) :
    GIR.releaseScope cx.fn fr.act sc si = Core.releaseScope env sc si := by
  funext s
  have hsz : cx.fn.slots.size = env.vars.size := by rw [hrel.slots]; simp
  simp only [GIR.releaseScope, Core.releaseScope, hrel.act, hsz]
  rw [releaseSlots_eq hrel.slots]

theorem block_enter {cfg : Cfg} {env : Env} {cx : FnCtx} {ls ls1 : LS} {fr : Frame} {pt : Pt}
    {le : LEnv} {sc : ScopeId} (hpp : ls.pp = some pt) (h : emitEffect (.enter sc) le ls = ((), ls1))
    (hext : ExtT ls1 cx.fn.blocks) (hrel : Rel cfg env cx fr ls) :
    SimG cx pt fr freshScope (fun si pt1 fr1 =>
      ls1.pp = some pt1 ∧ ls1.vals.size = ls.vals.size ∧ fr1.vals = fr.vals ∧
      Rel cfg { env with scopes := (sc, si) :: env.scopes } cx fr1 { ls1 with stack := sc :: ls1.stack }) := by
  obtain ⟨hv, hst, hpp1, hi⟩ := emitEffect_facts h hpp hext
  have hx : execEff cx.fn fr (.enter sc) =
      freshScope >>= fun si => pure ({ fr with scopes := (sc, si) :: fr.scopes } : Frame) := rfl
  refine (SimG.eff_step (fun si => { fr with scopes := (sc, si) :: fr.scopes }) hi hx).mono
    fun si pt1 fr1 ⟨hpt, hfr⟩ => ?_
  subst hpt; subst hfr
  refine ⟨hpp1, hv, rfl, ?_⟩
  exact ⟨hrel.prof, hrel.slots, hrel.act, by simp [hrel.scopes], hrel.depth, by simp [hst, hrel.stack]⟩

theorem block_leave {cfg : Cfg} {env : Env} {cx : FnCtx} {lsk ls_l : LS} {frk : Frame} {ptk : Pt}
    {le : LEnv} {sc : ScopeId} {si : ScopeInst} (hpp : lsk.pp = some ptk)
    (h : emitEffect (.leave sc) le lsk = ((), ls_l)) (hext : ExtT ls_l cx.fn.blocks)
    (hrel : Rel cfg { env with scopes := (sc, si) :: env.scopes } cx frk lsk) :
    SimG cx ptk frk (Core.releaseScope env sc si) (fun _ pt' fr' =>
      ls_l.pp = some pt' ∧ ls_l.vals.size = lsk.vals.size ∧ fr'.vals = frk.vals ∧
      Rel cfg env cx fr' { ls_l with stack := ls_l.stack.drop 1 }) := by
  obtain ⟨hv, hst, hpp1, hi⟩ := emitEffect_facts h hpp hext
  have hsc : frk.scopes = (sc, si) :: env.scopes := hrel.scopes
  have heq := releaseScope_eq hrel sc si
  have hx : execEff cx.fn frk (.leave sc) =
      Core.releaseScope env sc si >>= fun _ => pure ({ frk with scopes := env.scopes } : Frame) := by
    simp only [execEff, hsc, ↓reduceIte]
    rw [heq]
    rfl
  refine (SimG.eff_step (fun _ => { frk with scopes := env.scopes }) hi hx).mono
    fun u pt1 fr1 ⟨hpt, hfr⟩ => ?_
  subst hpt; subst hfr
  refine ⟨hpp1, hv, rfl, ?_⟩
  refine ⟨hrel.prof, hrel.slots, hrel.act, rfl, hrel.depth, ?_⟩
  have := hrel.stack
  simp only [List.map_cons] at this
  simp [hst, this]

theorem Post.rescope {cfg : Cfg} {env env' : Env} {cx : FnCtx} {ls lsp lsk ls_f : LS}
    {fr frp frk fr_f : Frame} {ptk pt : Pt} {cells : List (ValueId × RVal)}
    (hP : Post cfg env' cx lsp frp lsk frk ptk cells) (hv0 : lsp.vals.size = ls.vals.size)
    (hfr0 : frp.vals = fr.vals) (hpp : ls_f.pp = some pt) (hv : ls_f.vals.size = lsk.vals.size)
    (hfr : fr_f.vals = frk.vals) (hrel : Rel cfg env cx fr_f ls_f) :
    Post cfg env cx ls fr ls_f fr_f pt cells := by
  refine ⟨hpp, fun p hp => ?_, fun p hp => ?_, ?_, fun i hi => ?_, hrel⟩
  · rw [hfr]; exact hP.has p hp
  · rw [hv]; exact hP.lt p hp
  · have := hP.mono; rw [hv]; omega
  · have h1 := hP.same i (by omega)
    show fr_f.vals[i]? = fr.vals[i]?
    rw [hfr, h1, hfr0]


end Goose.Lower
