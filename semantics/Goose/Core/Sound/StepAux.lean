import Goose.Core.Sound.Lemmas
import Goose.Core.Sound.Stops

/-!
Facts shared by the statement cases: what the binding rule gives, how binding
and rebinding look from the code around them, and running a block from the
validator's two checks of it.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

variable {m : Module} {prof : NumProfile} {n : Nat}
variable {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}

theorem isRef_of_refLike {G : Nat} {st : Store} {v : Val} {T : Ty} (h : HasTy m G st v T)
    (hT : T.isRefLike = true) : IsRef v := by
  cases T <;> simp only [Ty.isRefLike] at hT <;> try cases hT
  · obtain ⟨l, rfl, _⟩ := h; trivial
  · obtain ⟨l, a, b, rfl, _⟩ := h; trivial

/-- A frame reads only the store and the scope counter of the state. -/
theorem Frame.of_eq {s' : St} {future : List VarId} (h : Frame m W tenv penv env s future)
    (h1 : s'.store = s.store) (h2 : s'.nextScope = s.nextScope) :
    Frame m W tenv penv env s' future :=
  { h with
    below := by rw [h2]; exact h.below
    base_le := by rw [h2]; exact h.base_le
    vis := by
      intro x hx hf
      obtain ⟨lv, si, v, hvar, hlk, hty, hroot, hvalue⟩ := h.vis x hx hf
      exact ⟨lv, si, v, hvar, hlk, hty, by rw [h1]; exact hroot, by rw [h1]; exact hvalue⟩
    rooted := by rw [h1]; exact h.rooted
    inv := {
      live := by
        intro r v hr hd
        rw [h1] at hr
        simpa [h1] using h.inv.live r v hr hd
      age := by
        intro r v hr r' ht
        rw [h1] at hr
        exact h.inv.age r v hr r' ht
      fresh := by
        intro a si x hr
        rw [h1] at hr
        rw [h2]
        exact h.inv.fresh a si x hr
      globals := by
        intro g gl hg hm
        rw [h1]
        exact h.inv.globals g gl hg hm
    }
    sa := by rw [h1]; exact h.sa }

theorem Ext.of_eq {is : List Nat} {D : RootInst → Prop} {s s' : St} (h1 : s'.store = s.store)
    (h2 : s'.nextScope = s.nextScope) : Ext is D s s' :=
  ⟨by rw [h1]; exact StoreLe.refl _, by rw [h2]; exact Nat.le_refl _,
   fun _ _ h _ _ _ => by rw [h1]; exact h, fun _ _ h _ _ _ => by rw [← h1]; exact h,
   fun _ h => by rw [← h1]; exact h⟩

theorem Footprint.of_eq {is : List Nat} {D : RootInst → Prop} {s s' : St}
    (h1 : s'.store = s.store) (h2 : s'.nextScope = s.nextScope) : Footprint is D s s' :=
  ⟨by rw [h2]; exact Nat.le_refl _, fun _ _ h _ _ _ => by rw [h1]; exact h,
   fun _ _ h _ _ _ => by rw [← h1]; exact h, fun _ h => by rw [← h1]; exact h⟩

/-- A root set with no local denotes the same roots in every activation. -/
theorem gam_noEnv {P : Nat → RootInst → Prop} {rho : List RootRef} {r : RootInst}
    (h : Gam env P rho r) (hn : ∀ y, RootRef.local y ∉ rho) : Gam noEnv P rho r := by
  obtain ⟨q, hq, hr⟩ := h
  refine ⟨q, hq, ?_⟩
  cases q with
  | «local» y => exact absurd hq (hn y)
  | global g => exact hr
  | param j => exact hr

theorem gam_of_noEnv {P : Nat → RootInst → Prop} {rho : List RootRef} {r : RootInst}
    (h : Gam noEnv P rho r) : Gam env P rho r := by
  obtain ⟨q, hq, hr⟩ := h
  refine ⟨q, hq, ?_⟩
  cases q with
  | «local» y => obtain ⟨lv, si, h1, _⟩ := hr; simp [noEnv] at h1
  | global g => exact hr
  | param j => exact hr

/-- What the binding rule gives: the bound value points into the variable's
annotation, and into roots that end no earlier than the variable. `chain`
is the open scopes, which hold the variable's scope. -/
theorem bind_roots_sem (hF : Frame m W tenv penv env s) {x : VarId} {lv : LocalVar}
    {si : ScopeInst} {rho : List RootRef} {v : Val}
    (hb : bindRootsV penv penv.scopes x rho = .ok ()) (hx : env.vars[x]? = some lv)
    (hsi : env.scopes.lookup lv.scope = some si) (hg : ∀ r, Targets v r → Gam env W.P rho r) :
    ∀ r, Targets v r → (∃ ann, penv.ann x = some ann ∧ Gam env W.P ann r) ∧
      Older r (.local env.act si x) := by
  obtain ⟨lv', ann, h1, h2, h3, h4⟩ := bindRootsV_ok _ _ _ _ hb
  rw [hF.vars_p, hx] at h1
  cases h1
  intro r hr
  have hgr := hg r hr
  refine ⟨⟨ann, h2, hgr.subset h3⟩, ?_⟩
  obtain ⟨q, hq, hrq⟩ := hgr
  cases q with
  | «local» y =>
    obtain ⟨ly, siy, g1, g2, rfl⟩ := hrq
    obtain ⟨ly', k1, _, k3⟩ := h4 y hq
    rw [hF.vars_p, g1] at k1
    cases k1
    rw [hF.scopes_p] at k3
    exact lookup_idx_le _ hF.sorted _ _ _ _ hsi g2 k3
  | global g => simp only [RootIn] at hrq; subst hrq; trivial
  | param j =>
    cases r with
    | global g => trivial
    | «local» a si' x' =>
      have h5 := hF.pAge j a si' x' hrq
      have h6 := (hF.inst_lt hsi).1
      exact Nat.le_of_lt (Nat.lt_of_lt_of_le h5 h6)

/-- The innermost open block and its scope instance. -/
theorem Frame.top (hF : Frame m W tenv penv env s) {sc : Nat} (h : tenv.scopes.head? = some sc) :
    ∃ si rest, env.scopes = (sc, si) :: rest ∧ env.scopes.lookup sc = some si := by
  rw [hF.scopes_t] at h
  cases hs : env.scopes with
  | nil => simp [hs] at h
  | cons p rest =>
    obtain ⟨k, si⟩ := p
    simp only [hs, List.map_cons, List.head?_cons, Option.some.injEq] at h
    subst h
    exact ⟨si, rest, rfl, by simp [lookup_cons]⟩

/-- Binding a variable of the innermost block, seen from the code around it. -/
theorem extS_bind {D : RootInst → Prop} {x : VarId} {lv : LocalVar} {si : ScopeInst}
    {rest : List (Nat × ScopeInst)} {v : Val} (htop : env.scopes = (lv.scope, si) :: rest) (hx : env.vars[x]? = some lv)
    (hfree : s.store.roots[RootInst.local env.act si x]? = none) :
    ExtS env D s { s with store := s.store.introduce (.local env.act si x) v } := by
  have hne : ∀ (r : RootInst), s.store.roots[r]? ≠ none → RootInst.local env.act si x ≠ r := by
    rintro r hr rfl; exact hr hfree
  refine ⟨introduce_le _ _ _ hfree, Nat.le_refl _, ?_, ?_, ?_⟩
  · intro r v' hv' _ _ _
    show (s.store.introduce _ v).roots[r]? = some v'
    rw [get_introduce]
    simp [hne r (by rw [hv']; simp), hv']
  · intro r v' hv' _ hn _
    have hv'' : (s.store.introduce (.local env.act si x) v).roots[r]? = some v' := hv'
    rw [get_introduce] at hv''
    by_cases e : RootInst.local env.act si x = r
    · subst e
      exact absurd (by simp [insts, htop]) (hn env.act si x rfl)
    · simpa [e] using hv''
  · intro r hr
    have hr' : (s.store.introduce (.local env.act si x) v).roots[r]? ≠ none := hr
    rw [get_introduce] at hr'
    by_cases e : RootInst.local env.act si x = r
    · subst e
      exact Or.inr ⟨x, lv, si, rest, htop, hx, rfl⟩
    · simp only [e, if_false] at hr'
      exact Or.inl hr'

theorem topB_bind {x : VarId} {si : ScopeInst} {sc : Nat} {rest : List (Nat × ScopeInst)} {v : Val}
    {lo cur cur' : Nat} (htop : env.scopes = (sc, si) :: rest) (h : TopB env lo cur s)
    (h1 : lo ≤ x) (h2 : x < cur') (h3 : cur ≤ cur') :
    TopB env lo cur' { s with store := s.store.introduce (.local env.act si x) v } := by
  intro sc' si' rest' he y hy
  rw [htop] at he
  cases he
  have hy' : (s.store.introduce (.local env.act si x) v).roots[RootInst.local env.act si y]? ≠ none := hy
  rw [get_introduce] at hy'
  by_cases e : x = y
  · subst e; exact ⟨h1, h2⟩
  · have : ¬ (RootInst.local env.act si x = RootInst.local env.act si y) := by
      intro e'; cases e'; exact e rfl
    simp only [this, if_false] at hy'
    obtain ⟨g1, g2⟩ := h _ _ _ htop y hy'
    exact ⟨g1, Nat.lt_of_lt_of_le g2 h3⟩

/-- Rebinding a variable of the activation, seen from the code around it. -/
theorem ext_rebind {D : RootInst → Prop} {x : VarId} {si : ScopeInst} {old v : Val}
    (hsi : si ∈ insts env) (ho : s.store.roots[RootInst.local env.act si x]? = some old)
    (hold : IsRef old) :
    Ext (insts env) D s
      { s with store := ⟨(s.store.roots.erase (.local env.act si x)).insert (.local env.act si x) v⟩ } := by
  refine ⟨rebind_le _ _ old v ho hold, Nat.le_refl _, ?_, ?_, ?_⟩
  · intro r v' hv' _ hn _
    have e : ¬ (RootInst.local env.act si x = r) := by
      rintro rfl; exact hn _ _ _ rfl hsi
    simp [get_reinsert, e, hv']
  · intro r v' hv' _ hn _
    have e : ¬ (RootInst.local env.act si x = r) := by
      rintro rfl; exact hn _ _ _ rfl hsi
    simpa [get_reinsert, e] using hv'
  · intro r hr
    by_cases e : RootInst.local env.act si x = r
    · subst e; simp [ho]
    · simpa [get_reinsert, e] using hr

theorem lookup_inst {l : List (Nat × Nat)} {a b : Nat} (h : l.lookup a = some b) :
    b ∈ l.map Prod.snd :=
  List.mem_map.2 ⟨(a, b), lookup_mem l a b h, rfl⟩

/-- A loop whose condition is the constant `true` ends normally only by `break`. -/
theorem while_diverges (c : Expr) (b : Block) (o : OriginId)
    (h : c = .bool true → b.hasBreak = true) : (Stmt.while c b o).diverges m.noReturn = false := by
  cases c <;> try rfl
  rename_i bb
  cases bb
  · rfl
  · simp [Stmt.diverges, h rfl]

/-- The elements of a sampled run, read out of a typed array. -/
theorem sat_readRun_bind {vw : ViewVal} {el : Ty} {f : Array Val → M α} {Q : α → St → Prop}
    (h : ViewOk s.store vw el)
    (k : ∀ vs : Array Val, (∀ (i : Nat) (e : Val), vs[i]? = some e → FlatTy el e) → Sat (f vs) s Q) :
    Sat (readRun vw >>= f) s Q := by
  obtain ⟨_, ⟨v, es, hr, hes, hn, hT⟩, _⟩ := h
  have helem : ∀ (i : Nat) (e : Val), es[i]? = some e → FlatTy el e := by
    intro i e he
    rcases hT with hT | hT | ⟨k', hT⟩ | ⟨capacity, hT⟩
    · cases v <;> simp only [FlatTy] at hT
      simp only [Val.elems?, Option.some.injEq, reduceCtorEq] at hes
      subst hes
      exact hT.2 i e he
    · cases v <;> simp only [FlatTy] at hT
      simp only [Val.elems?, Option.some.injEq, reduceCtorEq] at hes
      subst hes
      exact hT.2 i e he
    · cases v <;> simp only [FlatTy] at hT
      simp only [Val.elems?, Option.some.injEq, reduceCtorEq] at hes
      subst hes
      exact hT.2 i e he
    · cases v <;> simp only [FlatTy] at hT
      simp only [Val.elems?, Option.some.injEq, reduceCtorEq] at hes
      subst hes
      exact hT.2.2.2.2 i e he
  have hext : ∀ (i : Nat) (e : Val),
      (es.extract vw.start (vw.start + vw.len))[i]? = some e → FlatTy el e := by
    intro i e he
    rw [Array.getElem?_extract] at he
    split at he
    · exact helem _ e he
    · cases he
  have e1 : (readRun vw >>= f) s = f (es.extract vw.start (vw.start + vw.len)) s := by
    show M.bind' (readRun vw) f s = _
    have : readRun vw s = .ok (es.extract vw.start (vw.start + vw.len)) s := by
      show M.bind' (readLoc vw.loc) _ s = _
      simp only [M.bind', readLoc, hr]
      cases v <;> simp only [Val.elems?, Option.some.injEq, reduceCtorEq] at hes <;> subst hes <;>
        simp [hn, pure, M.pure']
    simp [M.bind', this]
  unfold Sat; rw [e1]; exact k _ hext

theorem sliceRefTy_some {env : TEnv} {e : Expr} {ty : Ty} (h : sliceRefTy env e = some ty) :
    ∃ x lv mu0 mu E, e = .read (.var x) ∧ x ∈ env.visible ∧ env.vars[x]? = some lv ∧
      lv.ty = .ref mu0 (.slice mu E) ∧ E.flat = true ∧ ty = lv.ty := by
  unfold sliceRefTy at h
  split at h
  · rename_i x
    by_cases hx : x ∈ env.visible
    · have hx' : env.visible.contains x = true := by simpa using hx
      simp only [hx', if_true] at h
      cases hv : env.vars[x]? with
      | none => simp [hv] at h
      | some lv =>
        simp only [hv] at h
        by_cases hr : lv.ty.isRefSlice = true
        · simp only [hr, if_true, Option.some.injEq] at h
          cases hty : lv.ty <;> simp only [hty, Ty.isRefSlice, reduceCtorEq] at hr
          rename_i mu0 t
          cases t <;> simp only [Ty.isRefSlice, reduceCtorEq] at hr
          rename_i mu E
          exact ⟨x, lv, mu0, mu, E, rfl, hx, hv, hty, hr, by rw [← h, hty]⟩
        · simp [hr] at h
    · have hx' : env.visible.contains x = false := by simpa using hx
      simp only [hx'] at h
      cases h
  · cases h

/-- Reading a visible variable only to dereference it. -/
theorem sat_read_var {future : List VarId} (hF : Frame m W tenv penv env s future)
    {x : VarId} (hx : x ∈ tenv.visible) (hfuture : x ∈ future) (k : Nat)
    {Q : Val → St → Prop}
    (hq : ∀ lv si v, env.vars[x]? = some lv → env.scopes.lookup lv.scope = some si →
      s.store.roots[RootInst.local env.act si x]? = some v → HasTy m W.G s.store v lv.ty → Q v s) :
    Sat (evalExpr k ⟨prof, m⟩ env (.read (.var x))) s Q := by
  obtain ⟨lv, si, v, h1, h2, _, h4, h5⟩ := hF.vis x hx hfuture
  cases k with
  | zero => simp only [evalExpr, sat_timeout]
  | succ k =>
    simp only [evalExpr]
    cases k with
    | zero => simp only [evalPlace, sat_timeout_bind]
    | succ k =>
      simp only [evalPlace, rootOf, h1, h2, sat_pure_bind]
      exact sat_readRoot h4 (hq lv si v h1 h2 h4 h5)

/-- Opening a block changes no root a static root denotes. -/
theorem gam_push (hF : Frame m W tenv penv env s) {sc : Nat} (hsc : sc ∉ tenv.scopes) (k : ScopeInst)
    {rho : List RootRef} {r : RootInst} (h : Gam env W.P rho r) :
    Gam { env with scopes := (sc, k) :: env.scopes } W.P rho r := by
  have hsc' : sc ∉ env.scopes.map Prod.fst := hF.scopes_t ▸ hsc
  obtain ⟨q, hq, hr⟩ := h
  refine ⟨q, hq, ?_⟩
  cases q with
  | «local» y =>
    obtain ⟨lv, si, h1, h2, h3⟩ := hr
    refine ⟨lv, si, h1, ?_, h3⟩
    show ((sc, k) :: env.scopes).lookup lv.scope = some si
    rw [lookup_cons]
    have : lv.scope ≠ sc := fun e => hsc' (e ▸ lookup_key h2)
    simp [this, h2]
  | global g => exact hr
  | param j => exact hr

theorem sat_lengthLoc {l : Loc} {E : Ty} {Q : Nat → St → Prop}
    (h : LocTy s.store l (.grow E))
    (k : ∀ es, s.store.read l = .ok (.resizable E es) → Q es.size s) : Sat (lengthLoc l) s Q := by
  obtain ⟨v, hv, hT⟩ := h
  rcases v with _|_|_|_|_|⟨E', es⟩|_|_ <;> simp only [FlatTy] at hT
  obtain ⟨rfl, _⟩ := hT
  simp only [Sat, lengthLoc, Store.length, hv]
  exact k es hv

theorem sat_lengthLoc_growshrink {l : Loc} {E : Ty} {Q : Nat → St → Prop}
    (h : LocTy s.store l (.growshrink E))
    (k : ∀ es, s.store.read l = .ok (.resizable E es) → Q es.size s) :
    Sat (lengthLoc l) s Q := by
  obtain ⟨v, hv, hT⟩ := h
  rcases v with _|_|_|_|_|⟨E', es⟩|_|_ <;> simp only [FlatTy] at hT
  obtain ⟨rfl, _⟩ := hT
  simp only [Sat, lengthLoc, Store.length, hv]
  exact k es hv

end Goose.Core.Sound
