import Goose.Core.Sound.Check

/-!
What each check of the root pass, and each per-item stage of the validator,
establishes when it succeeds.
-/

namespace Goose.Core.Sound
open Goose.Core

theorem checkOutlives_ok (env : PEnv) (chain : List Nat) (lv : LocalVar) (xpos : Nat) :
    ∀ (rho : List RootRef), checkOutlives env chain lv xpos rho = .ok () →
    ∀ y, RootRef.local y ∈ rho →
      ∃ ly, env.impl.vars[y]? = some ly ∧ ly.scope ∈ chain ∧ xpos ≤ chain.idxOf ly.scope
  | [], _, y, hy => by cases hy
  | .local z :: rest, h, y, hy => by
    cases hv : env.impl.vars[z]? with
    | none => simp only [checkOutlives, hv] at h; inv at h
    | some ly =>
      simp only [checkOutlives, hv] at h
      inv at h
      obtain ⟨c1, c2, h⟩ := h
      rcases List.mem_cons.1 hy with e | hy
      · cases e
        exact ⟨ly, hv, by simpa using c1, c2⟩
      · exact checkOutlives_ok env chain lv xpos rest h y hy
  | .global g :: rest, h, y, hy => by
    simp only [checkOutlives] at h
    rcases List.mem_cons.1 hy with e | hy
    · cases e
    · exact checkOutlives_ok env chain lv xpos rest h y hy
  | .param j :: rest, h, y, hy => by
    simp only [checkOutlives] at h
    rcases List.mem_cons.1 hy with e | hy
    · cases e
    · exact checkOutlives_ok env chain lv xpos rest h y hy

theorem bindRootsV_ok (env : PEnv) (chain : List Nat) (x : VarId) (rho : List RootRef)
    (h : bindRootsV env chain x rho = .ok ()) :
    ∃ lv ann, env.impl.vars[x]? = some lv ∧ env.ann x = some ann ∧ (∀ q, q ∈ rho → q ∈ ann) ∧
      ∀ y, RootRef.local y ∈ rho →
        ∃ ly, env.impl.vars[y]? = some ly ∧ ly.scope ∈ chain ∧
          chain.idxOf lv.scope ≤ chain.idxOf ly.scope := by
  unfold bindRootsV at h
  cases hv : env.impl.vars[x]? with
  | none => simp only [hv] at h; inv at h
  | some lv =>
    cases ha : env.ann x with
    | none => simp only [hv, ha] at h; inv at h
    | some ann =>
      simp only [hv, ha] at h
      inv at h
      obtain ⟨hs, h⟩ := h
      exact ⟨lv, ann, rfl, rfl, subsetRoots_mem hs, checkOutlives_ok env chain lv _ rho h⟩

@[chk] theorem bindRoots_ok (env : PEnv) (chain : List Nat) (x : VarId) (rho : List RootRef)
    (s : RState) (r : Unit × RState) :
    bindRoots env chain x rho s = .ok r ↔ bindRootsV env chain x rho = .ok () ∧ r.2 = s := by
  simp only [bindRoots, liftV_ok]

theorem checkNoLocal_ok : ∀ (rho : List RootRef), checkNoLocal rho = .ok () →
    ∀ y, RootRef.local y ∉ rho
  | [], _, y => by simp
  | .local z :: rest, h, y => by simp only [checkNoLocal] at h; inv at h
  | .global g :: rest, h, y => by
    simp only [checkNoLocal] at h
    simpa using checkNoLocal_ok rest h y
  | .param j :: rest, h, y => by
    simp only [checkNoLocal] at h
    simpa using checkNoLocal_ok rest h y

theorem checkResultV_ok (env : PEnv) (rho : List RootRef) (h : checkResultV env rho = .ok ()) :
    (∀ y, RootRef.local y ∉ rho) ∧
    ∃ declared, env.ctx.resultRoots = [declared] ∧ ∀ q, q ∈ rho → q ∈ declared := by
  unfold checkResultV at h
  simp only [ex_bind_ok] at h
  obtain ⟨_, h1, h2⟩ := h
  refine ⟨checkNoLocal_ok rho h1, ?_⟩
  split at h2
  · rename_i declared hd
    inv at h2
    exact ⟨declared, hd, subsetRoots_mem h2⟩
  · inv at h2

@[chk] theorem checkResult_ok (env : PEnv) (rho : List RootRef) (s : RState) (r : Unit × RState) :
    checkResult env rho s = .ok r ↔ checkResultV env rho = .ok () ∧ r.2 = s := by
  simp only [checkResult, liftV_ok]

theorem checkBlockValue_ok (n0 n1 : Nat) : ∀ (rho : List RootRef),
    checkBlockValue n0 n1 rho = .ok () → ∀ y, RootRef.local y ∈ rho → ¬ (n0 ≤ y ∧ y < n1)
  | [], _, y, hy => by cases hy
  | .local z :: rest, h, y, hy => by
    simp only [checkBlockValue] at h
    inv at h
    obtain ⟨c, h⟩ := h
    rcases List.mem_cons.1 hy with e | hy
    · cases e; exact c
    · exact checkBlockValue_ok n0 n1 rest h y hy
  | .global g :: rest, h, y, hy => by
    simp only [checkBlockValue] at h
    rcases List.mem_cons.1 hy with e | hy
    · cases e
    · exact checkBlockValue_ok n0 n1 rest h y hy
  | .param j :: rest, h, y, hy => by
    simp only [checkBlockValue] at h
    rcases List.mem_cons.1 hy with e | hy
    · cases e
    · exact checkBlockValue_ok n0 n1 rest h y hy

/-- What the caller's roots of a call result contain, for each root the
callee declares. -/
def MappedRoot (ar : List (List RootRef)) (out : List RootRef) : RootRef → Prop
  | .param j => ∃ a, ar[j]? = some a ∧ ∀ q, q ∈ a → q ∈ out
  | .global g => RootRef.global g ∈ out
  | .local _ => False

theorem mapResultRoots_ok (ar : List (List RootRef)) : ∀ (rs acc out : List RootRef),
    mapResultRoots ar acc rs = .ok out →
    (∀ q, q ∈ acc → q ∈ out) ∧ ∀ r, r ∈ rs → MappedRoot ar out r
  | [], acc, out, h => by
    simp only [mapResultRoots, ex_pure_ok] at h
    subst h
    exact ⟨fun _ h => h, fun _ h => by cases h⟩
  | r :: rest, acc, out, h => by
    simp only [mapResultRoots, ex_bind_ok] at h
    obtain ⟨mapped, h1, h2⟩ := h
    obtain ⟨g1, g2⟩ := mapResultRoots_ok ar rest _ out h2
    refine ⟨fun q hq => g1 q (unionRoots_left _ _ q hq), ?_⟩
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · cases r' with
      | «local» y => simp only [mapCalleeRoots] at h1; inv at h1
      | global g =>
        simp only [mapCalleeRoots, ex_pure_ok] at h1
        subst h1
        exact g1 _ (unionRoots_right _ _ _ (by simp))
      | param j =>
        simp only [mapCalleeRoots] at h1
        cases ha : ar[j]? with
        | none => simp only [ha] at h1; inv at h1
        | some a =>
          simp only [ha, ex_pure_ok] at h1
          subst h1
          exact ⟨mapped, ha, fun q hq => g1 q (unionRoots_right _ _ q hq)⟩
    · exact g2 r' hr'

/-- The callee context's assumption about each reference parameter holds of
the argument's roots. -/
theorem checkArgRoots_ok (callee : Impl) (cctx : Context) (ar : List (List RootRef)) (i : Nat)
    (p : Param) (h : checkArgRoots callee cctx ar i = .ok ()) (hp : callee.params[i]? = some p) :
    ∃ pv, callee.vars[p.var]? = some pv ∧
      (pv.ty.isRefLike = true → ∃ ann, (cctx.varRoots.find? (·.1 == p.var)).map (·.2) = some ann ∧
        (ann = [.param i] ∨ ∀ q, q ∈ ar[i]?.getD [] → q ∈ ann)) := by
  unfold checkArgRoots at h
  simp only [hp] at h
  cases hv : callee.vars[p.var]? with
  | none => simp only [hv] at h; inv at h
  | some pv =>
    refine ⟨pv, rfl, fun hr => ?_⟩
    simp only [hv, hr, if_true] at h
    cases hf : cctx.varRoots.find? (·.1 == p.var) with
    | none => simp only [hf] at h; inv at h
    | some pr =>
      obtain ⟨x, ann⟩ := pr
      refine ⟨ann, by simp, ?_⟩
      simp only [hf] at h
      inv at h
      rcases h with e | ⟨_, hs⟩
      · exact Or.inl (by simpa using e)
      · exact Or.inr (subsetRoots_mem hs)

theorem addReads_ok (rho : List RootRef) (s : RState) (r : Unit × RState)
    (h : addReads rho s = .ok r) :
    r.2.nextVar = s.nextVar ∧ ∀ t, t ∈ rootsTargets rho → t ∈ r.2.eff.reads := by
  unfold addReads addRoots at h
  rw [st_modify_ok] at h
  subst h
  exact ⟨rfl, addTargets_right _ _⟩

theorem addWrites_ok (rho : List RootRef) (s : RState) (r : Unit × RState)
    (h : addWrites rho s = .ok r) :
    r.2.nextVar = s.nextVar ∧ ∀ t, t ∈ rootsTargets rho → t ∈ r.2.eff.writes := by
  unfold addWrites addRoots at h
  rw [st_modify_ok] at h
  subst h
  exact ⟨rfl, addTargets_right _ _⟩

theorem addGrows_ok (rho : List RootRef) (s : RState) (r : Unit × RState)
    (h : addGrows rho s = .ok r) :
    r.2.nextVar = s.nextVar ∧ ∀ t, t ∈ rootsTargets rho → t ∈ r.2.eff.grows := by
  unfold addGrows addRoots at h
  rw [st_modify_ok] at h
  subst h
  exact ⟨rfl, addTargets_right _ _⟩

/-! ### Blocks and calls -/

theorem tyBlock_ok (env : TEnv) (pre : List (VarId × Ty)) (sc : Nat) (stmts : List Stmt)
    (value : Option Expr) (tn : Nat) (ty : Ty) (tn' : Nat)
    (h : tyBlock env pre (.mk sc stmts value) tn = .ok (ty, tn')) :
    sc ∉ env.scopes ∧ ∃ env1 tn1 env2 tn2,
      declarePre { env with scopes := sc :: env.scopes } sc pre tn = .ok (env1, tn1) ∧
      tyStmts env1 sc stmts tn1 = .ok (env2, tn2) ∧
      (match value with
       | none => ty = .unit ∧ tn' = tn2
       | some e => tyExpr env2 e tn2 = .ok (ty, tn')) := by
  cases value with
  | none =>
    simp only [tyBlock] at h
    inv at h
    obtain ⟨hc, env1, tn1, h1, env2, tn2, h2, rfl, rfl⟩ := h
    exact ⟨by simpa using hc, env1, tn1, env2, _, h1, h2, rfl, rfl⟩
  | some e =>
    simp only [tyBlock] at h
    inv at h
    obtain ⟨hc, env1, tn1, h1, env2, tn2, h2, h3⟩ := h
    exact ⟨by simpa using hc, env1, tn1, env2, tn2, h1, h2, h3⟩

theorem rpBlockValue_ok (env : PEnv) (pre : List VarId) (sc : Nat) (stmts : List Stmt)
    (value : Option Expr) (st : RState) (rho : List RootRef) (rng : Nat × Nat) (st' : RState)
    (h : rpBlockValue env pre (.mk sc stmts value) st = .ok ((rho, rng), st')) :
    (∀ x, x ∈ pre → st.nextVar ≤ x ∧ x < st.nextVar + pre.length) ∧
    ∃ st2, rpStmts { env with scopes := sc :: env.scopes } stmts
        { st with nextVar := st.nextVar + pre.length } = .ok ((), st2) ∧
      (match value with
       | none => rho = [] ∧ st' = st2
       | some e => rpExpr { env with scopes := sc :: env.scopes } e st2 = .ok (rho, st')) ∧
      (∀ y, RootRef.local y ∈ rho → ¬ (st.nextVar ≤ y ∧ y < st'.nextVar)) := by
  cases value with
  | none =>
    simp only [rpBlockValue] at h
    inv at h
    obtain ⟨hpre, st2, h2, hb, rfl, _, rfl⟩ := h
    refine ⟨?_, _, h2, ⟨rfl, rfl⟩, checkBlockValue_ok _ _ _ hb⟩
    intro x hx
    have := List.all_eq_true.1 hpre x hx
    simpa using this
  | some e =>
    simp only [rpBlockValue] at h
    inv at h
    obtain ⟨hpre, st2, h2, rho', st3, h3, hb, rfl, _, rfl⟩ := h
    refine ⟨?_, st2, h2, h3, checkBlockValue_ok _ _ _ hb⟩
    intro x hx
    have := List.all_eq_true.1 hpre x hx
    simpa using this

theorem rpCall_ok (env : PEnv) (c : ContextId) (ar : List (List RootRef)) (st : RState)
    (rho : List RootRef) (st' : RState) (h : rpCall env c ar st = .ok (rho, st')) :
    ∃ cctx callee, env.mod.contexts[c]? = some cctx ∧ env.mod.impls[cctx.impl]? = some callee ∧
      (∀ i, i < callee.params.size → checkArgRoots callee cctx ar i = .ok ()) ∧
      st' = { st with eff := callEffects callee cctx ar st.eff } ∧
      callResultRoots callee cctx ar = .ok rho := by
  unfold rpCall at h
  cases hc : env.mod.contexts[c]? with
  | none => simp only [hc] at h; inv at h
  | some cctx =>
    cases hi : env.mod.impls[cctx.impl]? with
    | none => simp only [hc, hi] at h; inv at h
    | some callee =>
      simp only [hc, hi] at h
      inv at h
      obtain ⟨hf, hr, rfl⟩ := h
      refine ⟨cctx, callee, rfl, hi, ?_, rfl, hr⟩
      intro i hi'
      exact (forAll_ok _ _).1 hf i (List.mem_range.2 hi')

theorem callEffects_ok (callee : Impl) (cctx : Context) (ar : List (List RootRef)) (e : Eff) :
    match callee.summary with
    | .unknown => (callEffects callee cctx ar e).unknown = true
    | .known sm =>
      (∀ t, t ∈ mapCallTargets callee cctx ar sm.reads → t ∈ (callEffects callee cctx ar e).reads) ∧
      (∀ t, t ∈ mapCallTargets callee cctx ar sm.writes → t ∈ (callEffects callee cctx ar e).writes) ∧
      (∀ t, t ∈ mapCallTargets callee cctx ar sm.grows → t ∈ (callEffects callee cctx ar e).grows) := by
  cases h : callee.summary with
  | unknown => simp only [callEffects, h]
  | known sm =>
    simp only [callEffects, h]
    exact ⟨addTargets_right _ _, addTargets_right _ _, addTargets_right _ _⟩

/-! ### Stages of the validator -/

theorem effWithin_ok (name what : String) (found declared : List Target)
    (h : effWithin name what found declared = .ok ()) : ∀ t, t ∈ found → t ∈ declared := by
  unfold effWithin at h
  split at h
  · inv at h
  · rename_i hf
    intro t ht
    have := List.find?_eq_none.1 hf t ht
    simpa using this

theorem checkSummary_ok (impl : Impl) (ctx : Context) (eff : Eff)
    (h : checkSummary impl ctx eff = .ok ()) (sm : Summary) (hs : impl.summary = .known sm) :
    eff.unknown = false ∧
    (∀ t, t ∈ eff.reads → t ∈ expandTargets impl ctx sm.reads) ∧
    (∀ t, t ∈ eff.writes → t ∈ expandTargets impl ctx sm.writes) ∧
    (∀ t, t ∈ eff.grows → t ∈ expandTargets impl ctx sm.grows) := by
  unfold checkSummary at h
  simp only [hs] at h
  inv at h
  obtain ⟨hu, h1, h2, h3, _⟩ := h
  exact ⟨by simpa using hu, effWithin_ok _ _ _ _ h1, effWithin_ok _ _ _ _ h2, effWithin_ok _ _ _ _ h3⟩

end Goose.Core.Sound
