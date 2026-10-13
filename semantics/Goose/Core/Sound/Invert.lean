import Goose.Core.Sound.Check

/-!
What each check of the root pass, and each per-item stage of the validator,
establishes when it succeeds.
-/

namespace Goose.Core.Sound
open Goose.Core

theorem structDef_ok (env : TEnv) (t : Ty) (n n' : Nat) (d : StructDef)
    (h : structDef env t n = .ok (d, n')) :
    ∃ sid ts, t = .structT sid ts ∧ t.flat = true ∧ env.mod.structType? sid = some t ∧
      env.mod.structs[sid]? = some d ∧ n' = n := by
  cases t <;> simp only [structDef] at h <;> inv at h
  rename_i sid ts
  obtain ⟨hp, hf, hc, h⟩ := h
  cases hd : env.mod.structs[sid]? with
  | none => simp only [hd] at h; inv at h
  | some found =>
    simp only [hd] at h; inv at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨sid, ts, rfl, hf, by simpa using hc, hd, rfl⟩

@[simp] theorem tyList_toList_ofList (ts : List Ty) : (TyList.ofList ts).toList = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [TyList.ofList, TyList.toList, ih]

theorem tyList_flat_get : ∀ (ts : TyList), ts.flat = true →
    ∀ (i : Nat) (t : Ty), ts.toList[i]? = some t → t.flat = true
  | .nil, h, i, t, ht => by simp [TyList.toList] at ht
  | .cons u us, h, i, t, ht => by
    simp only [TyList.flat, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [TyList.toList, List.getElem?_cons_zero, Option.some.injEq] at ht
      subst ht; exact h.1
    | succ i => exact tyList_flat_get us h.2 i t (by simpa [TyList.toList] using ht)

theorem structField_ok (env : TEnv) (t : Ty) (i n n' : Nat) (f : StructField)
    (h : structField env t i n = .ok (f, n')) :
    ∃ sid ts, t = .structT sid ts ∧ t.flat = true ∧ ts.toList[i]? = some f.ty ∧ n' = n := by
  simp only [structField] at h; inv at h
  obtain ⟨d, n1, hd, h⟩ := h
  obtain ⟨sid, ts, rfl, hflat, hc, hdesc, rfl⟩ := structDef_ok _ _ _ _ _ hd
  cases hf : d.fields[i]? with
  | none => simp only [hf] at h; inv at h
  | some found =>
    simp only [hf] at h; inv at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Module.structType?, hdesc, Option.map_some, Option.some.injEq, Ty.structT.injEq] at hc
    obtain ⟨_, rfl⟩ := hc
    refine ⟨sid, _, rfl, hflat, ?_, rfl⟩
    simp only [tyList_toList_ofList, List.getElem?_map, Array.getElem?_toList, hf, Option.map_some]

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

theorem addShrinks_ok (rho : List RootRef) (s : RState) (r : Unit × RState)
    (h : addShrinks rho s = .ok r) :
    r.2.nextVar = s.nextVar ∧ ∀ t, t ∈ rootsTargets rho → t ∈ r.2.eff.shrinks := by
  unfold addShrinks addRoots at h
  rw [st_modify_ok] at h
  subst h
  exact ⟨rfl, addTargets_right _ _⟩

/-- A direct shrinking statement records every replay root of its owner in the
resulting shrink effect, even when later replay stages add other effects. -/
theorem rpStmt_directShrink_targets (env : PEnv) (stmt : Stmt) (owner : Place)
    (state state' : RState)
    (hdirect : DemandNode.directShrinkPlace? (.statement stmt) = some owner)
    (hreplay : rpStmt env stmt state = .ok ((), state')) :
    ∃ roots ownerState, rpPlace env owner state = .ok (roots, ownerState) ∧
      ∀ target, target ∈ rootsTargets roots → target ∈ state'.eff.shrinks := by
  cases stmt <;> simp only [DemandNode.directShrinkPlace?] at hdirect
  all_goals try cases hdirect
  case popN count org =>
    simp only [rpStmt] at hreplay
    rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨roots, ownerState, hplace, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, _, _, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, _, _, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, mid, hshrink, habort⟩
    refine ⟨roots, ownerState, hplace, ?_⟩
    intro target htarget
    have hrecorded := (addShrinks_ok roots _ ((), mid) hshrink).2 target htarget
    exact (PMono.noteAborts _ _ _ habort).2.2.2.2.1 target hrecorded
  case resize size fill org =>
    cases fill with
    | none =>
      simp only [rpStmt] at hreplay
      rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨roots, ownerState, hplace, hrest⟩
      rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, _, _, hrest⟩
      rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, _, _, hrest⟩
      rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, mid, hshrink, habort⟩
      refine ⟨roots, ownerState, hplace, ?_⟩
      intro target htarget
      have hrecorded := (addShrinks_ok roots _ ((), mid) hshrink).2 target htarget
      exact (PMono.noteAborts _ _ _ habort).2.2.2.2.1 target hrecorded
    | some fillExpr =>
      simp only [rpStmt] at hreplay
      rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨roots, ownerState, hplace, hrest⟩
      rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, _, _, hrest⟩
      rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, _, _, hrest⟩
      rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, _, _, hrest⟩
      rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, _, _, hrest⟩
      rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, _, _, hrest⟩
      rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, mid, hshrink, habort⟩
      refine ⟨roots, ownerState, hplace, ?_⟩
      intro target htarget
      have hrecorded := (addShrinks_ok roots _ ((), mid) hshrink).2 target htarget
      exact (PMono.noteAborts _ _ _ habort).2.2.2.2.1 target hrecorded
  case clear org =>
    simp only [rpStmt] at hreplay
    rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨roots, ownerState, hplace, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, _, _, hshrink⟩
    refine ⟨roots, ownerState, hplace, ?_⟩
    intro target htarget
    exact (addShrinks_ok roots _ ((), state') hshrink).2 target htarget
  case assignWhole replacement org =>
    simp only [rpStmt] at hreplay
    rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨roots, ownerState, hplace, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, _, _, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, mid, hshrink, htail⟩
    refine ⟨roots, ownerState, hplace, ?_⟩
    intro target htarget
    have hrecorded := (addShrinks_ok roots _ ((), mid) hshrink).2 target htarget
    have htailMono := PMono.bind (rp_mono_all.2.2.1 env replacement) (fun _ =>
      PMono.bind (PMono.addWrites roots) (fun _ => PMono.addGrows roots))
    exact htailMono _ _ _ htail |>.2.2.2.2.1 target hrecorded

/-- A pop expression records every replay root of its owner in the resulting
shrink effect. -/
theorem rpExpr_pop_targets (env : PEnv) (owner : Place) (org : OriginId)
    (state state' : RState)
    (hreplay : rpExpr env (.pop owner org) state = .ok ([], state')) :
    ∃ roots ownerState, rpPlace env owner state = .ok (roots, ownerState) ∧
      ∀ target, target ∈ rootsTargets roots → target ∈ state'.eff.shrinks := by
  simp only [rpExpr] at hreplay
  rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨roots, ownerState, hplace, hrest⟩
  rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, _, _, hrest⟩
  rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, mid, hshrink, htail⟩
  refine ⟨roots, ownerState, hplace, ?_⟩
  intro target htarget
  have hrecorded := (addShrinks_ok roots _ ((), mid) hshrink).2 target htarget
  have htailMono : PMono (do noteAborts; pure ([] : List RootRef)) :=
    PMono.bind PMono.noteAborts (fun _ => PMono.pure [])
  exact htailMono _ _ _ htail |>.2.2.2.2.1 target hrecorded

private theorem rpStmts_member_replay (env : PEnv) (stmts : List Stmt)
    (index : Nat) (stmt : Stmt) (state state' : RState)
    (hindex : stmts[index]? = some stmt)
    (hreplay : rpStmts env stmts state = .ok ((), state')) :
    ∃ before after, rpStmt env stmt before = .ok ((), after) ∧ RLe after state' := by
  induction stmts generalizing index stmt state state' with
  | nil => simp at hindex
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hindex
      subst stmt
      simp only [rpStmts] at hreplay
      rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨_, after, hstmt, htail⟩
      refine ⟨state, after, hstmt, ?_⟩
      exact (rp_mono_all.2.2.2.2.2.1 env tail) _ _ _ htail
    | succ index =>
      have htailIndex : tail[index]? = some stmt := by simpa using hindex
      simp only [rpStmts] at hreplay
      rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨_, mid, _, htail⟩
      exact ih index stmt mid state' htailIndex htail

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
      (∀ y, RootRef.local y ∈ rho → ¬ (st.nextVar ≤ y ∧ y < st'.nextVar)) ∧
      rng.1 = st.nextVar := by
  cases value with
  | none =>
    simp only [rpBlockValue] at h
    inv at h
    obtain ⟨hpre, st2, h2, hb, rfl, hrng, rfl⟩ := h
    refine ⟨?_, _, h2, ⟨rfl, rfl⟩, checkBlockValue_ok _ _ _ hb, by rw [hrng]⟩
    intro x hx
    have := List.all_eq_true.1 hpre x hx
    simpa using this
  | some e =>
    simp only [rpBlockValue] at h
    inv at h
    obtain ⟨hpre, st2, h2, rho', st3, h3, hb, rfl, hrng, rfl⟩ := h
    refine ⟨?_, st2, h2, h3, checkBlockValue_ok _ _ _ hb, by rw [hrng]⟩
    intro x hx
    have := List.all_eq_true.1 hpre x hx
    simpa using this

private theorem rpBlockValue_directShrink_statement (env : PEnv) (scope : Nat)
    (stmts : List Stmt) (value : Option Expr) (index : Nat) (stmt : Stmt)
    (owner : Place) (state : RState) (rho : List RootRef) (range : Nat × Nat)
    (state' : RState)
    (hindex : stmts[index]? = some stmt)
    (hdirect : DemandNode.directShrinkPlace? (.statement stmt) = some owner)
    (hreplay : rpBlockValue env [] (.mk scope stmts value) state =
      .ok ((rho, range), state')) :
    ∃ before roots ownerState,
      rpPlace { env with scopes := scope :: env.scopes } owner before = .ok (roots, ownerState) ∧
      ∀ target, target ∈ rootsTargets roots → target ∈ state'.eff.shrinks := by
  obtain ⟨_, stateAfterStmts, hstmts, hvalue, _, _⟩ :=
    rpBlockValue_ok env [] scope stmts value state rho range state' hreplay
  have hstmts' : rpStmts { env with scopes := scope :: env.scopes } stmts state =
      .ok ((), stateAfterStmts) := by simpa using hstmts
  obtain ⟨before, after, hstmt, hmonoStmts⟩ :=
    rpStmts_member_replay { env with scopes := scope :: env.scopes }
      stmts index stmt state stateAfterStmts hindex hstmts'
  obtain ⟨roots, ownerState, howner, hrecorded⟩ :=
    rpStmt_directShrink_targets { env with scopes := scope :: env.scopes }
      stmt owner before after hdirect hstmt
  have hmonoValue : RLe stateAfterStmts state' := by
    cases value with
    | none =>
      obtain ⟨_, rfl⟩ := hvalue
      exact RLe.refl _
    | some expr =>
      exact (rp_mono_all.2.2.1 { env with scopes := scope :: env.scopes } expr)
        _ _ _ hvalue
  refine ⟨before, roots, ownerState, howner, ?_⟩
  intro target htarget
  exact (hmonoStmts.trans hmonoValue).2.2.2.2.1 target (hrecorded target htarget)

private theorem block_child_statement_index (scope : Nat) (stmts : List Stmt)
    (value : Option Expr) (index : Nat) (stmt : Stmt)
    (hchild : (DemandNode.block (.mk scope stmts value)).child? index =
      some (.statement stmt)) :
    stmts[index]? = some stmt := by
  simp only [DemandNode.child?, DemandNode.children] at hchild
  simp only [List.getElem?_append] at hchild
  split at hchild
  · simp only [List.getElem?_map] at hchild
    cases hindex : stmts[index]? with
    | none => simp [hindex] at hchild
    | some found =>
      simp [hindex] at hchild
      subst found
      rfl
  · cases hoffset : index - stmts.length with
    | zero => cases value <;> simp [hoffset] at hchild
    | succ offset => simp [hoffset] at hchild

theorem DemandExpectedSourceAt.directShrink_blockStatement_replay
    {m : Module} {owner : Nat} {expected : DemandExpectedPoint}
    {scope : Nat} {stmts : List Stmt} {value : Option Expr}
    {index : Nat} {stmt : Stmt} (env : PEnv)
    (sourceAt : DemandExpectedSourceAt m owner [index]
      (.statement stmt) .mutation expected)
    (root : demandRoot? m owner = some (.block (.mk scope stmts value)))
    (direct : DemandNode.directShrinkPlace? (.statement stmt) = some ownerPlace)
    (state : RState) (rho : List RootRef) (range : Nat × Nat) (state' : RState)
    (replay : rpBlockValue env [] (.mk scope stmts value) state =
      .ok ((rho, range), state')) :
    ∃ before roots ownerState,
      rpPlace { env with scopes := scope :: env.scopes } ownerPlace before =
        .ok (roots, ownerState) ∧
      ∀ target, target ∈ rootsTargets roots → target ∈ state'.eff.shrinks := by
  rcases sourceAt.sourceFacts.1 with ⟨sourceRoot, sourceRootEq, path⟩
  have rootEq : sourceRoot = .block (.mk scope stmts value) :=
    Option.some.inj (sourceRootEq.symm.trans root)
  subst sourceRoot
  have child : (DemandNode.block (.mk scope stmts value)).child? index =
      some (.statement stmt) := by
    cases path with
    | child hchild tail =>
      cases tail with
      | here _ => exact hchild
  have indexLookup := block_child_statement_index scope stmts value index stmt child
  exact rpBlockValue_directShrink_statement env scope stmts value index stmt ownerPlace
    state rho range state' indexLookup direct replay

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

theorem callShrinkTargets_ok (callee : Impl) (cctx : Context) (ar : List (List RootRef)) (e : Eff)
    (sm : Summary) (hs : callee.summary = .known sm) :
    ∀ t, t ∈ mapCallTargets callee cctx ar sm.shrinks →
      t ∈ (callEffects callee cctx ar e).shrinks := by
  simp only [callEffects, hs]
  exact addTargets_right _ _

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

theorem checkSummaryTargets_param_ok (m : Module) (impl : Impl) (what : String)
    (targets : List Target) (h : checkSummaryTargets m impl what targets = .ok ())
    (i : Nat) (hi : Target.param i ∈ targets) : i < impl.params.size := by
  unfold checkSummaryTargets at h
  have ht := (forAll_ok _ _).1 h _ hi
  simp only at ht
  split at ht
  · assumption
  · inv at ht

theorem checkSummary_ok (m : Module) (impl : Impl) (ctx : Context) (eff : Eff)
    (h : checkSummary m impl ctx eff = .ok ()) (sm : Summary) (hs : impl.summary = .known sm) :
    eff.unknown = false ∧
    (∀ t, t ∈ eff.reads → t ∈ expandTargets impl ctx sm.reads) ∧
    (∀ t, t ∈ eff.writes → t ∈ expandTargets impl ctx sm.writes) ∧
    (∀ t, t ∈ eff.grows → t ∈ expandTargets impl ctx sm.grows) ∧
    (∀ i, (Target.param i ∈ sm.reads ∨ Target.param i ∈ sm.writes ∨ Target.param i ∈ sm.grows) →
      i < impl.params.size) := by
  unfold checkSummary at h
  simp only [hs] at h
  inv at h
  obtain ⟨hreads, hwrites, hgrows, _, _, hu, h1, h2, h3, _, _, _, _⟩ := h
  refine ⟨by simpa using hu, effWithin_ok _ _ _ _ h1, effWithin_ok _ _ _ _ h2,
    effWithin_ok _ _ _ _ h3, ?_⟩
  intro i hi
  rcases hi with hi | hi | hi
  · exact checkSummaryTargets_param_ok m impl "reads" sm.reads hreads i hi
  · exact checkSummaryTargets_param_ok m impl "writes" sm.writes hwrites i hi
  · exact checkSummaryTargets_param_ok m impl "grows" sm.grows hgrows i hi

theorem checkSummary_shrinks_ok (m : Module) (impl : Impl) (ctx : Context) (eff : Eff)
    (h : checkSummary m impl ctx eff = .ok ()) (sm : Summary) (hs : impl.summary = .known sm) :
    ∀ t, t ∈ eff.shrinks → t ∈ expandTargets impl ctx sm.shrinks := by
  unfold checkSummary at h
  simp only [hs] at h
  inv at h
  obtain ⟨_, _, _, _, _, _, _, _, _, hshrinks, _, _, _⟩ := h
  exact effWithin_ok _ _ _ _ hshrinks

theorem checkSummary_shrinkParams_ok (m : Module) (impl : Impl) (ctx : Context) (eff : Eff)
    (h : checkSummary m impl ctx eff = .ok ()) (sm : Summary) (hs : impl.summary = .known sm) :
    ∀ i, Target.param i ∈ sm.shrinks → i < impl.params.size := by
  unfold checkSummary at h
  simp only [hs] at h
  inv at h
  obtain ⟨_, _, _, hshrinks, _⟩ := h
  intro i hi
  exact checkSummaryTargets_param_ok m impl "shrinks" sm.shrinks hshrinks i hi

theorem checkInitCall_state (env : TEnv) (callee : Impl) (s : Nat) (r : Unit × Nat)
    (h : checkInitCall env callee s = .ok r) : r.2 = s := by
  unfold checkInitCall at h
  cases hi : env.initializing with
  | none => simp only [hi] at h; inv at h; rw [h]
  | some gi =>
    simp only [hi] at h
    cases hs : callee.summary with
    | unknown => simp only [hs] at h; inv at h
    | known sm => simp only [hs] at h; inv at h; rw [h.2]

@[chk] theorem callResultTy_ok (callee : Impl) (s : Nat) (r : Ty × Nat) :
    callResultTy callee s = .ok r ↔
      ((callee.results.toList = [] ∧ r.1 = .unit) ∨ callee.results.toList = [r.1]) ∧ r.2 = s := by
  obtain ⟨t, s'⟩ := r
  unfold callResultTy
  generalize callee.results.toList = l
  match l with
  | [] => simp [st_pure_ok]
  | [t'] =>
    simp only [st_pure_ok, Prod.mk.injEq, List.cons.injEq, and_true, reduceCtorEq, false_and, false_or]
    exact ⟨fun ⟨a, b⟩ => ⟨a.symm, b⟩, fun ⟨a, b⟩ => ⟨a.symm, b⟩⟩
  | _ :: _ :: _ => simp [rej_ok]

theorem loopVarOk_ok (lv : LocalVar) (byRef : Bool) (el : Ty) (mu : Bool) (s : Nat) (r : Unit × Nat)
    (h : loopVarOk lv byRef el mu s = .ok r) :
    r.2 = s ∧ (if byRef = true then ∃ mx, lv.ty = .ref mx el else lv.ty = el) := by
  obtain ⟨u, s'⟩ := r
  unfold loopVarOk at h
  cases byRef with
  | true =>
    simp only [if_true] at h
    cases hty : lv.ty with
    | ref mx t0 =>
      simp only [hty] at h
      inv at h
      obtain ⟨he, h⟩ := h
      have he' : t0 = el := by simpa using he
      subst he'
      refine ⟨?_, by simp⟩
      rcases h with ⟨_, _, h⟩ | ⟨_, h⟩ <;> exact h
    | _ => simp only [hty] at h; inv at h
  | false =>
    simp only [Bool.false_eq_true, if_false] at h
    inv at h
    exact ⟨h.2, by simpa using h.1⟩

theorem declareIndex_ok (env : TEnv) (sc : Nat) (idx : Option VarId) (s : Nat) (r : Unit × Nat)
    (h : declareIndex env sc idx s = .ok r) :
    r.2 = s + idx.toList.length ∧ ∀ j, idx = some j → j = s ∧ ∃ lj, env.vars[j]? = some lj ∧
      lj.scope = sc ∧ lj.ty = .int .i64 := by
  obtain ⟨u, s'⟩ := r
  cases idx with
  | none =>
    simp only [declareIndex] at h; inv at h
    exact ⟨by simp [h], fun j e => by cases e⟩
  | some j =>
    simp only [declareIndex] at h; inv at h
    obtain ⟨lj, s1, hd, hty, rfl⟩ := h
    obtain ⟨hj, hv, hsc, _, hs1⟩ := declare_ok _ _ _ _ _ hd
    simp only at hv hsc hs1
    subst hs1
    refine ⟨by simp, fun j' e => ?_⟩
    cases e
    exact ⟨hj, lj, hv, hsc, by simpa using hty⟩

theorem derefVar_eq {p : Place} {x : VarId} (h : p.derefVar? = some x) :
    p = .deref (.read (.var x)) := by
  unfold Place.derefVar? at h
  split at h
  · cases h; rfl
  · cases h

theorem readRoots_ok (env : PEnv) (p : Place) (s : RState) (r : List RootRef × RState)
    (h : readRoots env p s = .ok r) :
    r.2 = s ∧
    ((∃ x lv, p = .var x ∧ env.impl.vars[x]? = some lv ∧ lv.ty.isRefLike = true ∧
        env.ann x = some r.1) ∨
      (∃ x, p = .deref (.read (.var x)) ∧ env.isRefSliceVar x = true ∧ env.cont x = some r.1) ∨
      (r.1 = [] ∧ (∀ x lv, p = .var x → env.impl.vars[x]? = some lv → lv.ty.isRefLike = false) ∧
        ∀ x, p = .deref (.read (.var x)) → env.isRefSliceVar x = false)) := by
  obtain ⟨rho, s'⟩ := r
  cases p with
  | var x =>
    simp only [readRoots] at h
    cases hv : env.impl.vars[x]? with
    | none =>
      simp only [hv] at h; inv at h
      refine ⟨h.2, Or.inr (Or.inr ⟨h.1, ?_, ?_⟩)⟩
      · intro x' lv e h'; cases e; rw [hv] at h'; cases h'
      · intro x' e; cases e
    | some lv =>
      simp only [hv] at h
      by_cases hr : lv.ty.isRefLike = true
      · simp only [hr, if_true] at h
        cases ha : env.ann x with
        | none => simp only [ha] at h; inv at h
        | some ann =>
          simp only [ha] at h; inv at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, Or.inl ⟨x, lv, rfl, hv, hr, ha⟩⟩
      · simp only [hr] at h; inv at h
        refine ⟨h.2, Or.inr (Or.inr ⟨h.1, ?_, ?_⟩)⟩
        · intro x' lv' e h'; cases e; rw [hv] at h'; cases h'; simpa using hr
        · intro x' e; cases e
  | deref e =>
    by_cases hx : ∃ x, e = .read (.var x)
    · obtain ⟨x, rfl⟩ := hx
      simp only [readRoots] at h
      by_cases hs : env.isRefSliceVar x = true
      · simp only [hs, if_true] at h
        cases hc : env.cont x with
        | none => simp only [hc] at h; inv at h
        | some cont =>
          simp only [hc] at h; inv at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, Or.inr (Or.inl ⟨x, rfl, hs, hc⟩)⟩
      · simp only [hs] at h; inv at h
        refine ⟨h.2, Or.inr (Or.inr ⟨h.1, ?_, ?_⟩)⟩
        · intro x' lv e; cases e
        · intro x' e; cases e; simpa using hs
    · have hp : readRoots env (.deref e) = pure [] := by
        cases e <;> try rfl
        rename_i p'
        cases p' <;> try rfl
        exact absurd ⟨_, rfl⟩ hx
      rw [hp] at h; inv at h
      refine ⟨h.2, Or.inr (Or.inr ⟨h.1, ?_, ?_⟩)⟩
      · intro x' lv e; cases e
      · intro x' e; cases e; exact absurd ⟨_, rfl⟩ hx
  | global g =>
    simp only [readRoots] at h; inv at h
    refine ⟨h.2, Or.inr (Or.inr ⟨h.1, ?_, ?_⟩)⟩
    · intro x' lv e; cases e
    · intro x' e; cases e
  | field p i =>
    simp only [readRoots] at h; inv at h
    refine ⟨h.2, Or.inr (Or.inr ⟨h.1, ?_, ?_⟩)⟩
    · intro x' lv e; cases e
    · intro x' e; cases e
  | elem v i o =>
    simp only [readRoots] at h; inv at h
    refine ⟨h.2, Or.inr (Or.inr ⟨h.1, ?_, ?_⟩)⟩
    · intro x' lv e; cases e
    · intro x' e; cases e

theorem checkStore_ok (env : PEnv) (p : Place) (rho : List RootRef) (h : checkStore env p rho = .ok ())
    (x : VarId) (hx : p.derefVar? = some x) (hs : env.isRefSliceVar x = true) :
    ∃ cont, env.cont x = some cont ∧ ∀ q, q ∈ rho → q ∈ cont := by
  unfold checkStore at h
  simp only [hx, hs, if_true] at h
  cases hc : env.cont x with
  | none => simp only [hc] at h; inv at h
  | some cont =>
    simp only [hc] at h; inv at h
    exact ⟨cont, rfl, subsetRoots_mem h⟩

theorem unionRoots_mem (a b : List RootRef) : ∀ q, q ∈ unionRoots a b → q ∈ a ∨ q ∈ b := by
  unfold unionRoots
  induction b generalizing a with
  | nil => intro q hq; exact Or.inl (by simpa using hq)
  | cons x xs ih =>
    intro q hq
    simp only [List.foldl_cons] at hq
    rcases ih _ q hq with h | h
    · split at h
      · exact Or.inl h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp at h; simp [h])
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- Where a caller root of a mapped root set comes from. -/
def FromRoot (ar : List (List RootRef)) (q : RootRef) : RootRef → Prop
  | .param j => ∃ a, ar[j]? = some a ∧ q ∈ a
  | .global g => q = .global g
  | .local _ => False

theorem mapResultRoots_sub (ar : List (List RootRef)) : ∀ (rs acc out : List RootRef),
    mapResultRoots ar acc rs = .ok out →
    ∀ q, q ∈ out → q ∈ acc ∨ ∃ r, r ∈ rs ∧ FromRoot ar q r
  | [], acc, out, h, q, hq => by
    simp only [mapResultRoots, ex_pure_ok] at h
    subst h
    exact Or.inl hq
  | r :: rest, acc, out, h, q, hq => by
    simp only [mapResultRoots, ex_bind_ok] at h
    obtain ⟨mapped, h1, h2⟩ := h
    rcases mapResultRoots_sub ar rest _ out h2 q hq with h3 | ⟨r', hr', hf⟩
    · rcases unionRoots_mem _ _ q h3 with h4 | h4
      · exact Or.inl h4
      · refine Or.inr ⟨r, List.mem_cons_self, ?_⟩
        cases r with
        | «local» y => simp only [mapCalleeRoots] at h1; inv at h1
        | global g =>
          simp only [mapCalleeRoots, ex_pure_ok] at h1
          subst h1
          have h5 : q = RootRef.global g := by simpa using h4
          exact h5
        | param j =>
          simp only [mapCalleeRoots] at h1
          cases ha : ar[j]? with
          | none => simp only [ha] at h1; inv at h1
          | some a =>
            simp only [ha, ex_pure_ok] at h1
            subst h1
            exact ⟨mapped, ha, h4⟩
    · exact Or.inr ⟨r', List.mem_cons_of_mem _ hr', hf⟩

theorem checkContent_ok (env : PEnv) (cctx : Context) (args : List Arg) (ars : List (List RootRef))
    (i : Nat) (cont : List RootRef) (h : checkContent env cctx args ars i = .ok ())
    (hc : (cctx.contentRoots.find? (·.1 == i)).map (·.2) = some cont) :
    ∃ inst, mapResultRoots ars [] cont = .ok inst ∧
      ((∃ mu s ann, args[i]? = some (.byRef mu (.var s)) ∧ env.ann s = some ann ∧
          (∀ q, q ∈ ann → q ∈ inst) ∧ bindRootsV env env.scopes s inst = .ok ()) ∨
        (∃ mu q cq, args[i]? = some (.byRef mu (.deref (.read (.var q)))) ∧ env.cont q = some cq ∧
          (∀ r, r ∈ inst → r ∈ cq) ∧ (∀ r, r ∈ cq → r ∈ inst))) := by
  unfold checkContent at h
  simp only [hc] at h
  inv at h
  obtain ⟨inst, h1, h2⟩ := h
  refine ⟨inst, h1, ?_⟩
  split at h2
  · rename_i mu s ha
    cases hann : env.ann s with
    | none => simp only [hann] at h2; inv at h2
    | some ann =>
      simp only [hann] at h2; inv at h2
      have hb : bindRootsV env env.scopes s inst = .ok () := by
        have h3 := h2.2
        unfold asCall at h3
        split at h3
        · assumption
        · cases h3
      exact Or.inl ⟨mu, s, ann, ha, hann, subsetRoots_mem h2.1, hb⟩
  · rename_i mu q ha
    cases hcq : env.cont q with
    | none => simp only [hcq] at h2; inv at h2
    | some cq =>
      simp only [hcq] at h2; inv at h2
      simp only [Bool.and_eq_true] at h2
      exact Or.inr ⟨mu, q, cq, ha, hcq, subsetRoots_mem h2.1, subsetRoots_mem h2.2⟩
  · inv at h2

theorem checkContents_ok (env : PEnv) (c : ContextId) (args : List Arg) (ars : List (List RootRef))
    (cctx : Context) (h : checkContents env c args ars = .ok ())
    (hc : env.mod.contexts[c]? = some cctx) :
    ∀ i, i < args.length → checkContent env cctx args ars i = .ok () := by
  unfold checkContents at h
  simp only [hc] at h
  intro i hi
  exact (forAll_ok _ _).1 h i (List.mem_range.2 hi)

theorem retUnit_ok (env : TEnv) (s : Nat) (r : Unit × Nat) (h : retUnit env s = .ok r) :
    r.2 = s ∧ env.inExpr = false ∧ ∃ impl, env.impl = some impl ∧ impl.results.toList = [] := by
  obtain ⟨u, s'⟩ := r
  unfold retUnit at h
  cases hi : env.inExpr with
  | true => simp only [hi] at h; inv at h
  | false =>
    cases him : env.impl with
    | none => simp only [hi, him] at h; inv at h
    | some impl =>
      simp only [hi, him] at h
      rcases hres : impl.results.toList with _ | ⟨t, rest⟩ <;> simp only [hres] at h <;> inv at h
      exact ⟨h, rfl, impl, rfl, hres⟩

theorem retTy_ok (env : TEnv) (s : Nat) (r : Ty × Nat) (h : retTy env s = .ok r) :
    r.2 = s ∧ env.inExpr = false ∧ ∃ impl, env.impl = some impl ∧ impl.results.toList = [r.1] := by
  obtain ⟨t, s'⟩ := r
  unfold retTy at h
  cases hi : env.inExpr with
  | true => simp only [hi] at h; inv at h
  | false =>
    cases him : env.impl with
    | none => simp only [hi, him] at h; inv at h
    | some impl =>
      simp only [hi, him] at h
      rcases hres : impl.results.toList with _ | ⟨t', _ | _⟩ <;> simp only [hres] at h <;> inv at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, impl, rfl, hres⟩

theorem rpBlockValue_rng (env : PEnv) (pre : List VarId) (b : Block) (st : RState)
    (rho : List RootRef) (rng : Nat × Nat) (st' : RState)
    (h : rpBlockValue env pre b st = .ok ((rho, rng), st')) : rng.1 = st.nextVar := by
  obtain ⟨sc, stmts, value⟩ := b
  obtain ⟨_, _, _, _, _, hr⟩ := rpBlockValue_ok _ _ _ _ _ _ _ _ _ h
  exact hr

end Goose.Core.Sound
