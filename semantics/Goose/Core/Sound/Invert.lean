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
    (state state' : RState) (result : List RootRef)
    (hreplay : rpExpr env (.pop owner org) state = .ok (result, state')) :
    ∃ roots ownerState, rpPlace env owner state = .ok (roots, ownerState) ∧
      ∀ target, target ∈ rootsTargets roots → target ∈ state'.eff.shrinks := by
  simp only [rpExpr] at hreplay
  rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨roots, ownerState, hplace, hrest⟩
  rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, _, _, hrest⟩
  rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, mid, hshrink, htail⟩
  rcases (st_bind_ok _ _ _ _).1 htail with ⟨_, afterAbort, habort, hpure⟩
  have hpureEq : (result, state') = ([], afterAbort) :=
    (st_pure_ok [] afterAbort (result, state')).1 hpure
  have hstate : state' = afterAbort := congrArg Prod.snd hpureEq
  refine ⟨roots, ownerState, hplace, ?_⟩
  intro target htarget
  have hrecorded := (addShrinks_ok roots _ ((), mid) hshrink).2 target htarget
  have hafterAbort := (PMono.noteAborts _ _ _ habort).2.2.2.2.1 target hrecorded
  simpa [hstate] using hafterAbort

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

private theorem rpExprs_member_replay (env : PEnv) (exprs : List Expr)
    (index : Nat) (expr : Expr) (state state' : RState)
    (hindex : exprs[index]? = some expr)
    (hreplay : rpExprs env exprs state = .ok ((), state')) :
    ∃ before after roots, rpExpr env expr before = .ok (roots, after) ∧
      RLe after state' := by
  induction exprs generalizing index expr state state' with
  | nil => simp at hindex
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hindex
      subst expr
      simp only [rpExprs] at hreplay
      rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨roots, afterExpr, hhead, htail⟩
      refine ⟨state, afterExpr, roots, hhead, ?_⟩
      exact (rp_mono_all.2.2.2.1 env tail) _ _ _ htail
    | succ index =>
      have htailIndex : tail[index]? = some expr := by simpa using hindex
      simp only [rpExprs] at hreplay
      rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨_, mid, _, htail⟩
      exact ih index expr mid state' htailIndex htail

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

/-- Replay output follows the syntax family of each demand node. -/
def DemandNode.replayOutput : DemandNode → Type
  | .expression _ | .place _ | .view _ => List RootRef
  | .bound _ | .statement _ => Unit
  | .block _ => Prod (List RootRef) (Nat × Nat)

/-- Run the root replay for a demand node without erasing its family result. -/
def rpDemandNode (env : PEnv) (node : DemandNode) : P (DemandNode.replayOutput node) :=
  match node with
  | .expression expr => rpExpr env expr
  | .place place => rpPlace env place
  | .view view => rpView env view
  | .bound bound => rpBound env bound
  | .statement statement => rpStmt env statement
  | .block block => rpBlockValue env [] block

def DemandNode.ofArg : Arg → DemandNode
  | .byVal expr => .expression expr
  | .byRef _ place => .place place

/-- A child replay records the lexical environment and state at that source edge. -/
def DemandNodeReplayChild (parentEnv : PEnv) (parent : DemandNode) (index : Nat)
    (child : DemandNode) (parentBefore parentAfter : RState) : Prop :=
  parent.child? index = some child ∧
  ∃ parentOutput : DemandNode.replayOutput parent,
    rpDemandNode parentEnv parent parentBefore = .ok (parentOutput, parentAfter) ∧
  ∃ childEnv childBefore childAfter childOutput,
    childEnv.mod = parentEnv.mod ∧
    childEnv.impl = parentEnv.impl ∧
    childEnv.ctx = parentEnv.ctx ∧
    rpDemandNode childEnv child childBefore = .ok (childOutput, childAfter) ∧
      RLe childAfter parentAfter

theorem rpDemandNode_directShrink_targets (env : PEnv) (node : DemandNode)
    (owner : Place) (before after : RState)
    (hdirect : node.directShrinkPlace? = some owner)
    (hreplay : ∃ output, rpDemandNode env node before = .ok (output, after)) :
    ∃ roots ownerState, rpPlace env owner before = .ok (roots, ownerState) ∧
      ∀ target, target ∈ rootsTargets roots → target ∈ after.eff.shrinks := by
  cases node with
  | expression expr =>
    cases expr <;> simp only [DemandNode.directShrinkPlace?] at hdirect
    case pop place origin =>
      have howner : place = owner := by
        exact Option.some.inj hdirect
      subst owner
      rcases hreplay with ⟨output, hExpr⟩
      have hpop : rpExpr env (.pop place origin) before = .ok (output, after) := by
        simpa [rpDemandNode, DemandNode.replayOutput] using hExpr
      exact rpExpr_pop_targets env place origin before after output hpop
    all_goals cases hdirect
  | statement stmt =>
    rcases hreplay with ⟨output, hstmt⟩
    have houtput : output = () := by
      cases output
      rfl
    subst output
    have hrun : rpStmt env stmt before = .ok ((), after) := by
      simpa [rpDemandNode, DemandNode.replayOutput] using hstmt
    exact rpStmt_directShrink_targets env stmt owner before after hdirect hrun
  | place _ | view _ | bound _ | block _ =>
    simp [DemandNode.directShrinkPlace?] at hdirect

theorem DemandNodeAt.directShrink_replay
    {root node : DemandNode} {path : List Nat}
    (source : DemandNodeAt root path node)
    (env : PEnv) (before after : RState)
    (hreplay : ∃ output, rpDemandNode env root before = .ok (output, after))
    (owner : Place) (hdirect : node.directShrinkPlace? = some owner)
    (childReplay : ∀ {parentEnv parent index child parentBefore parentAfter},
      parent.child? index = some child →
      (∃ output, rpDemandNode parentEnv parent parentBefore = .ok (output, parentAfter)) →
      DemandNodeReplayChild parentEnv parent index child parentBefore parentAfter) :
    ∃ leafEnv leafBefore roots ownerState,
      leafEnv.mod = env.mod ∧ leafEnv.impl = env.impl ∧ leafEnv.ctx = env.ctx ∧
      rpPlace leafEnv owner leafBefore = .ok (roots, ownerState) ∧
      ∀ target, target ∈ rootsTargets roots → target ∈ after.eff.shrinks := by
  induction source generalizing env before after with
  | here current =>
    obtain ⟨output, hcurrent⟩ := hreplay
    obtain ⟨roots, ownerState, howner, hrecorded⟩ :=
      rpDemandNode_directShrink_targets env current owner before after hdirect ⟨output, hcurrent⟩
    exact ⟨env, before, roots, ownerState, rfl, rfl, rfl, howner, hrecorded⟩
  | @child parent current target index path hchild hpath ih =>
    obtain ⟨parentOutput, hparent⟩ := hreplay
    obtain ⟨_, edgeOutput, hEdgeReplay, childEnv, childBefore, childAfter,
      childOutput, hmod, himpl, hctx, hchildReplay, hmono⟩ :=
      childReplay hchild ⟨parentOutput, hparent⟩
    have houtputEq : edgeOutput = parentOutput := by
      have heq : (edgeOutput, after) = (parentOutput, after) :=
        (Except.ok.inj (hEdgeReplay.symm.trans hparent))
      exact congrArg Prod.fst heq
    subst edgeOutput
    obtain ⟨leafEnv, leafBefore, roots, ownerState, hleafMod, hleafImpl, hleafCtx,
      howner, hrecorded⟩ :=
      ih childEnv childBefore childAfter ⟨childOutput, hchildReplay⟩ hdirect
    refine ⟨leafEnv, leafBefore, roots, ownerState,
      hleafMod.trans hmod, hleafImpl.trans himpl, hleafCtx.trans hctx, howner, ?_⟩
    intro target htarget
    exact (hmono.2.2.2.2.1 target (hrecorded target htarget))

private theorem demandNodeChild_mem_children {parent child : DemandNode} {index : Nat}
    (hchild : parent.child? index = some child) : some child ∈ parent.children := by
  unfold DemandNode.child? at hchild
  have hentry : parent.children[index]? = some (some child) := by
    cases hindex : parent.children[index]? with
    | none => simp [hindex] at hchild
    | some entry =>
      cases entry with
      | none => simp [hindex] at hchild
      | some found =>
        have heq : found = child := by simpa [hindex] using hchild
        subst found
        rfl
  exact List.mem_of_getElem? hentry

private theorem demandNodeReplayChild_ofParts
    (parentEnv : PEnv) (parent : DemandNode) (index : Nat) (child : DemandNode)
    (parentBefore parentAfter : RState) (parentOutput : DemandNode.replayOutput parent)
    (hchild : parent.child? index = some child)
    (hparent : rpDemandNode parentEnv parent parentBefore = .ok (parentOutput, parentAfter))
    (childEnv : PEnv) (childBefore childAfter : RState)
    (childOutput : DemandNode.replayOutput child)
    (hmod : childEnv.mod = parentEnv.mod) (himpl : childEnv.impl = parentEnv.impl)
    (hctx : childEnv.ctx = parentEnv.ctx)
    (hchildReplay : rpDemandNode childEnv child childBefore = .ok (childOutput, childAfter))
    (hmono : RLe childAfter parentAfter) :
    DemandNodeReplayChild parentEnv parent index child parentBefore parentAfter := by
  exact ⟨hchild, parentOutput, hparent, childEnv, childBefore, childAfter, childOutput,
    hmod, himpl, hctx, hchildReplay, hmono⟩

private theorem demandNodeExpressionChild_ofParts
    (env : PEnv) (parentExpr childExpr : Expr) (index : Nat)
    (before after childBefore childAfter : RState) (roots childRoots : List RootRef)
    (hchild : (DemandNode.expression parentExpr).child? index =
      some (.expression childExpr))
    (hparent : rpDemandNode env (.expression parentExpr) before = .ok (roots, after))
    (hchildReplay : rpExpr env childExpr childBefore = .ok (childRoots, childAfter))
    (hmono : RLe childAfter after) :
    DemandNodeReplayChild env (.expression parentExpr) index (.expression childExpr)
      before after := by
  have hchildReplay' : rpDemandNode env (.expression childExpr) childBefore =
      .ok (childRoots, childAfter) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hchildReplay
  exact demandNodeReplayChild_ofParts env (.expression parentExpr) index
    (.expression childExpr) before after roots hchild hparent env childBefore childAfter
    childRoots rfl rfl rfl hchildReplay' hmono

theorem rpDemandNode_mono (env : PEnv) (node : DemandNode) (before after : RState)
    (output : DemandNode.replayOutput node)
    (hreplay : rpDemandNode env node before = .ok (output, after)) :
    RLe before after := by
  cases node with
  | expression expr => exact rpExpr_mono hreplay
  | place place => exact rpPlace_mono hreplay
  | view view => exact rpView_mono hreplay
  | bound bound => exact rpBound_mono hreplay
  | statement statement => exact rpStmt_mono hreplay
  | block block => exact rpBlockValue_mono hreplay

private theorem rpArgs_member_replay (env : PEnv) (args : List Arg)
    (index : Nat) (arg : Arg) (state state' : RState)
    (argRoots : List (List RootRef)) (hindex : args[index]? = some arg)
    (hreplay : rpArgs env args state = .ok (argRoots, state')) :
    ∃ childBefore childAfter childRoots,
      rpDemandNode env (DemandNode.ofArg arg) childBefore = .ok (childRoots, childAfter) ∧
        RLe childAfter state' := by
  induction args generalizing index arg state state' argRoots with
  | nil => simp at hindex
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hindex
      subst arg
      cases head with
      | byVal expr =>
        simp only [rpArgs] at hreplay
        rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨roots, childAfter, hexpr, htail⟩
        refine ⟨state, childAfter, roots, ?_, ?_⟩
        · simpa [DemandNode.ofArg, rpDemandNode, DemandNode.replayOutput] using hexpr
        · have htailMono : PMono
            (rpArgs env tail >>= fun tailRoots => pure (roots :: tailRoots)) :=
              PMono.bind (by
                intro before result after h
                exact rpArgs_mono h) (fun _ => PMono.pure _)
          exact htailMono _ _ _ htail
      | byRef mutability place =>
        simp only [rpArgs] at hreplay
        rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨roots, childAfter, hplace, htail⟩
        refine ⟨state, childAfter, roots, ?_, ?_⟩
        · simpa [DemandNode.ofArg, rpDemandNode, DemandNode.replayOutput] using hplace
        · have htailMono : PMono
            (rpArgs env tail >>= fun tailRoots => pure (roots :: tailRoots)) :=
              PMono.bind (by
                intro before result after h
                exact rpArgs_mono h) (fun _ => PMono.pure _)
          exact htailMono _ _ _ htail
    | succ index =>
      have htailIndex : tail[index]? = some arg := by simpa using hindex
      cases head with
      | byVal expr =>
        simp only [rpArgs] at hreplay
        rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨roots, mid, _, htail⟩
        rcases (st_bind_ok _ _ _ _).1 htail with ⟨tailRoots, finalState, htailArgs, hpure⟩
        have hpureEq := (st_pure_ok _ _ _).1 hpure
        cases hpureEq
        exact ih index arg mid state' tailRoots htailIndex htailArgs
      | byRef mutability place =>
        simp only [rpArgs] at hreplay
        rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨roots, mid, _, htail⟩
        rcases (st_bind_ok _ _ _ _).1 htail with ⟨tailRoots, finalState, htailArgs, hpure⟩
        have hpureEq := (st_pure_ok _ _ _).1 hpure
        cases hpureEq
        exact ih index arg mid state' tailRoots htailIndex htailArgs

theorem rpDemandNode_expression_callArg_child
    (env : PEnv) (context : ContextId) (args : List Arg) (origin : OriginId)
    (index : Nat) (arg : Arg) (before after : RState) (roots : List RootRef)
    (hindex : args[index]? = some arg)
    (hchild : (DemandNode.expression (.call context args origin)).child? index =
      some (DemandNode.ofArg arg))
    (hreplay : rpDemandNode env (.expression (.call context args origin)) before =
      .ok (roots, after)) :
    DemandNodeReplayChild env (.expression (.call context args origin)) index
      (DemandNode.ofArg arg) before after := by
  have hcall : rpExpr env (.call context args origin) before = .ok (roots, after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpExpr] at hcall
  rcases (st_bind_ok _ _ _ _).1 hcall with ⟨argRoots, argsAfter, hargs, htail⟩
  have htailMono : PMono (do
      liftV (checkContents env context args argRoots)
      rpCall env context argRoots) :=
    PMono.bind (PMono.liftV _) (fun _ => PMono.rpCall env context argRoots)
  obtain ⟨childBefore, childAfter, childRoots, harg, hmonoArgs⟩ :=
    rpArgs_member_replay env args index arg before argsAfter argRoots hindex hargs
  refine ⟨hchild, roots, hreplay, env, childBefore, childAfter, childRoots, ?_⟩
  exact ⟨rfl, rfl, rfl,
    by simpa [rpDemandNode, DemandNode.replayOutput] using harg,
    hmonoArgs.trans (htailMono _ _ _ htail)⟩

theorem rpDemandNode_expression_read_place_child
    (env : PEnv) (place : Place) (index : Nat) (before after : RState)
    (roots : List RootRef)
    (hchild : (DemandNode.expression (.read place)).child? index = some (.place place))
    (hreplay : rpDemandNode env (.expression (.read place)) before = .ok (roots, after)) :
    DemandNodeReplayChild env (.expression (.read place)) index (.place place) before after := by
  have hexpr : rpExpr env (.read place) before = .ok (roots, after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpExpr] at hexpr
  rcases (st_bind_ok _ _ _ _).1 hexpr with ⟨placeRoots, afterPlace, hplace, htail⟩
  have htailMono : PMono (do addReads placeRoots; readRoots env place) :=
    PMono.bind (PMono.addReads placeRoots) (fun _ => PMono.readRoots env place)
  have hplaceReplay : rpDemandNode env (.place place) before =
      .ok (placeRoots, afterPlace) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hplace
  refine demandNodeReplayChild_ofParts env (.expression (.read place)) index (.place place)
    before after roots hchild hreplay env before afterPlace placeRoots rfl rfl rfl
    hplaceReplay ?_
  exact htailMono _ _ _ htail

theorem rpDemandNode_expression_ref_place_child
    (env : PEnv) (mutability : Mutability) (place : Place) (index : Nat)
    (before after : RState) (roots : List RootRef)
    (hchild : (DemandNode.expression (.ref mutability place)).child? index =
      some (.place place))
    (hreplay : rpDemandNode env (.expression (.ref mutability place)) before =
      .ok (roots, after)) :
    DemandNodeReplayChild env (.expression (.ref mutability place)) index (.place place)
      before after := by
  have hplace : rpPlace env place before = .ok (roots, after) := by
    simpa [rpDemandNode, DemandNode.replayOutput, rpExpr] using hreplay
  have hplaceReplay : rpDemandNode env (.place place) before = .ok (roots, after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hplace
  exact demandNodeReplayChild_ofParts env (.expression (.ref mutability place)) index
    (.place place) before after roots hchild hreplay env before after roots rfl rfl rfl
    hplaceReplay (RLe.refl _)

theorem rpDemandNode_expression_pop_place_child
    (env : PEnv) (place : Place) (origin : OriginId) (index : Nat)
    (before after : RState) (roots : List RootRef)
    (hchild : (DemandNode.expression (.pop place origin)).child? index = some (.place place))
    (hreplay : rpDemandNode env (.expression (.pop place origin)) before =
      .ok (roots, after)) :
    DemandNodeReplayChild env (.expression (.pop place origin)) index (.place place)
      before after := by
  have hexpr : rpExpr env (.pop place origin) before = .ok (roots, after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpExpr] at hexpr
  rcases (st_bind_ok _ _ _ _).1 hexpr with ⟨placeRoots, afterPlace, hplace, htail⟩
  have htailMono : PMono (do
      addReads placeRoots
      addShrinks placeRoots
      noteAborts
      pure ([] : List RootRef)) :=
    PMono.bind (PMono.addReads placeRoots) (fun _ =>
      PMono.bind (PMono.addShrinks placeRoots) (fun _ =>
        PMono.bind PMono.noteAborts (fun _ => PMono.pure ([] : List RootRef))))
  have hplaceReplay : rpDemandNode env (.place place) before =
      .ok (placeRoots, afterPlace) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hplace
  refine demandNodeReplayChild_ofParts env (.expression (.pop place origin)) index
    (.place place) before after roots hchild hreplay env before afterPlace placeRoots rfl rfl rfl
    hplaceReplay ?_
  exact htailMono _ _ _ htail

theorem rpDemandNode_expression_un_child
    (env : PEnv) (op : UnOp) (expr : Expr) (origin : OriginId) (index : Nat)
    (before after : RState)
    (hchild : (DemandNode.expression (.un op expr origin)).child? index =
      some (.expression expr))
    (hreplay : rpDemandNode env (.expression (.un op expr origin)) before =
      .ok ([], after)) :
    DemandNodeReplayChild env (.expression (.un op expr origin)) index
      (.expression expr) before after := by
  have hparent : rpDemandNode env (.expression (.un op expr origin)) before =
      .ok ([], after) := hreplay
  simp only [rpDemandNode, rpExpr] at hparent
  rcases (st_bind_ok _ _ _ _).1 hparent with ⟨childRoots, childAfter, hExpr, htail⟩
  have hchildReplay : rpExpr env expr before = .ok (childRoots, childAfter) := by
    simpa [rpExpr] using hExpr
  cases op with
  | neg =>
    have htailMono : PMono (do noteAborts; pure ([] : List RootRef)) :=
      PMono.bind PMono.noteAborts (fun _ => PMono.pure ([] : List RootRef))
    have hmono := htailMono _ _ _ htail
    exact demandNodeExpressionChild_ofParts env (.un .neg expr origin) expr index before after
      before childAfter [] childRoots hchild hparent hchildReplay hmono
  | bitnot =>
    have htailMono : PMono (pure ([] : List RootRef)) := PMono.pure []
    have hmono := htailMono _ _ _ htail
    exact demandNodeExpressionChild_ofParts env (.un .bitnot expr origin) expr index before after
      before childAfter [] childRoots hchild hparent hchildReplay hmono

theorem rpDemandNode_expression_not_child
    (env : PEnv) (expr : Expr) (index : Nat) (before after : RState)
    (hchild : (DemandNode.expression (.not expr)).child? index =
      some (.expression expr))
    (hreplay : rpDemandNode env (.expression (.not expr)) before = .ok ([], after)) :
    DemandNodeReplayChild env (.expression (.not expr)) index (.expression expr)
      before after := by
  have hparent : rpDemandNode env (.expression (.not expr)) before = .ok ([], after) := hreplay
  simp only [rpDemandNode, rpExpr] at hparent
  rcases (st_bind_ok _ _ _ _).1 hparent with ⟨childRoots, childAfter, hExpr, htail⟩
  have hchildReplay : rpExpr env expr before = .ok (childRoots, childAfter) := by
    simpa [rpExpr] using hExpr
  have htailMono : PMono (pure ([] : List RootRef)) := PMono.pure []
  exact demandNodeExpressionChild_ofParts env (.not expr) expr index before after before childAfter
    [] childRoots hchild hparent hchildReplay (htailMono _ _ _ htail)

theorem rpDemandNode_expression_fill_child
    (env : PEnv) (ty : Ty) (expr : Expr) (index : Nat) (before after : RState)
    (hchild : (DemandNode.expression (.fill ty expr)).child? index =
      some (.expression expr))
    (hreplay : rpDemandNode env (.expression (.fill ty expr)) before = .ok ([], after)) :
    DemandNodeReplayChild env (.expression (.fill ty expr)) index (.expression expr)
      before after := by
  have hparent : rpDemandNode env (.expression (.fill ty expr)) before = .ok ([], after) := hreplay
  simp only [rpDemandNode, rpExpr] at hparent
  rcases (st_bind_ok _ _ _ _).1 hparent with ⟨childRoots, childAfter, hExpr, htail⟩
  have hchildReplay : rpExpr env expr before = .ok (childRoots, childAfter) := by
    simpa [rpExpr] using hExpr
  have htailMono : PMono (pure ([] : List RootRef)) := PMono.pure []
  exact demandNodeExpressionChild_ofParts env (.fill ty expr) expr index before after before
    childAfter [] childRoots hchild hparent hchildReplay (htailMono _ _ _ htail)

theorem rpDemandNode_expression_conv_child
    (env : PEnv) (kind : ConvKind) (target : Ty) (expr : Expr) (origin : OriginId)
    (index : Nat) (before after : RState)
    (hchild : (DemandNode.expression (.conv kind target expr origin)).child? index =
      some (.expression expr))
    (hreplay : rpDemandNode env (.expression (.conv kind target expr origin)) before =
      .ok ([], after)) :
    DemandNodeReplayChild env (.expression (.conv kind target expr origin)) index
      (.expression expr) before after := by
  have hparent : rpDemandNode env (.expression (.conv kind target expr origin)) before =
      .ok ([], after) := hreplay
  simp only [rpDemandNode, rpExpr] at hparent
  rcases (st_bind_ok _ _ _ _).1 hparent with ⟨childRoots, childAfter, hExpr, htail⟩
  have hchildReplay : rpExpr env expr before = .ok (childRoots, childAfter) := by
    simpa [rpExpr] using hExpr
  cases kind with
  | widen =>
    have htailMono : PMono (pure ([] : List RootRef)) := PMono.pure []
    exact demandNodeExpressionChild_ofParts env (.conv .widen target expr origin) expr index
      before after before childAfter [] childRoots hchild hparent hchildReplay (htailMono _ _ _ htail)
  | as =>
    have htailMono : PMono (do noteAborts; pure ([] : List RootRef)) :=
      PMono.bind PMono.noteAborts (fun _ => PMono.pure ([] : List RootRef))
    exact demandNodeExpressionChild_ofParts env (.conv .as target expr origin) expr index
      before after before childAfter [] childRoots hchild hparent hchildReplay (htailMono _ _ _ htail)
  | asUnchecked =>
    have htailMono : PMono (pure ([] : List RootRef)) := PMono.pure []
    exact demandNodeExpressionChild_ofParts env (.conv .asUnchecked target expr origin) expr index
      before after before childAfter [] childRoots hchild hparent hchildReplay (htailMono _ _ _ htail)

theorem rpDemandNode_expression_len_view_child
    (env : PEnv) (view : View) (index : Nat) (before after : RState)
    (hchild : (DemandNode.expression (.len view)).child? index = some (.view view))
    (hreplay : rpDemandNode env (.expression (.len view)) before = .ok ([], after)) :
    DemandNodeReplayChild env (.expression (.len view)) index (.view view) before after := by
  have hparent : rpDemandNode env (.expression (.len view)) before = .ok ([], after) := hreplay
  simp only [rpDemandNode, rpExpr] at hparent
  rcases (st_bind_ok _ _ _ _).1 hparent with ⟨viewRoots, viewAfter, hview, htail⟩
  have htailMono : PMono (pure ([] : List RootRef)) := PMono.pure []
  have hviewReplay : rpDemandNode env (.view view) before = .ok (viewRoots, viewAfter) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hview
  refine demandNodeReplayChild_ofParts env (.expression (.len view)) index (.view view)
    before after [] hchild hreplay env before viewAfter viewRoots rfl rfl rfl hviewReplay ?_
  exact htailMono _ _ _ htail

theorem rpDemandNode_expression_slice_view_child
    (env : PEnv) (mutability : Mutability) (view : View) (lower upper : Bound)
    (origin : OriginId) (index : Nat) (before after : RState) (roots : List RootRef)
    (hchild : (DemandNode.expression (.slice mutability view lower upper origin)).child?
      index = some (.view view))
    (hreplay : rpDemandNode env
      (.expression (.slice mutability view lower upper origin)) before = .ok (roots, after)) :
    DemandNodeReplayChild env (.expression (.slice mutability view lower upper origin)) index
      (.view view) before after := by
  have hparent : rpDemandNode env
      (.expression (.slice mutability view lower upper origin)) before = .ok (roots, after) := hreplay
  simp only [rpDemandNode, rpExpr] at hparent
  rcases (st_bind_ok _ _ _ _).1 hparent with ⟨viewRoots, viewAfter, hview, htail⟩
  have htailMono : PMono (do
      rpBound env lower
      rpBound env upper
      noteAborts
      pure viewRoots) :=
    PMono.bind (by
      intro st result st' h
      exact rpBound_mono h) (fun _ =>
        PMono.bind (by
          intro st result st' h
          exact rpBound_mono h) (fun _ =>
          PMono.bind PMono.noteAborts (fun _ => PMono.pure viewRoots)))
  have hviewReplay : rpDemandNode env (.view view) before = .ok (viewRoots, viewAfter) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hview
  refine demandNodeReplayChild_ofParts env
    (.expression (.slice mutability view lower upper origin)) index (.view view)
    before after roots hchild hreplay env before viewAfter viewRoots rfl rfl rfl hviewReplay ?_
  exact htailMono _ _ _ htail

theorem rpDemandNode_expression_slice_lower_child
    (env : PEnv) (mutability : Mutability) (view : View) (lower upper : Bound)
    (origin : OriginId) (index : Nat) (before after : RState) (roots : List RootRef)
    (hchild : (DemandNode.expression (.slice mutability view lower upper origin)).child?
      index = some (.bound lower))
    (hreplay : rpDemandNode env
      (.expression (.slice mutability view lower upper origin)) before = .ok (roots, after)) :
    DemandNodeReplayChild env (.expression (.slice mutability view lower upper origin)) index
      (.bound lower) before after := by
  have hparent : rpDemandNode env
      (.expression (.slice mutability view lower upper origin)) before = .ok (roots, after) := hreplay
  simp only [rpDemandNode, rpExpr] at hparent
  rcases (st_bind_ok _ _ _ _).1 hparent with ⟨viewRoots, viewAfter, _, htail⟩
  rcases (st_bind_ok _ _ _ _).1 htail with ⟨_, lowerAfter, hlower, htail⟩
  have htailMono : PMono (do rpBound env upper; noteAborts; pure viewRoots) :=
    PMono.bind (by
      intro st result st' h
      exact rpBound_mono h) (fun _ =>
        PMono.bind PMono.noteAborts (fun _ => PMono.pure viewRoots))
  have hlowerReplay : rpDemandNode env (.bound lower) viewAfter = .ok ((), lowerAfter) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hlower
  refine demandNodeReplayChild_ofParts env
    (.expression (.slice mutability view lower upper origin)) index (.bound lower)
    before after roots hchild hreplay env viewAfter lowerAfter () rfl rfl rfl hlowerReplay ?_
  exact htailMono _ _ _ htail

theorem rpDemandNode_expression_slice_upper_child
    (env : PEnv) (mutability : Mutability) (view : View) (lower upper : Bound)
    (origin : OriginId) (index : Nat) (before after : RState) (roots : List RootRef)
    (hchild : (DemandNode.expression (.slice mutability view lower upper origin)).child?
      index = some (.bound upper))
    (hreplay : rpDemandNode env
      (.expression (.slice mutability view lower upper origin)) before = .ok (roots, after)) :
    DemandNodeReplayChild env (.expression (.slice mutability view lower upper origin)) index
      (.bound upper) before after := by
  have hparent : rpDemandNode env
      (.expression (.slice mutability view lower upper origin)) before = .ok (roots, after) := hreplay
  simp only [rpDemandNode, rpExpr] at hparent
  rcases (st_bind_ok _ _ _ _).1 hparent with ⟨viewRoots, viewAfter, _, htail⟩
  rcases (st_bind_ok _ _ _ _).1 htail with ⟨_, lowerAfter, _, htail⟩
  rcases (st_bind_ok _ _ _ _).1 htail with ⟨_, upperAfter, hupper, htail⟩
  have htailMono : PMono (do noteAborts; pure viewRoots) :=
    PMono.bind PMono.noteAborts (fun _ => PMono.pure viewRoots)
  have hupperReplay : rpDemandNode env (.bound upper) lowerAfter = .ok ((), upperAfter) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hupper
  refine demandNodeReplayChild_ofParts env
    (.expression (.slice mutability view lower upper origin)) index (.bound upper)
    before after roots hchild hreplay env lowerAfter upperAfter () rfl rfl rfl hupperReplay ?_
  exact htailMono _ _ _ htail

theorem rpDemandNode_expression_push_owner_child
    (env : PEnv) (owner : Place) (expr : Expr) (origin : Option OriginId)
    (index : Nat) (before after : RState) (roots : List RootRef)
    (hchild : (DemandNode.expression (.push owner expr origin)).child? index =
      some (.place owner))
    (hreplay : rpDemandNode env (.expression (.push owner expr origin)) before =
      .ok (roots, after)) :
    DemandNodeReplayChild env (.expression (.push owner expr origin)) index (.place owner)
      before after := by
  have hparent : rpDemandNode env (.expression (.push owner expr origin)) before =
      .ok (roots, after) := hreplay
  simp only [rpDemandNode, rpExpr] at hparent
  rcases (st_bind_ok _ _ _ _).1 hparent with ⟨ownerRoots, ownerAfter, howner, htail⟩
  have hexprMono : ∀ {st a st'}, rpExpr env expr st = .ok (a, st') → RLe st st' :=
    fun h => rpExpr_mono h
  have htailMono : PMono (do
      let _ ← rpExpr env expr
      addGrows ownerRoots
      if env.mod.profile == .shrink then do
        addWrites ownerRoots
        if (← liftV (env.limitedOwner owner)) then noteAborts
      pure ownerRoots) :=
    PMono.bind (by
      intro st result st' h
      exact hexprMono h) (fun _ =>
        PMono.bind (PMono.addGrows ownerRoots) (fun _ =>
          PMono.profileWriteAbortValue env owner ownerRoots))
  have hownerReplay : rpDemandNode env (.place owner) before = .ok (ownerRoots, ownerAfter) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using howner
  refine demandNodeReplayChild_ofParts env (.expression (.push owner expr origin)) index
    (.place owner) before after roots hchild hreplay env before ownerAfter ownerRoots
    rfl rfl rfl hownerReplay ?_
  exact htailMono _ _ _ htail

theorem rpDemandNode_expression_push_value_child
    (env : PEnv) (owner : Place) (expr : Expr) (origin : Option OriginId)
    (index : Nat) (before after : RState) (roots : List RootRef)
    (hchild : (DemandNode.expression (.push owner expr origin)).child? index =
      some (.expression expr))
    (hreplay : rpDemandNode env (.expression (.push owner expr origin)) before =
      .ok (roots, after)) :
    DemandNodeReplayChild env (.expression (.push owner expr origin)) index
      (.expression expr) before after := by
  have hparent : rpDemandNode env (.expression (.push owner expr origin)) before =
      .ok (roots, after) := hreplay
  simp only [rpDemandNode, rpExpr] at hparent
  rcases (st_bind_ok _ _ _ _).1 hparent with ⟨ownerRoots, ownerAfter, howner, htail⟩
  rcases (st_bind_ok _ _ _ _).1 htail with ⟨valueRoots, valueAfter, hvalue, htail⟩
  have htailMono : PMono (do
      addGrows ownerRoots
      if env.mod.profile == .shrink then do
        addWrites ownerRoots
        if (← liftV (env.limitedOwner owner)) then noteAborts
      pure ownerRoots) :=
    PMono.bind (PMono.addGrows ownerRoots) (fun _ =>
      PMono.profileWriteAbortValue env owner ownerRoots)
  have hvalueReplay : rpDemandNode env (.expression expr) ownerAfter =
      .ok (valueRoots, valueAfter) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hvalue
  refine demandNodeReplayChild_ofParts env (.expression (.push owner expr origin)) index
    (.expression expr) before after roots hchild hreplay env ownerAfter valueAfter valueRoots
    rfl rfl rfl hvalueReplay ?_
  exact htailMono _ _ _ htail

theorem rpDemandNode_block_statement_child
    (env : PEnv) (scope : Nat) (stmts : List Stmt) (value : Option Expr)
    (index : Nat) (stmt : Stmt) (before : RState)
    (output : Prod (List RootRef) (Nat × Nat)) (after : RState)
    (hchild : (DemandNode.block (.mk scope stmts value)).child? index =
      some (.statement stmt))
    (hreplay : rpDemandNode env (.block (.mk scope stmts value)) before =
      .ok (output, after)) :
    DemandNodeReplayChild env (.block (.mk scope stmts value)) index (.statement stmt)
      before after := by
  obtain ⟨rho, range⟩ := output
  have hindex := block_child_statement_index scope stmts value index stmt hchild
  have hblock : rpBlockValue env [] (.mk scope stmts value) before =
      .ok ((rho, range), after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  obtain ⟨_, stateAfterStmts, hstmts, hvalue, _, _⟩ :=
    rpBlockValue_ok env [] scope stmts value before rho range after hblock
  have hstmts' : rpStmts { env with scopes := scope :: env.scopes } stmts before =
      .ok ((), stateAfterStmts) := by simpa using hstmts
  obtain ⟨childBefore, childAfter, hstmt, hmonoStmts⟩ :=
    rpStmts_member_replay { env with scopes := scope :: env.scopes }
      stmts index stmt before stateAfterStmts hindex hstmts'
  have hmonoValue : RLe stateAfterStmts after := by
    cases value with
    | none =>
      obtain ⟨_, rfl⟩ := hvalue
      exact RLe.refl _
    | some expr => exact rpExpr_mono (by simpa using hvalue)
  refine ⟨hchild, (rho, range), hreplay, { env with scopes := scope :: env.scopes },
    childBefore, childAfter, (), ?_⟩
  exact ⟨rfl, rfl, rfl, hstmt, hmonoStmts.trans hmonoValue⟩

private theorem block_child_value_index (scope : Nat) (stmts : List Stmt)
    (value : Option Expr) (index : Nat) (expr : Expr)
    (hchild : (DemandNode.block (.mk scope stmts value)).child? index =
      some (.expression expr)) :
    index = stmts.length ∧ value = some expr := by
  simp only [DemandNode.child?, DemandNode.children] at hchild
  simp only [List.getElem?_append] at hchild
  split at hchild
  · simp only [List.getElem?_map] at hchild
    cases hindex : stmts[index]? with
    | none => simp [hindex] at hchild
    | some stmt => simp [hindex] at hchild
  · rename_i hnot
    simp only [List.length_map] at hnot
    cases hoffset : index - stmts.length with
    | zero =>
      cases hvalue : value with
      | none => simp [hoffset, hvalue] at hchild
      | some found =>
        simp [hoffset, hvalue] at hchild
        exact ⟨by omega, congrArg some hchild⟩
    | succ offset => simp [hoffset] at hchild

theorem rpDemandNode_block_value_child
    (env : PEnv) (scope : Nat) (stmts : List Stmt) (value : Option Expr)
    (index : Nat) (expr : Expr) (before : RState)
    (output : Prod (List RootRef) (Nat × Nat)) (after : RState)
    (hchild : (DemandNode.block (.mk scope stmts value)).child? index =
      some (.expression expr))
    (hreplay : rpDemandNode env (.block (.mk scope stmts value)) before =
      .ok (output, after)) :
    DemandNodeReplayChild env (.block (.mk scope stmts value)) index (.expression expr)
      before after := by
  obtain ⟨rho, range⟩ := output
  obtain ⟨hindex, hvalue⟩ := block_child_value_index scope stmts value index expr hchild
  subst index
  subst value
  have hblock : rpBlockValue env [] (.mk scope stmts (some expr)) before =
      .ok ((rho, range), after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  obtain ⟨_, stateAfterStmts, _, hvalue, _, _⟩ :=
    rpBlockValue_ok env [] scope stmts (some expr) before rho range after hblock
  refine ⟨hchild, (rho, range), hreplay, { env with scopes := scope :: env.scopes },
    stateAfterStmts, after, rho, ?_⟩
  exact ⟨rfl, rfl, rfl, by simpa [rpDemandNode, DemandNode.replayOutput] using hvalue,
    RLe.refl _⟩

theorem rpDemandNode_statement_expr_child
    (env : PEnv) (expr : Expr) (origin : OriginId) (index : Nat)
    (before after : RState)
    (hchild : (DemandNode.statement (.expr expr origin)).child? index =
      some (.expression expr))
    (hreplay : rpDemandNode env (.statement (.expr expr origin)) before =
      .ok ((), after)) :
    DemandNodeReplayChild env (.statement (.expr expr origin)) index (.expression expr)
      before after := by
  have hstmt : rpStmt env (.expr expr origin) before = .ok ((), after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpStmt] at hstmt
  rcases (st_bind_ok _ _ _ _).1 hstmt with ⟨roots, childAfter, hExpr, hpure⟩
  have hstate : childAfter = after := by
    have hpair : ((), childAfter) = ((), after) :=
      ((st_pure_ok () childAfter ((), after)).1 hpure).symm
    exact congrArg Prod.snd hpair
  refine ⟨hchild, (), hreplay, env, before, childAfter, roots, ?_⟩
  exact ⟨rfl, rfl, rfl, by simpa [rpDemandNode, DemandNode.replayOutput] using hExpr,
    by rw [hstate]; exact RLe.refl _⟩

theorem rpDemandNode_block_child
    (env : PEnv) (block : Block) (index : Nat) (child : DemandNode)
    (before after : RState)
    (output : DemandNode.replayOutput (.block block))
    (hchild : (DemandNode.block block).child? index = some child)
    (hreplay : rpDemandNode env (.block block) before = .ok (output, after)) :
    DemandNodeReplayChild env (.block block) index child before after := by
  cases block with
  | mk scope statements value =>
    cases child with
    | statement stmt =>
      exact rpDemandNode_block_statement_child env scope statements value index stmt before
        output after hchild hreplay
    | expression expr =>
      exact rpDemandNode_block_value_child env scope statements value index expr before
        output after hchild hreplay
    | place _ | view _ | bound _ | block _ =>
      have hmem := demandNodeChild_mem_children hchild
      cases value <;> simp [DemandNode.children] at hmem

theorem rpDemandNode_place_deref_child
    (env : PEnv) (expr : Expr) (index : Nat) (before after : RState)
    (roots : List RootRef)
    (hchild : (DemandNode.place (.deref expr)).child? index =
      some (.expression expr))
    (hreplay : rpDemandNode env (.place (.deref expr)) before = .ok (roots, after)) :
    DemandNodeReplayChild env (.place (.deref expr)) index (.expression expr)
      before after := by
  refine ⟨hchild, roots, hreplay, env, before, after, roots, ?_⟩
  exact ⟨rfl, rfl, rfl, by simpa [rpDemandNode, DemandNode.replayOutput, rpPlace] using hreplay,
    RLe.refl _⟩

theorem rpDemandNode_view_value_child
    (env : PEnv) (expr : Expr) (index : Nat) (before after : RState)
    (roots : List RootRef)
    (hchild : (DemandNode.view (.val expr)).child? index =
      some (.expression expr))
    (hreplay : rpDemandNode env (.view (.val expr)) before = .ok (roots, after)) :
    DemandNodeReplayChild env (.view (.val expr)) index (.expression expr)
      before after := by
  refine ⟨hchild, roots, hreplay, env, before, after, roots, ?_⟩
  exact ⟨rfl, rfl, rfl, by simpa [rpDemandNode, DemandNode.replayOutput, rpView] using hreplay,
    RLe.refl _⟩

theorem rpDemandNode_place_field_child
    (env : PEnv) (owner : Place) (field : Nat) (index : Nat) (before after : RState)
    (roots : List RootRef)
    (hchild : (DemandNode.place (.field owner field)).child? index = some (.place owner))
    (hreplay : rpDemandNode env (.place (.field owner field)) before = .ok (roots, after)) :
    DemandNodeReplayChild env (.place (.field owner field)) index (.place owner) before after := by
  have hplace : rpPlace env (.field owner field) before = .ok (roots, after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpPlace] at hplace
  have hchild' : rpDemandNode env (.place owner) before = .ok (roots, after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hplace
  exact demandNodeReplayChild_ofParts env (.place (.field owner field)) index (.place owner)
    before after roots hchild hreplay env before after roots rfl rfl rfl hchild' (RLe.refl _)

theorem rpDemandNode_place_elem_view_child
    (env : PEnv) (view : View) (indexExpr : Expr) (origin : OriginId)
    (index : Nat) (before after : RState) (roots : List RootRef)
    (hchild : (DemandNode.place (.elem view indexExpr origin)).child? index = some (.view view))
    (hreplay : rpDemandNode env (.place (.elem view indexExpr origin)) before =
      .ok (roots, after)) :
    DemandNodeReplayChild env (.place (.elem view indexExpr origin)) index (.view view)
      before after := by
  have hplace : rpPlace env (.elem view indexExpr origin) before = .ok (roots, after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpPlace] at hplace
  rcases (st_bind_ok _ _ _ _).1 hplace with ⟨viewRoots, afterView, hview, htail⟩
  have htailMono : PMono (do
      let _ ← rpExpr env indexExpr
      noteAborts
      pure viewRoots) :=
    PMono.bind (by
      intro st result st' h
      exact rpExpr_mono h) (fun _ =>
        PMono.bind PMono.noteAborts (fun _ => PMono.pure viewRoots))
  have hviewReplay : rpDemandNode env (.view view) before = .ok (viewRoots, afterView) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hview
  refine demandNodeReplayChild_ofParts env (.place (.elem view indexExpr origin)) index
    (.view view) before after roots hchild hreplay env before afterView viewRoots rfl rfl rfl
    hviewReplay ?_
  exact htailMono _ _ _ htail

theorem rpDemandNode_place_elem_index_child
    (env : PEnv) (view : View) (indexExpr : Expr) (origin : OriginId)
    (index : Nat) (before after : RState) (roots : List RootRef)
    (hchild : (DemandNode.place (.elem view indexExpr origin)).child? index =
      some (.expression indexExpr))
    (hreplay : rpDemandNode env (.place (.elem view indexExpr origin)) before =
      .ok (roots, after)) :
    DemandNodeReplayChild env (.place (.elem view indexExpr origin)) index
      (.expression indexExpr) before after := by
  have hplace : rpPlace env (.elem view indexExpr origin) before = .ok (roots, after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpPlace] at hplace
  rcases (st_bind_ok _ _ _ _).1 hplace with ⟨viewRoots, afterView, hview, htail⟩
  rcases (st_bind_ok _ _ _ _).1 htail with ⟨indexRoots, afterIndex, hindex, htail⟩
  have htailMono : PMono (do noteAborts; pure viewRoots) :=
    PMono.bind PMono.noteAborts (fun _ => PMono.pure viewRoots)
  have hindexReplay : rpDemandNode env (.expression indexExpr) afterView =
      .ok (indexRoots, afterIndex) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hindex
  refine demandNodeReplayChild_ofParts env (.place (.elem view indexExpr origin)) index
    (.expression indexExpr) before after roots hchild hreplay env afterView afterIndex indexRoots
    rfl rfl rfl hindexReplay ?_
  have htailMonoResult := htailMono _ _ _ htail
  exact htailMonoResult

theorem rpDemandNode_place_child
    (env : PEnv) (place : Place) (index : Nat) (child : DemandNode)
    (before after : RState) (roots : List RootRef)
    (hchild : (DemandNode.place place).child? index = some child)
    (hreplay : rpDemandNode env (.place place) before = .ok (roots, after)) :
    DemandNodeReplayChild env (.place place) index child before after := by
  cases index with
  | zero =>
    cases place with
    | var x => cases child <;> simp [DemandNode.child?, DemandNode.children] at hchild
    | global g => cases child <;> simp [DemandNode.child?, DemandNode.children] at hchild
    | deref expr =>
      cases child with
      | expression childExpr =>
        have hchildExpr : expr = childExpr := by
          simpa [DemandNode.child?, DemandNode.children] using hchild
        subst childExpr
        exact rpDemandNode_place_deref_child env expr 0 before after roots hchild hreplay
      | place _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | view _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | bound _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | statement _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | block _ => simp [DemandNode.child?, DemandNode.children] at hchild
    | field owner field =>
      cases child with
      | place childPlace =>
        have hchildPlace : owner = childPlace := by
          simpa [DemandNode.child?, DemandNode.children] using hchild
        subst childPlace
        exact rpDemandNode_place_field_child env owner field 0 before after roots hchild hreplay
      | expression _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | view _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | bound _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | statement _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | block _ => simp [DemandNode.child?, DemandNode.children] at hchild
    | elem view indexExpr origin =>
      cases child with
      | view childView =>
        have hchildView : view = childView := by
          simpa [DemandNode.child?, DemandNode.children] using hchild
        subst childView
        exact rpDemandNode_place_elem_view_child env view indexExpr origin 0 before after
          roots hchild hreplay
      | expression _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | place _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | bound _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | statement _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | block _ => simp [DemandNode.child?, DemandNode.children] at hchild
  | succ index =>
    cases index with
    | zero =>
      cases place with
      | elem view indexExpr origin =>
        cases child with
        | expression childExpr =>
          have hchildExpr : indexExpr = childExpr := by
            simpa [DemandNode.child?, DemandNode.children] using hchild
          subst childExpr
          exact rpDemandNode_place_elem_index_child env view indexExpr origin 1 before after
            roots hchild hreplay
        | place _ => simp [DemandNode.child?, DemandNode.children] at hchild
        | view _ => simp [DemandNode.child?, DemandNode.children] at hchild
        | bound _ => simp [DemandNode.child?, DemandNode.children] at hchild
        | statement _ => simp [DemandNode.child?, DemandNode.children] at hchild
        | block _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | var x => cases child <;> simp [DemandNode.child?, DemandNode.children] at hchild
      | global g => cases child <;> simp [DemandNode.child?, DemandNode.children] at hchild
      | deref expr => cases child <;> simp [DemandNode.child?, DemandNode.children] at hchild
      | field owner field => cases child <;> simp [DemandNode.child?, DemandNode.children] at hchild
    | succ index =>
      cases place <;> cases child <;> simp [DemandNode.child?, DemandNode.children] at hchild

theorem rpDemandNode_view_of_child
    (env : PEnv) (place : Place) (index : Nat) (before after : RState)
    (roots : List RootRef)
    (hchild : (DemandNode.view (.of place)).child? index = some (.place place))
    (hreplay : rpDemandNode env (.view (.of place)) before = .ok (roots, after)) :
    DemandNodeReplayChild env (.view (.of place)) index (.place place) before after := by
  have hview : rpView env (.of place) before = .ok (roots, after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpView] at hview
  rcases (st_bind_ok _ _ _ _).1 hview with ⟨placeRoots, afterPlace, hplace, htail⟩
  have htailMono : PMono (do addReads placeRoots; pure placeRoots) :=
    PMono.bind (PMono.addReads placeRoots) (fun _ => PMono.pure placeRoots)
  have hplaceReplay : rpDemandNode env (.place place) before = .ok (placeRoots, afterPlace) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hplace
  refine demandNodeReplayChild_ofParts env (.view (.of place)) index (.place place)
    before after roots hchild hreplay env before afterPlace placeRoots rfl rfl rfl
    hplaceReplay ?_
  exact htailMono _ _ _ htail

theorem rpDemandNode_view_child
    (env : PEnv) (view : View) (index : Nat) (child : DemandNode)
    (before after : RState) (roots : List RootRef)
    (hchild : (DemandNode.view view).child? index = some child)
    (hreplay : rpDemandNode env (.view view) before = .ok (roots, after)) :
    DemandNodeReplayChild env (.view view) index child before after := by
  cases index with
  | zero =>
    cases view with
    | of place =>
      cases child with
      | place childPlace =>
        have heq : place = childPlace := by
          simpa [DemandNode.child?, DemandNode.children] using hchild
        subst childPlace
        exact rpDemandNode_view_of_child env place 0 before after roots hchild hreplay
      | expression _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | view _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | bound _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | statement _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | block _ => simp [DemandNode.child?, DemandNode.children] at hchild
    | val expr =>
      cases child with
      | expression childExpr =>
        have heq : expr = childExpr := by
          simpa [DemandNode.child?, DemandNode.children] using hchild
        subst childExpr
        exact rpDemandNode_view_value_child env expr 0 before after roots hchild hreplay
      | place _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | view _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | bound _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | statement _ => simp [DemandNode.child?, DemandNode.children] at hchild
      | block _ => simp [DemandNode.child?, DemandNode.children] at hchild
  | succ index => cases view <;> cases child <;> simp [DemandNode.child?, DemandNode.children] at hchild

theorem rpDemandNode_bound_expression_child
    (env : PEnv) (bound : Bound) (index : Nat) (child : DemandNode)
    (before after : RState)
    (hchild : (DemandNode.bound bound).child? index = some child)
    (hreplay : rpDemandNode env (.bound bound) before = .ok ((), after)) :
    DemandNodeReplayChild env (.bound bound) index child before after := by
  have hbound : rpBound env bound before = .ok ((), after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  cases bound with
  | omitted => simp [DemandNode.child?, DemandNode.children] at hchild
  | expr expr =>
    have hindex : index = 0 := by
      cases index with
      | zero => rfl
      | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
    subst index
    have hchild' : child = .expression expr := by
      simpa [DemandNode.child?, DemandNode.children] using hchild.symm
    subst child
    simp only [rpBound] at hbound
    rcases (st_bind_ok _ _ _ _).1 hbound with ⟨roots, childAfter, hExpr, hpure⟩
    have hstate : childAfter = after := by
      have hpair : ((), childAfter) = ((), after) :=
        ((st_pure_ok () childAfter ((), after)).1 hpure).symm
      exact congrArg Prod.snd hpair
    refine ⟨hchild, (), hreplay, env, before, childAfter, roots, ?_⟩
    exact ⟨rfl, rfl, rfl,
      by simpa [rpDemandNode, DemandNode.replayOutput] using hExpr,
      by rw [hstate]; exact RLe.refl _⟩
  | fromEnd expr =>
    have hindex : index = 0 := by
      cases index with
      | zero => rfl
      | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
    subst index
    have hchild' : child = .expression expr := by
      simpa [DemandNode.child?, DemandNode.children] using hchild.symm
    subst child
    simp only [rpBound] at hbound
    rcases (st_bind_ok _ _ _ _).1 hbound with ⟨roots, childAfter, hExpr, hpure⟩
    have hstate : childAfter = after := by
      have hpair : ((), childAfter) = ((), after) :=
        ((st_pure_ok () childAfter ((), after)).1 hpure).symm
      exact congrArg Prod.snd hpair
    refine ⟨hchild, (), hreplay, env, before, childAfter, roots, ?_⟩
    exact ⟨rfl, rfl, rfl,
      by simpa [rpDemandNode, DemandNode.replayOutput] using hExpr,
      by rw [hstate]; exact RLe.refl _⟩

theorem rpDemandNode_expression_block_child
    (env : PEnv) (block : Block) (index : Nat) (before after : RState)
    (roots : List RootRef)
    (hchild : (DemandNode.expression (.blockE block)).child? index =
      some (.block block))
    (hreplay : rpDemandNode env (.expression (.blockE block)) before =
      .ok (roots, after)) :
    DemandNodeReplayChild env (.expression (.blockE block)) index (.block block)
      before after := by
  have hexpr : rpExpr env (.blockE block) before = .ok (roots, after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpExpr] at hexpr
  rcases (st_bind_ok _ _ _ _).1 hexpr with ⟨blockOutput, blockAfter, hblock, hpure⟩
  have hpair : (roots, after) = (blockOutput.1, blockAfter) :=
    (st_pure_ok blockOutput.1 blockAfter (roots, after)).1 hpure
  have hstate : blockAfter = after := (congrArg Prod.snd hpair).symm
  refine ⟨hchild, roots, hreplay, env, before, blockAfter, blockOutput, ?_⟩
  exact ⟨rfl, rfl, rfl,
    by simpa [rpDemandNode, DemandNode.replayOutput] using hblock,
    by rw [hstate]; exact RLe.refl _⟩

theorem rpDemandNode_expression_bin_left_child
    (env : PEnv) (op : BinOp) (left right : Expr) (origin : OriginId)
    (before after : RState)
    (hreplay : rpDemandNode env (.expression (.bin op left right origin)) before =
      .ok ([], after)) :
    DemandNodeReplayChild env (.expression (.bin op left right origin)) 0
      (.expression left) before after := by
  have hexpr : rpExpr env (.bin op left right origin) before = .ok ([], after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpExpr] at hexpr
  rcases (st_bind_ok _ _ _ _).1 hexpr with ⟨leftRoots, leftAfter, hleft, htail⟩
  have htailMono : PMono (do
      let _ ← rpExpr env right
      if op.mayAbort then noteAborts
      pure ([] : List RootRef)) :=
    PMono.bind (rp_mono_all.2.2.1 env right) (fun _ =>
      PMono.iteBool op.mayAbort
        (PMono.bind PMono.noteAborts (fun _ => PMono.pure []))
        (PMono.pure []))
  have hchild : (DemandNode.expression (.bin op left right origin)).child? 0 =
      some (.expression left) := by simp [DemandNode.child?, DemandNode.children]
  refine ⟨hchild, [], hreplay, env, before, leftAfter, leftRoots, ?_⟩
  exact ⟨rfl, rfl, rfl, by simpa [rpDemandNode, DemandNode.replayOutput] using hleft,
    htailMono _ _ _ htail⟩

theorem rpDemandNode_expression_bin_right_child
    (env : PEnv) (op : BinOp) (left right : Expr) (origin : OriginId)
    (before after : RState)
    (hreplay : rpDemandNode env (.expression (.bin op left right origin)) before =
      .ok ([], after)) :
    DemandNodeReplayChild env (.expression (.bin op left right origin)) 1
      (.expression right) before after := by
  have hexpr : rpExpr env (.bin op left right origin) before = .ok ([], after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpExpr] at hexpr
  rcases (st_bind_ok _ _ _ _).1 hexpr with ⟨_, leftAfter, _, htail⟩
  rcases (st_bind_ok _ _ _ _).1 htail with ⟨rightRoots, rightAfter, hright, htail⟩
  have htailMono : PMono (do
      if op.mayAbort then noteAborts
      pure ([] : List RootRef)) :=
    PMono.iteBool op.mayAbort
      (PMono.bind PMono.noteAborts (fun _ => PMono.pure []))
      (PMono.pure [])
  have hchild : (DemandNode.expression (.bin op left right origin)).child? 1 =
      some (.expression right) := by simp [DemandNode.child?, DemandNode.children]
  refine ⟨hchild, [], hreplay, env, leftAfter, rightAfter, rightRoots, ?_⟩
  exact ⟨rfl, rfl, rfl, by simpa [rpDemandNode, DemandNode.replayOutput] using hright,
    htailMono _ _ _ htail⟩

private theorem rpDemandNode_expression_pair_child_ofStage
    (env : PEnv) (parentExpr left right childExpr : Expr) (index : Nat)
    (before after : RState)
    (hindex : index = 0 ∨ index = 1)
    (hchildExpr : childExpr = (if index = 0 then left else right))
    (hchild : (DemandNode.expression parentExpr).child? index =
      some (.expression childExpr))
    (hreplay : rpDemandNode env (.expression parentExpr) before = .ok ([], after))
    (hstage : rpExpr env parentExpr = do
      let _ ← rpExpr env left
      let _ ← rpExpr env right
      pure []) :
    DemandNodeReplayChild env (.expression parentExpr) index
      (.expression childExpr) before after := by
  have hstage' : (do
      let _ ← rpExpr env left
      let _ ← rpExpr env right
      pure ([] : List RootRef)) before = .ok ([], after) := by
    simpa [rpDemandNode, DemandNode.replayOutput, hstage] using hreplay
  rcases hindex with hzero | hone
  · subst index
    subst childExpr
    have hleftIndex : (DemandNode.expression parentExpr).child? 0 =
        some (.expression left) := hchild
    rcases (st_bind_ok _ _ _ _).1 hstage' with ⟨leftRoots, leftAfter, hleft, htail⟩
    have htailMono : PMono (do let _ ← rpExpr env right; pure ([] : List RootRef)) :=
      PMono.bind (fun _ _ _ h => rpExpr_mono h) (fun _ => PMono.pure [])
    exact ⟨hleftIndex, [], hreplay, env, before, leftAfter, leftRoots,
      rfl, rfl, rfl,
      by simpa [rpDemandNode, DemandNode.replayOutput] using hleft,
      htailMono _ _ _ htail⟩
  · subst index
    subst childExpr
    have hrightIndex : (DemandNode.expression parentExpr).child? 1 =
        some (.expression right) := hchild
    rcases (st_bind_ok _ _ _ _).1 hstage' with ⟨_, leftAfter, _, htail⟩
    rcases (st_bind_ok _ _ _ _).1 htail with ⟨rightRoots, rightAfter, hright, htail⟩
    have htailMono : PMono (pure ([] : List RootRef)) := PMono.pure []
    exact ⟨hrightIndex, [], hreplay, env, leftAfter, rightAfter, rightRoots,
      rfl, rfl, rfl,
      by simpa [rpDemandNode, DemandNode.replayOutput] using hright,
      htailMono _ _ _ htail⟩

theorem rpDemandNode_expression_cmp_child
    (env : PEnv) (op : CmpOp) (left right : Expr) (index : Nat)
    (before after : RState) (child : DemandNode)
    (hchild : (DemandNode.expression (.cmp op left right)).child? index = some child)
    (hreplay : rpDemandNode env (.expression (.cmp op left right)) before = .ok ([], after)) :
    DemandNodeReplayChild env (.expression (.cmp op left right)) index child before after := by
  cases index with
  | zero =>
    have hchild' : child = .expression left := by
      simpa [DemandNode.child?, DemandNode.children] using hchild.symm
    subst child
    apply rpDemandNode_expression_pair_child_ofStage env (.cmp op left right) left right left 0
      before after (Or.inl rfl) (by simp)
    · simp [DemandNode.child?, DemandNode.children]
    · exact hreplay
    · funext state; simp [rpExpr]
  | succ index =>
    cases index with
    | zero =>
      have hchild' : child = .expression right := by
        simpa [DemandNode.child?, DemandNode.children] using hchild.symm
      subst child
      apply rpDemandNode_expression_pair_child_ofStage env (.cmp op left right) left right right 1
        before after (Or.inr rfl) (by simp)
      · simp [DemandNode.child?, DemandNode.children]
      · exact hreplay
      · funext state; simp [rpExpr]
    | succ index => simp [DemandNode.child?, DemandNode.children] at hchild

theorem rpDemandNode_expression_and_child
    (env : PEnv) (left right : Expr) (index : Nat)
    (before after : RState) (child : DemandNode)
    (hchild : (DemandNode.expression (.and left right)).child? index = some child)
    (hreplay : rpDemandNode env (.expression (.and left right)) before = .ok ([], after)) :
    DemandNodeReplayChild env (.expression (.and left right)) index child before after := by
  cases index with
  | zero =>
    have hchild' : child = .expression left := by
      simpa [DemandNode.child?, DemandNode.children] using hchild.symm
    subst child
    apply rpDemandNode_expression_pair_child_ofStage env (.and left right) left right left 0
      before after (Or.inl rfl) (by simp)
    · simp [DemandNode.child?, DemandNode.children]
    · exact hreplay
    · funext state; simp [rpExpr]
  | succ index =>
    cases index with
    | zero =>
      have hchild' : child = .expression right := by
        simpa [DemandNode.child?, DemandNode.children] using hchild.symm
      subst child
      apply rpDemandNode_expression_pair_child_ofStage env (.and left right) left right right 1
        before after (Or.inr rfl) (by simp)
      · simp [DemandNode.child?, DemandNode.children]
      · exact hreplay
      · funext state; simp [rpExpr]
    | succ index => simp [DemandNode.child?, DemandNode.children] at hchild

theorem rpDemandNode_expression_or_child
    (env : PEnv) (left right : Expr) (index : Nat)
    (before after : RState) (child : DemandNode)
    (hchild : (DemandNode.expression (.or left right)).child? index = some child)
    (hreplay : rpDemandNode env (.expression (.or left right)) before = .ok ([], after)) :
    DemandNodeReplayChild env (.expression (.or left right)) index child before after := by
  cases index with
  | zero =>
    have hchild' : child = .expression left := by
      simpa [DemandNode.child?, DemandNode.children] using hchild.symm
    subst child
    apply rpDemandNode_expression_pair_child_ofStage env (.or left right) left right left 0
      before after (Or.inl rfl) (by simp)
    · simp [DemandNode.child?, DemandNode.children]
    · exact hreplay
    · funext state; simp [rpExpr]
  | succ index =>
    cases index with
    | zero =>
      have hchild' : child = .expression right := by
        simpa [DemandNode.child?, DemandNode.children] using hchild.symm
      subst child
      apply rpDemandNode_expression_pair_child_ofStage env (.or left right) left right right 1
        before after (Or.inr rfl) (by simp)
      · simp [DemandNode.child?, DemandNode.children]
      · exact hreplay
      · funext state; simp [rpExpr]
    | succ index => simp [DemandNode.child?, DemandNode.children] at hchild

private theorem rpExpr_pair_result_empty (env : PEnv) (left right : Expr)
    (tail : P Unit) (before after : RState) (roots : List RootRef)
    (hreplay : (do
      let _ ← rpExpr env left
      let _ ← rpExpr env right
      let _ ← tail
      pure ([] : List RootRef)) before = .ok (roots, after)) :
    roots = [] := by
  rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨_, _, _, hrest⟩
  rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, _, _, hrest⟩
  rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, afterTail, _, hpure⟩
  have heq : (roots, after) = ([], afterTail) :=
    (st_pure_ok [] afterTail (roots, after)).1 hpure
  exact congrArg Prod.fst heq

private theorem rpExpr_child_result_empty (env : PEnv) (expr : Expr)
    (tail : P Unit) (before after : RState) (roots : List RootRef)
    (hreplay : (do
      let _ ← rpExpr env expr
      let _ ← tail
      pure ([] : List RootRef)) before = .ok (roots, after)) :
    roots = [] := by
  rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨_, _, _, hrest⟩
  rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, afterTail, _, hpure⟩
  have heq : (roots, after) = ([], afterTail) :=
    (st_pure_ok [] afterTail (roots, after)).1 hpure
  exact congrArg Prod.fst heq

private theorem rpComputation_result_empty {α : Type} (first : P α) (tail : P Unit)
    (before after : RState) (roots : List RootRef)
    (hreplay : (do let _ ← first; let _ ← tail; pure ([] : List RootRef)) before =
      .ok (roots, after)) : roots = [] := by
  rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨_, _, _, hrest⟩
  rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, afterTail, _, hpure⟩
  have heq : (roots, after) = ([], afterTail) :=
    (st_pure_ok [] afterTail (roots, after)).1 hpure
  exact congrArg Prod.fst heq

private theorem rpExprs_result_empty (env : PEnv) (exprs : List Expr)
    (before after : RState) (roots : List RootRef)
    (hreplay : (do rpExprs env exprs; pure ([] : List RootRef)) before =
      .ok (roots, after)) : roots = [] := by
  rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨_, afterExprs, _, hpure⟩
  have heq : (roots, after) = ([], afterExprs) :=
    (st_pure_ok [] afterExprs (roots, after)).1 hpure
  exact congrArg Prod.fst heq

private theorem arr_child_index (arrayType : Ty) (exprs : List Expr)
    (index : Nat) (expr : Expr)
    (hchild : (DemandNode.expression (.arrLit arrayType exprs)).child? index =
      some (.expression expr)) :
    exprs[index]? = some expr := by
  simp only [DemandNode.child?, DemandNode.children, List.getElem?_map] at hchild
  cases hindex : exprs[index]? with
  | none => simp [hindex] at hchild
  | some found =>
    simp [hindex] at hchild
    subst found
    rfl

theorem rpDemandNode_expression_arrItem_child
    (env : PEnv) (arrayType : Ty) (exprs : List Expr) (index : Nat)
    (expr : Expr) (before after : RState)
    (hchild : (DemandNode.expression (.arrLit arrayType exprs)).child? index =
      some (.expression expr))
    (hreplay : rpDemandNode env (.expression (.arrLit arrayType exprs)) before =
      .ok ([], after)) :
    DemandNodeReplayChild env (.expression (.arrLit arrayType exprs)) index
      (.expression expr) before after := by
  have hexpr : rpExpr env (.arrLit arrayType exprs) before = .ok ([], after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpExpr] at hexpr
  rcases (st_bind_ok _ _ _ _).1 hexpr with ⟨_, exprsAfter, hexprs, hpure⟩
  have hpair : ([], after) = ([], exprsAfter) :=
    (st_pure_ok [] exprsAfter ([], after)).1 hpure
  have hstate : exprsAfter = after := (congrArg Prod.snd hpair).symm
  obtain ⟨childBefore, childAfter, childRoots, hitem, hmono⟩ :=
      rpExprs_member_replay env exprs index expr before exprsAfter
        (arr_child_index arrayType exprs index expr hchild) hexprs
  refine ⟨hchild, [], hreplay, env, childBefore, childAfter, childRoots, ?_⟩
  exact ⟨rfl, rfl, rfl,
    by simpa [rpDemandNode, DemandNode.replayOutput] using hitem,
    by rw [← hstate]; exact hmono⟩

private theorem struct_child_index (structType : Ty) (exprs : List Expr)
    (index : Nat) (expr : Expr)
    (hchild : (DemandNode.expression (.structLit structType exprs)).child? index =
      some (.expression expr)) : exprs[index]? = some expr := by
  simp only [DemandNode.child?, DemandNode.children, List.getElem?_map] at hchild
  cases hindex : exprs[index]? with
  | none => simp [hindex] at hchild
  | some found =>
    simp [hindex] at hchild
    subst found
    rfl

theorem rpDemandNode_expression_structItem_child
    (env : PEnv) (structType : Ty) (exprs : List Expr) (index : Nat)
    (expr : Expr) (before after : RState)
    (hchild : (DemandNode.expression (.structLit structType exprs)).child? index =
      some (.expression expr))
    (hreplay : rpDemandNode env (.expression (.structLit structType exprs)) before =
      .ok ([], after)) :
    DemandNodeReplayChild env (.expression (.structLit structType exprs)) index
      (.expression expr) before after := by
  have hexpr : rpExpr env (.structLit structType exprs) before = .ok ([], after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpExpr] at hexpr
  rcases (st_bind_ok _ _ _ _).1 hexpr with ⟨_, exprsAfter, hexprs, hpure⟩
  have hpair : ([], after) = ([], exprsAfter) :=
    (st_pure_ok [] exprsAfter ([], after)).1 hpure
  have hstate : exprsAfter = after := (congrArg Prod.snd hpair).symm
  obtain ⟨childBefore, childAfter, childRoots, hitem, hmono⟩ :=
    rpExprs_member_replay env exprs index expr before exprsAfter
      (struct_child_index structType exprs index expr hchild) hexprs
  refine ⟨hchild, [], hreplay, env, childBefore, childAfter, childRoots, ?_⟩
  exact ⟨rfl, rfl, rfl,
    by simpa [rpDemandNode, DemandNode.replayOutput] using hitem,
    by rw [← hstate]; exact hmono⟩

private theorem rpExpr_ifE_stages (env : PEnv) (condition : Expr)
    (thenBlock elseBlock : Block) (before after : RState)
    (roots : List RootRef)
    (hreplay : rpExpr env (.ifE condition thenBlock elseBlock) before =
      .ok (roots, after)) :
    ∃ conditionRoots afterCondition thenOutput afterThen elseOutput afterElse,
      rpExpr env condition before = .ok (conditionRoots, afterCondition) ∧
      rpBlockValue env [] thenBlock afterCondition = .ok (thenOutput, afterThen) ∧
      rpBlockValue env [] elseBlock afterThen = .ok (elseOutput, afterElse) ∧
      afterElse = after := by
  simp only [rpExpr] at hreplay
  rcases (st_bind_ok _ _ _ _).1 hreplay with
    ⟨conditionRoots, afterCondition, hcondition, hthen⟩
  rcases (st_bind_ok _ _ _ _).1 hthen with ⟨thenOutput, afterThen, hthen, helse⟩
  rcases (st_bind_ok _ _ _ _).1 helse with ⟨elseOutput, afterElse, helse, hpure⟩
  have hstate : afterElse = after := by
    have hpair : (roots, after) = (unionRoots thenOutput.1 elseOutput.1, afterElse) :=
      (st_pure_ok _ afterElse (roots, after)).1 hpure
    exact (congrArg Prod.snd hpair).symm
  exact ⟨conditionRoots, afterCondition, thenOutput, afterThen, elseOutput, afterElse,
    hcondition, hthen, helse, hstate⟩

theorem rpDemandNode_expression_ifE_condition_child
    (env : PEnv) (condition : Expr) (thenBlock elseBlock : Block)
    (before after : RState) (roots : List RootRef)
    (hreplay : rpDemandNode env
      (.expression (.ifE condition thenBlock elseBlock)) before = .ok (roots, after)) :
    DemandNodeReplayChild env (.expression (.ifE condition thenBlock elseBlock)) 0
      (.expression condition) before after := by
  have hexpr : rpExpr env (.ifE condition thenBlock elseBlock) before =
      .ok (roots, after) := by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  obtain ⟨conditionRoots, afterCondition, thenOutput, afterThen, elseOutput, afterElse,
    hcondition, hthen, helse, hstate⟩ :=
    rpExpr_ifE_stages env condition thenBlock elseBlock before after roots hexpr
  have hchild : (DemandNode.expression (.ifE condition thenBlock elseBlock)).child? 0 =
      some (.expression condition) := by
    simp [DemandNode.child?, DemandNode.children]
  refine ⟨hchild, roots, hreplay, env, before, afterCondition, conditionRoots, ?_⟩
  exact ⟨rfl, rfl, rfl, by simpa [rpDemandNode, DemandNode.replayOutput] using hcondition,
    by rw [← hstate]; exact (rpBlockValue_mono hthen).trans (rpBlockValue_mono helse)⟩

theorem rpDemandNode_expression_ifE_then_child
    (env : PEnv) (condition : Expr) (thenBlock elseBlock : Block)
    (before after : RState) (roots : List RootRef)
    (hreplay : rpDemandNode env
      (.expression (.ifE condition thenBlock elseBlock)) before = .ok (roots, after)) :
    DemandNodeReplayChild env (.expression (.ifE condition thenBlock elseBlock)) 1
      (.block thenBlock) before after := by
  have hexpr : rpExpr env (.ifE condition thenBlock elseBlock) before =
      .ok (roots, after) := by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  obtain ⟨_, afterCondition, thenOutput, afterThen, elseOutput, afterElse,
    _, hthen, helse, hstate⟩ :=
    rpExpr_ifE_stages env condition thenBlock elseBlock before after roots hexpr
  have hchild : (DemandNode.expression (.ifE condition thenBlock elseBlock)).child? 1 =
      some (.block thenBlock) := by simp [DemandNode.child?, DemandNode.children]
  refine ⟨hchild, roots, hreplay, env, afterCondition, afterThen, thenOutput, ?_⟩
  exact ⟨rfl, rfl, rfl,
    by simpa [rpDemandNode, DemandNode.replayOutput] using hthen,
    by rw [← hstate]; exact rpBlockValue_mono helse⟩

theorem rpDemandNode_expression_ifE_else_child
    (env : PEnv) (condition : Expr) (thenBlock elseBlock : Block)
    (before after : RState) (roots : List RootRef)
    (hreplay : rpDemandNode env
      (.expression (.ifE condition thenBlock elseBlock)) before = .ok (roots, after)) :
    DemandNodeReplayChild env (.expression (.ifE condition thenBlock elseBlock)) 2
      (.block elseBlock) before after := by
  have hexpr : rpExpr env (.ifE condition thenBlock elseBlock) before =
      .ok (roots, after) := by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  obtain ⟨_, afterCondition, thenOutput, afterThen, elseOutput, afterElse,
    _, _, helse, hstate⟩ :=
    rpExpr_ifE_stages env condition thenBlock elseBlock before after roots hexpr
  have hchild : (DemandNode.expression (.ifE condition thenBlock elseBlock)).child? 2 =
      some (.block elseBlock) := by simp [DemandNode.child?, DemandNode.children]
  refine ⟨hchild, roots, hreplay, env, afterThen, afterElse, elseOutput, ?_⟩
  exact ⟨rfl, rfl, rfl,
    by simpa [rpDemandNode, DemandNode.replayOutput] using helse,
    by rw [hstate]; exact RLe.refl _⟩

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

private theorem rpStmt_ifSThen_block_replay (env : PEnv) (condition : Expr)
    (thenBlock : Block) (elseBlock : Option Block) (origin : OriginId)
    (state state' : RState)
    (hreplay : rpStmt env (.ifS condition thenBlock elseBlock origin) state =
      .ok ((), state')) :
    ∃ before roots range after,
      rpBlockValue env [] thenBlock before = .ok ((roots, range), after) ∧
        RLe after state' := by
  cases elseBlock with
  | none =>
    simp only [rpStmt] at hreplay
    rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨_, afterCondition, _, hthen⟩
    rcases (st_bind_ok _ _ _ _).1 hthen with ⟨⟨roots, range⟩, afterThen, hthen, hpure⟩
    have hstate : afterThen = state' := by
      have hpair : ((), afterThen) = ((), state') :=
        ((st_pure_ok () afterThen ((), state')).1 hpure).symm
      exact congrArg Prod.snd hpair
    exact ⟨afterCondition, roots, range, afterThen, hthen, by simpa [hstate] using
      (RLe.refl afterThen)⟩
  | some otherBlock =>
    simp only [rpStmt] at hreplay
    rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨_, afterCondition, _, hthen⟩
    rcases (st_bind_ok _ _ _ _).1 hthen with ⟨⟨roots, range⟩, afterThen, hthen, helse⟩
    rcases (st_bind_ok _ _ _ _).1 helse with ⟨_, afterElse, helse, hpure⟩
    have hstate : afterElse = state' := by
      have hpair : ((), afterElse) = ((), state') :=
        ((st_pure_ok () afterElse ((), state')).1 hpure).symm
      exact congrArg Prod.snd hpair
    exact ⟨afterCondition, roots, range, afterThen, hthen, by
      rw [← hstate]
      exact rpBlockValue_mono helse⟩

theorem rpDemandNode_statement_ifThen_child
    (env : PEnv) (condition : Expr) (thenBlock : Block)
    (elseBlock : Option Block) (origin : OriginId) (index : Nat)
    (before after : RState)
    (hchild : (DemandNode.statement (.ifS condition thenBlock elseBlock origin)).child?
      index = some (.block thenBlock))
    (hreplay : rpDemandNode env
      (.statement (.ifS condition thenBlock elseBlock origin)) before = .ok ((), after)) :
    DemandNodeReplayChild env (.statement (.ifS condition thenBlock elseBlock origin)) index
      (.block thenBlock) before after := by
  have hstmt : rpStmt env (.ifS condition thenBlock elseBlock origin) before =
      .ok ((), after) := by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  obtain ⟨blockBefore, roots, range, blockAfter, hblock, hmono⟩ :=
    rpStmt_ifSThen_block_replay env condition thenBlock elseBlock origin before after hstmt
  refine ⟨hchild, (), hreplay, env, blockBefore, blockAfter, (roots, range), ?_⟩
  exact ⟨rfl, rfl, rfl,
    by simpa [rpDemandNode, DemandNode.replayOutput] using hblock, hmono⟩

theorem rpDemandNode_statement_ifElse_child
    (env : PEnv) (condition : Expr) (thenBlock elseBlock : Block)
    (origin : OriginId) (index : Nat) (before after : RState)
    (hchild : (DemandNode.statement
      (.ifS condition thenBlock (some elseBlock) origin)).child? index =
        some (.block elseBlock))
    (hreplay : rpDemandNode env
      (.statement (.ifS condition thenBlock (some elseBlock) origin)) before =
        .ok ((), after)) :
    DemandNodeReplayChild
      env (.statement (.ifS condition thenBlock (some elseBlock) origin)) index
      (.block elseBlock) before after := by
  have hstmt : rpStmt env (.ifS condition thenBlock (some elseBlock) origin) before =
      .ok ((), after) := by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpStmt] at hstmt
  rcases (st_bind_ok _ _ _ _).1 hstmt with ⟨_, afterCondition, _, hthen⟩
  rcases (st_bind_ok _ _ _ _).1 hthen with ⟨_, afterThen, _, helse⟩
  rcases (st_bind_ok _ _ _ _).1 helse with ⟨blockOutput, blockAfter, hblock, hpure⟩
  have hstate : blockAfter = after := by
    have hpair : ((), blockAfter) = ((), after) :=
      ((st_pure_ok () blockAfter ((), after)).1 hpure).symm
    exact congrArg Prod.snd hpair
  refine ⟨hchild, (), hreplay, env, afterThen, blockAfter, blockOutput, ?_⟩
  exact ⟨rfl, rfl, rfl,
    by simpa [rpDemandNode, DemandNode.replayOutput] using hblock,
    by rw [hstate]; exact RLe.refl _⟩

theorem rpDemandNode_statement_while_child
    (env : PEnv) (condition : Expr) (body : Block) (origin : OriginId)
    (index : Nat) (before after : RState)
    (hchild : (DemandNode.statement (.while condition body origin)).child? index =
      some (.block body))
    (hreplay : rpDemandNode env (.statement (.while condition body origin)) before =
      .ok ((), after)) :
    DemandNodeReplayChild env (.statement (.while condition body origin)) index
      (.block body) before after := by
  have hstmt : rpStmt env (.while condition body origin) before = .ok ((), after) := by
    simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpStmt] at hstmt
  rcases (st_bind_ok _ _ _ _).1 hstmt with ⟨_, bodyBefore, _, hbody⟩
  rcases (st_bind_ok _ _ _ _).1 hbody with ⟨bodyOutput, bodyAfter, hblock, hpure⟩
  have hstate : bodyAfter = after := by
    have hpair : ((), bodyAfter) = ((), after) :=
      ((st_pure_ok () bodyAfter ((), after)).1 hpure).symm
    exact congrArg Prod.snd hpair
  refine ⟨hchild, (), hreplay, env, bodyBefore, bodyAfter, bodyOutput, ?_⟩
  exact ⟨rfl, rfl, rfl,
    by simpa [rpDemandNode, DemandNode.replayOutput] using hblock,
    by rw [hstate]; exact RLe.refl _⟩

theorem rpDemandNode_statement_forRange_child
    (env : PEnv) (variableId : VarId) (lower upper : Expr) (body : Block)
    (origin : OriginId) (index : Nat) (before after : RState)
    (hchild : (DemandNode.statement
      (.forRange variableId lower upper body origin)).child? index = some (.block body))
    (hreplay : rpDemandNode env
      (.statement (.forRange variableId lower upper body origin)) before = .ok ((), after)) :
    DemandNodeReplayChild
      env (.statement (.forRange variableId lower upper body origin)) index
      (.block body) before after := by
  have hstmt : rpStmt env (.forRange variableId lower upper body origin) before =
      .ok ((), after) := by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpStmt] at hstmt
  rcases (st_bind_ok _ _ _ _).1 hstmt with ⟨initial, stateAfterGet, hget, hrest⟩
  have hgetState : (initial, stateAfterGet) = (before, before) :=
    (st_get_ok before _).1 hget
  cases hgetState
  rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, stateAfterCheck, hcheck, hrest⟩
  rcases (st_ite_ok _ _ _ _ _).1 hcheck with ⟨_, hpure⟩ | ⟨_, herror⟩
  · have hcheckPair : ((), stateAfterCheck) = ((), before) :=
      (st_pure_ok () before _).1 hpure
    have hcheckState : stateAfterCheck = before := congrArg Prod.snd hcheckPair
    subst stateAfterCheck
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, afterModify, _, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, afterLower, hlower, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, afterUpper, hupper, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨bodyOutput, bodyAfter, hbody, hcheckBody⟩
    have hstate : bodyAfter = after := by
      unfold liftV at hcheckBody
      cases hv : checkBlockValue before.nextVar bodyOutput.2.1 bodyOutput.1 with
      | error error => simp [hv] at hcheckBody
      | ok checked =>
        simp [hv] at hcheckBody
        cases hcheckBody
        rfl
    refine ⟨hchild, (), hreplay, env, afterUpper, bodyAfter, bodyOutput, ?_⟩
    exact ⟨rfl, rfl, rfl,
      by simpa [rpDemandNode, DemandNode.replayOutput] using hbody,
      by rw [hstate]; exact RLe.refl _⟩
  · unfold rejP at herror
    simp only [st_throw_ok] at herror

theorem rpDemandNode_statement_forEach_child
    (env : PEnv) (variableId : VarId) (indexVar : Option VarId)
    (source : View) (byRef : Bool) (body : Block) (origin : OriginId)
    (index : Nat) (before after : RState)
    (hchild : (DemandNode.statement
      (.forEach variableId indexVar source byRef body origin)).child? index =
        some (.block body))
    (hreplay : rpDemandNode env
      (.statement (.forEach variableId indexVar source byRef body origin)) before =
        .ok ((), after)) :
    DemandNodeReplayChild
      env (.statement (.forEach variableId indexVar source byRef body origin)) index
      (.block body) before after := by
  have hstmt : rpStmt env (.forEach variableId indexVar source byRef body origin) before =
      .ok ((), after) := by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
  simp only [rpStmt] at hstmt
  rcases (st_bind_ok _ _ _ _).1 hstmt with ⟨initial, stateAfterGet, hget, hrest⟩
  have hgetState : (initial, stateAfterGet) = (before, before) :=
    (st_get_ok before _).1 hget
  cases hgetState
  rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, stateAfterCheck, hcheck, hrest⟩
  rcases (st_ite_ok _ _ _ _ _).1 hcheck with ⟨_, hpure⟩ | ⟨_, herror⟩
  · have hcheckPair : ((), stateAfterCheck) = ((), before) :=
      (st_pure_ok () before _).1 hpure
    have hcheckState : stateAfterCheck = before := congrArg Prod.snd hcheckPair
    subst stateAfterCheck
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, _, _, hrest⟩
    rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, afterSource, _, hrest⟩
    have hbodyWitness : ∃ bodyBefore bodyOutput bodyAfter,
        rpBlockValue env [] body bodyBefore = .ok (bodyOutput, bodyAfter) ∧
          bodyAfter = after := by
      cases byRef <;> simp only [Bool.false_eq_true, if_true, if_false] at hrest
      all_goals
        rcases (st_bind_ok _ _ _ _).1 hrest with ⟨_, bodyBefore, _, hbodyRun⟩
        rcases (st_bind_ok _ _ _ _).1 hbodyRun with
          ⟨bodyOutput, bodyAfter, hbody, hcheckBody⟩
        have hstate : bodyAfter = after := by
          unfold liftV at hcheckBody
          cases hv : checkBlockValue before.nextVar bodyOutput.2.1 bodyOutput.1 with
          | error error => simp [hv] at hcheckBody
          | ok checked =>
            simp [hv] at hcheckBody
            cases hcheckBody
            rfl
        exact ⟨bodyBefore, bodyOutput, bodyAfter, hbody, hstate⟩
    rcases hbodyWitness with ⟨bodyBefore, bodyOutput, bodyAfter, hbody, hstate⟩
    refine ⟨hchild, (), hreplay, env, bodyBefore, bodyAfter, bodyOutput, ?_⟩
    exact ⟨rfl, rfl, rfl,
      by simpa [rpDemandNode, DemandNode.replayOutput] using hbody,
      by rw [hstate]; exact RLe.refl _⟩
  · unfold rejP at herror
    simp only [st_throw_ok] at herror

theorem rpDemandNode_expression_child (env : PEnv) (expr : Expr) (index : Nat)
    (child : DemandNode) (before after : RState) (roots : List RootRef)
    (hchild : (DemandNode.expression expr).child? index = some child)
    (hreplay : rpDemandNode env (.expression expr) before = .ok (roots, after)) :
    DemandNodeReplayChild env (.expression expr) index child before after := by
  cases expr with
  | lit _ _ | bool _ => simp [DemandNode.child?, DemandNode.children] at hchild
  | read place =>
    cases index with
    | zero =>
      have heq : child = .place place := by
        simpa [DemandNode.child?, DemandNode.children] using hchild.symm
      subst child
      exact rpDemandNode_expression_read_place_child env place 0 before after roots hchild hreplay
    | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
  | ref mutability place =>
    cases index with
    | zero =>
      have heq : child = .place place := by
        simpa [DemandNode.child?, DemandNode.children] using hchild.symm
      subst child
      exact rpDemandNode_expression_ref_place_child env mutability place 0 before after roots
        hchild hreplay
    | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
  | pop place origin =>
    cases index with
    | zero =>
      have heq : child = .place place := by
        simpa [DemandNode.child?, DemandNode.children] using hchild.symm
      subst child
      exact rpDemandNode_expression_pop_place_child env place origin 0 before after roots
        hchild hreplay
    | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
  | slice mutability view lower upper origin =>
    cases index with
    | zero =>
      have heq : child = .view view := by
        simpa [DemandNode.child?, DemandNode.children] using hchild.symm
      subst child
      exact rpDemandNode_expression_slice_view_child env mutability view lower upper origin 0
        before after roots hchild hreplay
    | succ index =>
      cases index with
      | zero =>
        have heq : child = .bound lower := by
          simpa [DemandNode.child?, DemandNode.children] using hchild.symm
        subst child
        exact rpDemandNode_expression_slice_lower_child env mutability view lower upper origin 1
          before after roots hchild hreplay
      | succ index =>
        cases index with
        | zero =>
          have heq : child = .bound upper := by
            simpa [DemandNode.child?, DemandNode.children] using hchild.symm
          subst child
          exact rpDemandNode_expression_slice_upper_child env mutability view lower upper origin 2
            before after roots hchild hreplay
        | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
  | len view =>
    cases index with
    | zero =>
      have heq : child = .view view := by
        simpa [DemandNode.child?, DemandNode.children] using hchild.symm
      subst child
      have hexpr : rpExpr env (.len view) before = .ok (roots, after) := by
        simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
      have htail : (do let _ ← rpView env view; pure ([] : List RootRef)) before =
          .ok (roots, after) := by simpa [rpExpr] using hexpr
      have hroots := rpComputation_result_empty (rpView env view) (pure ()) before after roots htail
      subst roots
      exact rpDemandNode_expression_len_view_child env view 0 before after hchild
        (by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay)
    | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
  | un op inner origin =>
    cases index with
    | zero =>
      have heq : child = .expression inner := by
        simpa [DemandNode.child?, DemandNode.children] using hchild.symm
      subst child
      cases op with
      | neg =>
        have hexpr : rpExpr env (.un .neg inner origin) before = .ok (roots, after) := by
          simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
        have hstage : (do let _ ← rpExpr env inner; noteAborts; pure ([] : List RootRef))
            before = .ok (roots, after) := by simpa [rpExpr] using hexpr
        have hroots := rpComputation_result_empty (rpExpr env inner) noteAborts
          before after roots hstage
        subst roots
        exact rpDemandNode_expression_un_child env .neg inner origin 0 before after hchild
          (by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay)
      | bitnot =>
        have hexpr : rpExpr env (.un .bitnot inner origin) before = .ok (roots, after) := by
          simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
        have hstage : (do let _ ← rpExpr env inner; pure ([] : List RootRef))
            before = .ok (roots, after) := by simpa [rpExpr] using hexpr
        have hroots := rpExpr_child_result_empty env inner (pure ()) before after roots hstage
        subst roots
        exact rpDemandNode_expression_un_child env .bitnot inner origin 0 before after hchild
          (by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay)
    | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
  | not inner =>
    cases index with
    | zero =>
      have heq : child = .expression inner := by
        simpa [DemandNode.child?, DemandNode.children] using hchild.symm
      subst child
      have hexpr : rpExpr env (.not inner) before = .ok (roots, after) := by
        simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
      have hstage : (do let _ ← rpExpr env inner; pure ([] : List RootRef)) before =
          .ok (roots, after) := by simpa [rpExpr] using hexpr
      have hroots := rpExpr_child_result_empty env inner (pure ()) before after roots hstage
      subst roots
      exact rpDemandNode_expression_not_child env inner 0 before after hchild
        (by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay)
    | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
  | fill ty inner =>
    cases index with
    | zero =>
      have heq : child = .expression inner := by
        simpa [DemandNode.child?, DemandNode.children] using hchild.symm
      subst child
      have hexpr : rpExpr env (.fill ty inner) before = .ok (roots, after) := by
        simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
      have hstage : (do let _ ← rpExpr env inner; pure ([] : List RootRef)) before =
          .ok (roots, after) := by simpa [rpExpr] using hexpr
      have hroots := rpExpr_child_result_empty env inner (pure ()) before after roots hstage
      subst roots
      exact rpDemandNode_expression_fill_child env ty inner 0 before after hchild
        (by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay)
    | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
  | conv kind target inner origin =>
    cases index with
    | zero =>
      have heq : child = .expression inner := by
        simpa [DemandNode.child?, DemandNode.children] using hchild.symm
      subst child
      cases kind with
      | widen =>
        have hexpr : rpExpr env (.conv .widen target inner origin) before =
            .ok (roots, after) := by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
        have hstage : (do let _ ← rpExpr env inner; pure ([] : List RootRef))
            before = .ok (roots, after) := by simpa [rpExpr] using hexpr
        have hroots := rpExpr_child_result_empty env inner (pure ()) before after roots hstage
        subst roots
        exact rpDemandNode_expression_conv_child env .widen target inner origin 0 before after hchild
          (by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay)
      | as =>
        have hexpr : rpExpr env (.conv .as target inner origin) before =
            .ok (roots, after) := by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
        have hstage : (do let _ ← rpExpr env inner; noteAborts; pure ([] : List RootRef))
            before = .ok (roots, after) := by simpa [rpExpr] using hexpr
        have hroots := rpComputation_result_empty (rpExpr env inner) noteAborts
          before after roots hstage
        subst roots
        exact rpDemandNode_expression_conv_child env .as target inner origin 0 before after hchild
          (by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay)
      | asUnchecked =>
        have hexpr : rpExpr env (.conv .asUnchecked target inner origin) before =
            .ok (roots, after) := by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
        have hstage : (do let _ ← rpExpr env inner; pure ([] : List RootRef))
            before = .ok (roots, after) := by simpa [rpExpr] using hexpr
        have hroots := rpExpr_child_result_empty env inner (pure ()) before after roots hstage
        subst roots
        exact rpDemandNode_expression_conv_child env .asUnchecked target inner origin 0 before after hchild
          (by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay)
    | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
  | bin op left right origin =>
    have hexpr : rpExpr env (.bin op left right origin) before = .ok (roots, after) := by
      simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
    cases hmay : op.mayAbort with
    | false =>
      have hstage : (do
          let _ ← rpExpr env left
          let _ ← rpExpr env right
          pure ([] : List RootRef)) before = .ok (roots, after) := by
        simpa [rpExpr, hmay] using hexpr
      have hroots := rpExpr_pair_result_empty env left right (pure ()) before after roots hstage
      subst roots
      cases index with
      | zero =>
        have heq : child = .expression left := by
          simpa [DemandNode.child?, DemandNode.children] using hchild.symm
        subst child
        exact rpDemandNode_expression_bin_left_child env op left right origin before after hreplay
      | succ index =>
        cases index with
        | zero =>
          have heq : child = .expression right := by
            simpa [DemandNode.child?, DemandNode.children] using hchild.symm
          subst child
          exact rpDemandNode_expression_bin_right_child env op left right origin before after hreplay
        | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
    | true =>
      have hstage : (do
          let _ ← rpExpr env left
          let _ ← rpExpr env right
          noteAborts
          pure ([] : List RootRef)) before = .ok (roots, after) := by
        simpa [rpExpr, hmay] using hexpr
      have hroots := rpExpr_pair_result_empty env left right noteAborts
        before after roots hstage
      subst roots
      cases index with
      | zero =>
        have heq : child = .expression left := by
          simpa [DemandNode.child?, DemandNode.children] using hchild.symm
        subst child
        exact rpDemandNode_expression_bin_left_child env op left right origin before after hreplay
      | succ index =>
        cases index with
        | zero =>
          have heq : child = .expression right := by
            simpa [DemandNode.child?, DemandNode.children] using hchild.symm
          subst child
          exact rpDemandNode_expression_bin_right_child env op left right origin before after hreplay
        | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
  | cmp op left right =>
    have hexpr : rpExpr env (.cmp op left right) before = .ok (roots, after) := by
      simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
    have hstage : (do
      let _ ← rpExpr env left
      let _ ← rpExpr env right
      pure ([] : List RootRef)) before = .ok (roots, after) := by simpa [rpExpr] using hexpr
    have hroots := rpExpr_pair_result_empty env left right (pure ()) before after roots hstage
    subst roots
    exact rpDemandNode_expression_cmp_child env op left right index before after child hchild
      (by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay)
  | and left right =>
    have hexpr : rpExpr env (.and left right) before = .ok (roots, after) := by
      simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
    have hstage : (do
      let _ ← rpExpr env left
      let _ ← rpExpr env right
      pure ([] : List RootRef)) before = .ok (roots, after) := by simpa [rpExpr] using hexpr
    have hroots := rpExpr_pair_result_empty env left right (pure ()) before after roots hstage
    subst roots
    exact rpDemandNode_expression_and_child env left right index before after child hchild
      (by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay)
  | or left right =>
    have hexpr : rpExpr env (.or left right) before = .ok (roots, after) := by
      simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
    have hstage : (do
      let _ ← rpExpr env left
      let _ ← rpExpr env right
      pure ([] : List RootRef)) before = .ok (roots, after) := by simpa [rpExpr] using hexpr
    have hroots := rpExpr_pair_result_empty env left right (pure ()) before after roots hstage
    subst roots
    exact rpDemandNode_expression_or_child env left right index before after child hchild
      (by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay)
  | call context args origin =>
    cases hindex : args[index]? with
    | none =>
      simp [DemandNode.child?, DemandNode.children, hindex, DemandNode.ofArg] at hchild
    | some arg =>
      cases arg with
      | byVal expr =>
        have hsome : some (.expression expr) = some child := by
          simpa [DemandNode.child?, DemandNode.children, hindex] using hchild
        have heq : child = .expression expr := (Option.some.inj hsome).symm
        subst child
        exact rpDemandNode_expression_callArg_child env context args origin index (.byVal expr)
          before after roots hindex hchild hreplay
      | byRef mutability place =>
        have hsome : some (.place place) = some child := by
          simpa [DemandNode.child?, DemandNode.children, hindex] using hchild
        have heq : child = .place place := (Option.some.inj hsome).symm
        subst child
        exact rpDemandNode_expression_callArg_child env context args origin index
          (.byRef mutability place) before after roots hindex hchild hreplay
  | push owner value origin =>
    cases index with
    | zero =>
      have heq : child = .place owner := by
        simpa [DemandNode.child?, DemandNode.children] using hchild.symm
      subst child
      exact rpDemandNode_expression_push_owner_child env owner value origin 0 before after roots
        hchild hreplay
    | succ index =>
      cases index with
      | zero =>
        have heq : child = .expression value := by
          simpa [DemandNode.child?, DemandNode.children] using hchild.symm
        subst child
        exact rpDemandNode_expression_push_value_child env owner value origin 1 before after roots
          hchild hreplay
      | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
  | ifE condition thenBlock elseBlock =>
    cases index with
    | zero =>
      have heq : child = .expression condition := by
        simpa [DemandNode.child?, DemandNode.children] using hchild.symm
      subst child
      exact rpDemandNode_expression_ifE_condition_child env condition thenBlock elseBlock
        before after roots hreplay
    | succ index =>
      cases index with
      | zero =>
        have heq : child = .block thenBlock := by
          simpa [DemandNode.child?, DemandNode.children] using hchild.symm
        subst child
        exact rpDemandNode_expression_ifE_then_child env condition thenBlock elseBlock
          before after roots hreplay
      | succ index =>
        cases index with
        | zero =>
          have heq : child = .block elseBlock := by
            simpa [DemandNode.child?, DemandNode.children] using hchild.symm
          subst child
          exact rpDemandNode_expression_ifE_else_child env condition thenBlock elseBlock
            before after roots hreplay
        | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
  | blockE block =>
    cases index with
    | zero =>
      have heq : child = .block block := by
        simpa [DemandNode.child?, DemandNode.children] using hchild.symm
      subst child
      exact rpDemandNode_expression_block_child env block 0 before after roots hchild hreplay
    | succ index => simp [DemandNode.child?, DemandNode.children] at hchild
  | arrLit arrayType exprs =>
    cases child with
    | expression item =>
      exact rpDemandNode_expression_arrItem_child env arrayType exprs index item before after
        hchild (by
          have hexpr : rpExpr env (.arrLit arrayType exprs) before = .ok (roots, after) := by
            simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
          have hstage : (do rpExprs env exprs; pure ([] : List RootRef)) before =
              .ok (roots, after) := by simpa [rpExpr] using hexpr
          have hroots := rpExprs_result_empty env exprs before after roots hstage
          simpa [hroots] using hreplay)
    | place _ | view _ | bound _ | statement _ | block _ =>
      simp only [DemandNode.child?, DemandNode.children, List.getElem?_map] at hchild
      cases hindex : exprs[index]? <;> simp [hindex] at hchild

  | structLit structType exprs =>
    cases child with
    | expression item =>
      have hexpr : rpExpr env (.structLit structType exprs) before = .ok (roots, after) := by
        simpa [rpDemandNode, DemandNode.replayOutput] using hreplay
      have hstage : (do rpExprs env exprs; pure ([] : List RootRef)) before =
          .ok (roots, after) := by simpa [rpExpr] using hexpr
      have hroots := rpExprs_result_empty env exprs before after roots hstage
      subst roots
      exact rpDemandNode_expression_structItem_child env structType exprs index item before after
        hchild (by simpa [rpDemandNode, DemandNode.replayOutput] using hreplay)
    | place _ | view _ | bound _ | statement _ | block _ =>
      simp only [DemandNode.child?, DemandNode.children, List.getElem?_map] at hchild
      cases hindex : exprs[index]? <;> simp [hindex] at hchild

private def ReplayWithin (env : PEnv) (node : DemandNode) (after : RState) : Prop :=
  ∃ before finish output, rpDemandNode env node before = .ok (output, finish) ∧ RLe finish after
private theorem replayWithin_tail {env : PEnv} {node : DemandNode} {middle after : RState}
    {α β : Type} {output : β} {head : α} {f : α → P β}
    (h : f head middle = .ok (output, after)) (hmono : PMono (f head))
    (inside : ReplayWithin env node middle) : ReplayWithin env node after := by
  obtain ⟨childBefore, childAfter, childOutput, hchild, hle⟩ := inside
  exact ⟨childBefore, childAfter, childOutput, hchild, hle.trans (hmono _ _ _ h)⟩
local syntax "extract_demand_replay " ident : tactic
macro_rules
| `(tactic| extract_demand_replay $h:ident) => `(tactic|
  first
  | exact ⟨_, _, _, by simpa only [rpDemandNode, DemandNode.replayOutput] using $h, RLe.refl _⟩
  | (rcases (st_bind_ok _ _ _ _).1 $h with ⟨head, middle, hhead, htail⟩
     first
     | (apply replayWithin_tail htail
        · repeat' (first
            | exact PMono.pure _ | exact PMono.liftV _
            | exact PMono.addReads _ | exact PMono.addWrites _ | exact PMono.addGrows _
            | exact PMono.addShrinks _ | exact PMono.noteAborts
            | exact PMono.profileWriteAbort _ _ _
            | exact rp_mono_all.1 _ _ | exact rp_mono_all.2.1 _ _
            | exact rp_mono_all.2.2.1 _ _
            | exact rp_mono_all.2.2.2.2.1 _ _ _
            | exact PMono.rej _ _ | exact PMono.get
            | exact PMono.modify _ (fun s => RLe.refl s)
            | exact PMono.modify _ (fun s =>
                ⟨Nat.le_refl _, fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun h => h⟩)
            | exact rp_mono_all.2.2.2.2.2.2.2.1 _ _
            | (simp only [bindRoots, checkResult]; exact PMono.liftV _)
            | refine PMono.bind ?_ (fun _ => ?_)
            | refine PMono.ite ?_ ?_
            | split)
        · extract_demand_replay hhead)
     | extract_demand_replay htail))
private theorem printArgs_replayWithin (env : PEnv) (args : List PrintArg)
    (child : DemandNode) (before after : RState)
    (hmem : some child ∈ args.map (fun arg => match arg with
      | .text _ => none | .expr expr => some (.expression expr)))
    (hreplay : rpPrintArgs env args before = .ok ((), after)) : ReplayWithin env child after := by
  induction args generalizing before with
  | nil => simp at hmem
  | cons arg args ih =>
    cases arg with
    | text text =>
      simp only [List.map_cons, List.mem_cons, Option.some_ne_none, false_or] at hmem
      exact ih before hmem (by simpa only [rpPrintArgs] using hreplay)
    | expr expr =>
      simp only [List.map_cons, List.mem_cons, Option.some.injEq] at hmem
      simp only [rpPrintArgs] at hreplay
      obtain ⟨roots, middle, hExpr, htail⟩ := (st_bind_ok _ _ _ _).1 hreplay
      rcases hmem with hchild | hrest
      · subst child
        exact replayWithin_tail htail (rp_mono_all.2.2.2.2.2.2.2.1 env args)
          ⟨before, middle, roots, by simpa only [rpDemandNode, DemandNode.replayOutput]
            using hExpr, RLe.refl middle⟩
      · exact ih middle hrest htail

set_option maxHeartbeats 1000000 in
private theorem statement_replayWithin (env : PEnv) (stmt : Stmt) (child : DemandNode)
    (before after : RState) (hmem : some child ∈ (DemandNode.statement stmt).children)
    (hreplay : rpStmt env stmt before = .ok ((), after)) : ReplayWithin env child after := by
  cases stmt with
  | assign p e o =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h
    all_goals
      have hc := Option.some.inj h
      subst child
      simp only [rpStmt] at hreplay
      extract_demand_replay hreplay
  | assignOp op p e o =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h
    all_goals
      have hc := Option.some.inj h
      subst child
      simp only [rpStmt] at hreplay
      extract_demand_replay hreplay
  | expr e o =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false] at hmem
    have h := hmem
    all_goals
      have hc := Option.some.inj h
      subst child
      simp only [rpStmt] at hreplay
      extract_demand_replay hreplay
  | append p v o =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h
    all_goals
      have hc := Option.some.inj h
      subst child
      simp only [rpStmt] at hreplay
      extract_demand_replay hreplay
  | popN p e o =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h
    all_goals
      have hc := Option.some.inj h
      subst child
      simp only [rpStmt] at hreplay
      extract_demand_replay hreplay
  | clear p o =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false] at hmem
    have h := hmem
    all_goals
      have hc := Option.some.inj h
      subst child
      simp only [rpStmt] at hreplay
      extract_demand_replay hreplay
  | assignWhole p e o =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h
    all_goals
      have hc := Option.some.inj h
      subst child
      simp only [rpStmt] at hreplay
      extract_demand_replay hreplay
  | assertS e o =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false] at hmem
    have h := hmem
    all_goals
      have hc := Option.some.inj h
      subst child
      simp only [rpStmt] at hreplay
      extract_demand_replay hreplay
  | exit e o =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false] at hmem
    have h := hmem
    all_goals
      have hc := Option.some.inj h
      subst child
      simp only [rpStmt] at hreplay
      extract_demand_replay hreplay
  | rebind x e o =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false] at hmem
    have h := hmem
    all_goals
      have hc := Option.some.inj h
      subst child
      simp only [rpStmt] at hreplay
      extract_demand_replay hreplay
  | brk _ | cont _ | abort _ _ => simp [DemandNode.children] at hmem
  | letS x e o =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false] at hmem
    have hc := Option.some.inj hmem
    subst child
    simp only [rpStmt] at hreplay
    rcases (st_bind_ok _ _ _ _).1 hreplay with ⟨initial, state, hget, htail⟩
    split at htail
    · extract_demand_replay htail
    · rcases (st_bind_ok _ _ _ _).1 htail with ⟨_, _, herror, _⟩
      exact ((rejP_ok _ _ _ _).1 herror).elim
  | resize p size fill o =>
    cases fill with
    | none =>
      simp only [DemandNode.children, Option.map, List.mem_cons, List.not_mem_nil,
        or_false, Option.some_ne_none, Option.some.injEq] at hmem
      rcases hmem with h | h
      all_goals
        subst child
        simp only [rpStmt] at hreplay
        extract_demand_replay hreplay
    | some inner =>
      simp only [DemandNode.children, Option.map, List.mem_cons, List.not_mem_nil,
        or_false, Option.some_ne_none, Option.some.injEq] at hmem
      rcases hmem with h | h | h
      all_goals
        subst child
        simp only [rpStmt] at hreplay
        extract_demand_replay hreplay
  | ifS c t f o =>
    cases f with
    | none =>
      simp only [DemandNode.children, Option.map, List.mem_cons, List.not_mem_nil,
        or_false, Option.some_ne_none, Option.some.injEq] at hmem
      rcases hmem with h | h
      all_goals
        subst child
        simp only [rpStmt] at hreplay
        extract_demand_replay hreplay
    | some inner =>
      simp only [DemandNode.children, Option.map, List.mem_cons, List.not_mem_nil,
        or_false, Option.some_ne_none, Option.some.injEq] at hmem
      rcases hmem with h | h | h
      all_goals
        subst child
        simp only [rpStmt] at hreplay
        extract_demand_replay hreplay
  | «while» c b o =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h
    all_goals
      have hc := Option.some.inj h
      subst child
      simp only [rpStmt] at hreplay
      all_goals extract_demand_replay hreplay
  | forRange x lo hi b o =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h
    all_goals
      have hc := Option.some.inj h
      subst child
      simp only [rpStmt] at hreplay
      all_goals extract_demand_replay hreplay
  | forEach x i v ref b o =>
    simp only [DemandNode.children, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h
    all_goals
      have hc := Option.some.inj h
      subst child
      cases ref <;> simp only [rpStmt, Bool.false_eq_true, ite_true, ite_false] at hreplay
      all_goals extract_demand_replay hreplay
  | ret e o =>
    cases e with
    | none => simp [DemandNode.children] at hmem
    | some inner =>
      simp only [DemandNode.children, Option.map, List.mem_cons, List.not_mem_nil,
        or_false, Option.some.injEq] at hmem
      subst child
      simp only [rpStmt] at hreplay
      extract_demand_replay hreplay
  | print args o =>
    simp only [DemandNode.children] at hmem
    simp only [rpStmt] at hreplay
    obtain ⟨_, middle, hargs, houtputs⟩ := (st_bind_ok _ _ _ _).1 hreplay
    exact replayWithin_tail houtputs PMono.noteOutputs
      (printArgs_replayWithin env args child before middle hmem hargs)

/-- Every indexed source child has a successful replay whose effects survive
in the enclosing node, with the same module, implementation, and context. -/
theorem rpDemandNode_child (env : PEnv) (parent : DemandNode) (index : Nat)
    (child : DemandNode) (before after : RState)
    (hchild : parent.child? index = some child)
    (hreplay : ∃ output, rpDemandNode env parent before = .ok (output, after)) :
    DemandNodeReplayChild env parent index child before after := by
  obtain ⟨output, hparent⟩ := hreplay
  cases parent with
  | expression expr =>
    exact rpDemandNode_expression_child env expr index child before after
      output hchild hparent
  | place place =>
    exact rpDemandNode_place_child env place index child before after
      output hchild hparent
  | view view =>
    exact rpDemandNode_view_child env view index child before after
      output hchild hparent
  | bound bound =>
    cases output
    exact rpDemandNode_bound_expression_child env bound index child before after hchild hparent
  | block block =>
    exact rpDemandNode_block_child env block index child before after
      output hchild hparent
  | statement stmt =>
    cases output
    have hstmt : rpStmt env stmt before = .ok ((), after) := by
      simpa only [rpDemandNode, DemandNode.replayOutput] using hparent
    obtain ⟨childBefore, childAfter, childOutput, hrun, hle⟩ :=
      statement_replayWithin env stmt child before after
        (demandNodeChild_mem_children hchild) hstmt
    exact demandNodeReplayChild_ofParts env (.statement stmt) index child before after
      () hchild hparent env childBefore childAfter childOutput rfl rfl rfl hrun hle

/-- A direct mutation at any source path contributes every external owner target
to the enclosing replay's shrink effects. -/
theorem DemandNodeAt.directShrink_targets
    {root node : DemandNode} {path : List Nat}
    (source : DemandNodeAt root path node)
    (env : PEnv) (before after : RState)
    (hreplay : ∃ output, rpDemandNode env root before = .ok (output, after))
    (owner : Place) (hdirect : node.directShrinkPlace? = some owner) :
    ∃ leafEnv leafBefore roots ownerState,
      leafEnv.mod = env.mod ∧ leafEnv.impl = env.impl ∧ leafEnv.ctx = env.ctx ∧
      rpPlace leafEnv owner leafBefore = .ok (roots, ownerState) ∧
      ∀ target, target ∈ rootsTargets roots → target ∈ after.eff.shrinks := by
  exact DemandNodeAt.directShrink_replay source env before after hreplay owner hdirect
    (fun hchild hparent => rpDemandNode_child _ _ _ _ _ _ hchild hparent)

/-- Expected mutation evidence selects the same syntax occurrence as the whole
block replay, including occurrences inside call arguments and nested blocks. -/
theorem DemandExpectedSourceAt.directShrink_block_replay
    {m : Module} {owner : Nat} {path : List Nat} {node : DemandNode}
    {expected : DemandExpectedPoint} {block : Block} {ownerPlace : Place}
    (sourceAt : DemandExpectedSourceAt m owner path node .mutation expected)
    (root : demandRoot? m owner = some (.block block))
    (direct : node.directShrinkPlace? = some ownerPlace)
    (env : PEnv) (before after : RState) (roots : List RootRef) (range : Nat × Nat)
    (replay : rpBlockValue env [] block before = .ok ((roots, range), after)) :
    ∃ leafEnv leafBefore ownerRoots ownerState,
      leafEnv.mod = env.mod ∧ leafEnv.impl = env.impl ∧ leafEnv.ctx = env.ctx ∧
      rpPlace leafEnv ownerPlace leafBefore = .ok (ownerRoots, ownerState) ∧
      ∀ target, target ∈ rootsTargets ownerRoots → target ∈ after.eff.shrinks := by
  obtain ⟨sourceRoot, hroot, source⟩ := sourceAt.sourceFacts.1
  have hrootEq : sourceRoot = .block block := Option.some.inj (hroot.symm.trans root)
  subst sourceRoot
  exact DemandNodeAt.directShrink_targets source env before after
    ⟨(roots, range), by simpa only [rpDemandNode, DemandNode.replayOutput] using replay⟩
    ownerPlace direct

theorem DemandExpectedSourceAt.directShrink_ifThenBlockStatement_replay
    {m : Module} {owner : Nat} {expected : DemandExpectedPoint}
    {scope : Nat} {stmts : List Stmt} {value : Option Expr}
    {outerIndex innerIndex blockScope : Nat} {condition : Expr}
    {blockStmts : List Stmt} {blockValue : Option Expr} {elseBlock : Block}
    {origin : OriginId} {stmt : Stmt} {ownerPlace : Place} (env : PEnv)
    (sourceAt : DemandExpectedSourceAt m owner [outerIndex, 1, innerIndex]
      (.statement stmt) .mutation expected)
    (root : demandRoot? m owner = some (.block (.mk scope stmts value)))
    (outerChild : (DemandNode.block (.mk scope stmts value)).child? outerIndex =
      some (.statement (.ifS condition (.mk blockScope blockStmts blockValue)
        (some elseBlock) origin)))
    (direct : DemandNode.directShrinkPlace? (.statement stmt) = some ownerPlace)
    (state : RState) (rho : List RootRef) (range : Nat × Nat) (state' : RState)
    (replay : rpBlockValue env [] (.mk scope stmts value) state =
      .ok ((rho, range), state')) :
    ∃ before roots ownerState,
      rpPlace { env with scopes := blockScope :: scope :: env.scopes } ownerPlace before =
        .ok (roots, ownerState) ∧
      ∀ target, target ∈ rootsTargets roots → target ∈ state'.eff.shrinks := by
  rcases sourceAt.sourceFacts.1 with ⟨sourceRoot, sourceRootEq, path⟩
  have rootEq : sourceRoot = .block (.mk scope stmts value) :=
    Option.some.inj (sourceRootEq.symm.trans root)
  subst sourceRoot
  cases path with
  | child houter tail =>
    rename_i outerNode
    have outerNodeEq : outerNode = .statement
        (.ifS condition (.mk blockScope blockStmts blockValue) (some elseBlock) origin) :=
      Option.some.inj (houter.symm.trans outerChild)
    subst outerNode
    cases tail with
    | child hthen tail =>
      rename_i thenNode
      have thenNodeEq : thenNode = .block (.mk blockScope blockStmts blockValue) := by
        simpa [DemandNode.child?, DemandNode.children] using hthen.symm
      subst thenNode
      cases tail with
      | child hinner final =>
        cases final with
        | here _ =>
          have houterStmt : stmts[outerIndex]? =
              some (.ifS condition (.mk blockScope blockStmts blockValue)
                (some elseBlock) origin) :=
            block_child_statement_index scope stmts value outerIndex
              (.ifS condition (.mk blockScope blockStmts blockValue)
                (some elseBlock) origin) outerChild
          have hinnerIndex := block_child_statement_index blockScope blockStmts blockValue
            innerIndex stmt hinner
          obtain ⟨_, stateAfterStmts, hstmts, hvalue, _, _⟩ :=
            rpBlockValue_ok env [] scope stmts value state rho range state' replay
          have hstmts' : rpStmts { env with scopes := scope :: env.scopes } stmts state =
              .ok ((), stateAfterStmts) := by simpa using hstmts
          obtain ⟨beforeIf, afterIf, hif, hmonoStmts⟩ :=
            rpStmts_member_replay { env with scopes := scope :: env.scopes }
              stmts outerIndex (.ifS condition (.mk blockScope blockStmts blockValue)
                (some elseBlock) origin) state stateAfterStmts houterStmt hstmts'
          obtain ⟨beforeBlock, blockRoots, blockRange, afterBlock, hblock, hmonoElse⟩ :=
            rpStmt_ifSThen_block_replay { env with scopes := scope :: env.scopes }
              condition (.mk blockScope blockStmts blockValue) (some elseBlock) origin
              beforeIf afterIf hif
          obtain ⟨before, roots, ownerState, howner, hrecorded⟩ :=
            rpBlockValue_directShrink_statement
              { env with scopes := scope :: env.scopes }
              blockScope blockStmts blockValue innerIndex stmt ownerPlace beforeBlock
              blockRoots blockRange afterBlock hinnerIndex direct hblock
          have hmonoValue : RLe stateAfterStmts state' := by
            cases value with
            | none =>
              obtain ⟨_, rfl⟩ := hvalue
              exact RLe.refl _
            | some expr =>
              exact rpExpr_mono (by simpa using hvalue)
          refine ⟨before, roots, ownerState, howner, ?_⟩
          intro target htarget
          exact (hmonoElse.trans (hmonoStmts.trans hmonoValue)).2.2.2.2.1 target
            (hrecorded target htarget)

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
    | .unknown =>
      (callEffects callee cctx ar e).unknown = true ∧
      ∀ t, t ∈ rootsTargets ar.flatten → t ∈ (callEffects callee cctx ar e).writes
    | .known sm =>
      (∀ t, t ∈ mapCallTargets callee cctx ar sm.reads → t ∈ (callEffects callee cctx ar e).reads) ∧
      (∀ t, t ∈ mapCallTargets callee cctx ar sm.writes → t ∈ (callEffects callee cctx ar e).writes) ∧
      (∀ t, t ∈ mapCallTargets callee cctx ar sm.grows → t ∈ (callEffects callee cctx ar e).grows) := by
  cases h : callee.summary with
  | unknown =>
    simp only [callEffects, h]
    exact ⟨trivial, addTargets_right _ _⟩
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
