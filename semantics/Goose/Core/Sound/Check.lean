import Goose.Core.Sound.Frame
import Goose.Core.Sound.Attr

/-!
Reading facts off a successful run of the validator: laws of its two monads,
and that the root pass only ever adds to the effects it has collected.
-/

namespace Goose.Core.Sound
open Goose.Core

section Monad
variable {σ ε α β : Type}

@[chk] theorem st_bind_ok (x : StateT σ (Except ε) α) (f : α → StateT σ (Except ε) β) (s : σ) (r : β × σ) :
    (x >>= f) s = .ok r ↔ ∃ a s1, x s = .ok (a, s1) ∧ f a s1 = .ok r := by
  show (StateT.bind x f) s = .ok r ↔ _
  unfold StateT.bind
  cases h : x s with
  | error e => simp [bind, Except.bind]
  | ok p =>
    obtain ⟨a, s1⟩ := p
    simp only [bind, Except.bind, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · intro h'; exact ⟨a, s1, ⟨rfl, rfl⟩, h'⟩
    · rintro ⟨a', s1', ⟨rfl, rfl⟩, h'⟩; exact h'

@[chk] theorem st_pure_ok (a : α) (s : σ) (r : α × σ) :
    (pure a : StateT σ (Except ε) α) s = .ok r ↔ r = (a, s) := by
  show Except.ok (a, s) = Except.ok r ↔ _
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

@[chk] theorem st_throw_ok (e : ε) (s : σ) (r : α × σ) :
    (throw e : StateT σ (Except ε) α) s = .ok r ↔ False := by
  show (Except.error e : Except ε (α × σ)) = Except.ok r ↔ False
  simp

@[chk] theorem st_ite_ok (c : Prop) [Decidable c] (x y : StateT σ (Except ε) α) (s : σ) (r : α × σ) :
    (if c then x else y) s = .ok r ↔ (c ∧ x s = .ok r) ∨ (¬ c ∧ y s = .ok r) := by
  by_cases h : c <;> simp [h]

@[chk] theorem st_get_ok (s : σ) (r : σ × σ) :
    (get : StateT σ (Except ε) σ) s = .ok r ↔ r = (s, s) := by
  show Except.ok (s, s) = Except.ok r ↔ _
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

@[chk] theorem st_set_ok (s' s : σ) (r : PUnit × σ) :
    (set s' : StateT σ (Except ε) PUnit) s = .ok r ↔ r = (⟨⟩, s') := by
  show Except.ok (PUnit.unit, s') = Except.ok r ↔ _
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

@[chk] theorem st_modify_ok (f : σ → σ) (s : σ) (r : PUnit × σ) :
    (modify f : StateT σ (Except ε) PUnit) s = .ok r ↔ r = (⟨⟩, f s) := by
  show Except.ok (PUnit.unit, f s) = Except.ok r ↔ _
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

@[chk] theorem ex_bind_ok (x : Except ε α) (f : α → Except ε β) (b : β) :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

@[chk] theorem ex_ite_ok (c : Prop) [Decidable c] (x y : Except ε α) (b : α) :
    (if c then x else y) = .ok b ↔ (c ∧ x = .ok b) ∨ (¬ c ∧ y = .ok b) := by
  by_cases h : c <;> simp [h]

@[chk] theorem ex_pure_ok (a b : α) : (pure a : Except ε α) = .ok b ↔ b = a := by
  show Except.ok a = Except.ok b ↔ _
  constructor
  · intro h; cases h; rfl
  · intro h; rw [h]

end Monad

@[chk] theorem reject_ok (r : Rule) (msg : String) (a : α) : (reject r msg : V α) = .ok a ↔ False := by
  simp [reject]

@[chk] theorem rej_ok (r : Rule) (msg : String) (s : Nat) (a : α × Nat) : (rej r msg : T α) s = .ok a ↔ False :=
  st_throw_ok _ _ _

@[chk] theorem rejP_ok (r : Rule) (msg : String) (s : RState) (a : α × RState) :
    (rejP r msg : P α) s = .ok a ↔ False :=
  st_throw_ok _ _ _

@[chk] theorem liftV_ok (x : V α) (s : RState) (r : α × RState) :
    liftV x s = .ok r ↔ x = .ok r.1 ∧ r.2 = s := by
  obtain ⟨a, s'⟩ := r
  unfold liftV
  cases x with
  | error e => simp
  | ok b =>
    simp only [Except.ok.injEq, Prod.mk.injEq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩

@[chk] theorem unit_exists (p : Unit → Prop) : (∃ a, p a) ↔ p () :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩

theorem forAll_ok (l : List α) (f : α → V Unit) : forAll l f = .ok () ↔ ∀ a, a ∈ l → f a = .ok () := by
  induction l with
  | nil => simp [forAll]; rfl
  | cons a rest ih =>
    simp only [forAll, ex_bind_ok, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨u, h1, h2⟩; exact ⟨h1, ih.1 h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(), h1, ih.2 h2⟩

/-! ### The root pass only adds effects -/

def RLe (a b : RState) : Prop := a.nextVar ≤ b.nextVar ∧ EffLe a.eff b.eff

theorem RLe.refl (a : RState) : RLe a a := ⟨Nat.le_refl _, EffLe.refl _⟩

theorem RLe.trans {a b c : RState} (h1 : RLe a b) (h2 : RLe b c) : RLe a c :=
  ⟨Nat.le_trans h1.1 h2.1, h1.2.trans h2.2⟩

def PMono (x : P α) : Prop := ∀ st a st', x st = .ok (a, st') → RLe st st'

theorem PMono.bind {x : P α} {f : α → P β} (hx : PMono x) (hf : ∀ a, PMono (f a)) :
    PMono (x >>= f) := by
  intro st b st' h
  obtain ⟨a, s1, h1, h2⟩ := (st_bind_ok _ _ _ _).1 h
  exact (hx _ _ _ h1).trans (hf a _ _ _ h2)

theorem PMono.pure (a : α) : PMono (pure a : P α) := by
  intro st b st' h
  have := (st_pure_ok _ _ _).1 h
  cases this; exact RLe.refl _

theorem PMono.rej (r : Rule) (msg : String) : PMono (rejP r msg : P α) := by
  intro st b st' h
  exact ((rejP_ok _ _ _ _).1 h).elim

theorem PMono.liftV (x : V α) : PMono (liftV x) := by
  intro st b st' h
  obtain ⟨_, h2⟩ := (liftV_ok _ _ _).1 h
  cases h2; exact RLe.refl _

theorem PMono.get : PMono (get : P RState) := by
  intro st b st' h
  have := (st_get_ok _ _).1 h
  cases this; exact RLe.refl _

theorem PMono.modify (f : RState → RState) (hf : ∀ s, RLe s (f s)) : PMono (modify f : P PUnit) := by
  intro st b st' h
  have := (st_modify_ok _ _ _).1 h
  cases this; exact hf st

theorem PMono.ite {c : Prop} [Decidable c] {x y : P α} (hx : PMono x) (hy : PMono y) :
    PMono (if c then x else y) := by
  by_cases h : c <;> simp [h, hx, hy]

theorem addTargets_left (old new : List Target) : ∀ t, t ∈ old → t ∈ addTargets old new := by
  unfold addTargets
  induction new generalizing old with
  | nil => intro t ht; simpa using ht
  | cons x xs ih =>
    intro t ht
    simp only [List.foldl_cons]
    apply ih
    split
    · exact ht
    · exact List.mem_append_left _ ht

theorem addTargets_right (old new : List Target) : ∀ t, t ∈ new → t ∈ addTargets old new := by
  unfold addTargets
  induction new generalizing old with
  | nil => intro t ht; cases ht
  | cons x xs ih =>
    intro t ht
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 ht with rfl | ht
    · have := addTargets_left (if old.contains t = true then old else old ++ [t]) xs t
        (by split
            · rename_i h; simpa using h
            · simp)
      simpa [addTargets] using this
    · exact ih _ t ht

theorem PMono.addReads (rs : List RootRef) : PMono (addReads rs) := by
  unfold Goose.Core.addReads addRoots
  exact PMono.modify _ fun s => ⟨Nat.le_refl _, addTargets_left _ _, fun _ h => h, fun _ h => h, fun h => h⟩

theorem PMono.addWrites (rs : List RootRef) : PMono (addWrites rs) := by
  unfold Goose.Core.addWrites addRoots
  exact PMono.modify _ fun s => ⟨Nat.le_refl _, fun _ h => h, addTargets_left _ _, fun _ h => h, fun h => h⟩

theorem PMono.addGrows (rs : List RootRef) : PMono (addGrows rs) := by
  unfold Goose.Core.addGrows addRoots
  exact PMono.modify _ fun s => ⟨Nat.le_refl _, fun _ h => h, fun _ h => h, addTargets_left _ _, fun h => h⟩

theorem PMono.noteAborts : PMono noteAborts := by
  unfold Goose.Core.noteAborts
  exact PMono.modify _ fun s => RLe.refl _

theorem PMono.noteOutputs : PMono noteOutputs := by
  unfold Goose.Core.noteOutputs
  exact PMono.modify _ fun s => RLe.refl _

theorem PMono.rpCall (env : PEnv) (c : ContextId) (ar : List (List RootRef)) : PMono (rpCall env c ar) := by
  unfold Goose.Core.rpCall
  repeat' (first
    | exact PMono.pure _ | exact PMono.rej _ _ | exact PMono.liftV _
    | refine PMono.bind ?_ (fun _ => ?_)
    | split)
  refine PMono.modify _ fun s => ⟨Nat.le_refl _, ?_⟩
  simp only [callEffects]
  split
  · exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ => rfl⟩
  · exact ⟨addTargets_left _ _, addTargets_left _ _, addTargets_left _ _, fun h => h⟩

theorem PMono.readRoots (env : PEnv) (p : Place) : PMono (readRoots env p) := by
  unfold Goose.Core.readRoots
  repeat' (first | exact PMono.pure _ | exact PMono.rej _ _ | split)

macro "pm" : tactic => `(tactic| repeat' (first
    | exact PMono.pure _ | exact PMono.rej _ _ | exact PMono.liftV _ | exact PMono.get
    | exact PMono.addReads _ | exact PMono.addWrites _ | exact PMono.addGrows _
    | exact PMono.noteAborts | exact PMono.noteOutputs | exact PMono.rpCall _ _ _
    | exact PMono.readRoots _ _
    | exact PMono.modify _ (fun s => ⟨Nat.le_add_right _ _, EffLe.refl _⟩)
    | exact PMono.modify _ (fun s => ⟨Nat.le_trans (Nat.le_add_right _ 1) (Nat.le_add_right _ _), EffLe.refl _⟩)
    | exact PMono.modify _ (fun s => ⟨Nat.le_refl _, fun _ h => h, fun _ h => h, fun _ h => h, fun h => h⟩)
    | with_reducible apply_assumption
    | refine PMono.bind ?_ (fun _ => ?_)
    | refine PMono.ite ?_ ?_
    | split))

/-- Every function of the root pass leaves the declaration counter no smaller
and every collected effect in place. -/
theorem rp_mono_all :
    (∀ env p, PMono (rpPlace env p)) ∧ (∀ env v, PMono (rpView env v)) ∧ (∀ env e, PMono (rpExpr env e)) ∧
    (∀ env es, PMono (rpExprs env es)) ∧ (∀ env pre b, PMono (rpBlockValue env pre b)) ∧
    (∀ env ss, PMono (rpStmts env ss)) ∧ (∀ env s, PMono (rpStmt env s)) ∧
    (∀ env as, PMono (rpPrintArgs env as)) ∧ (∀ env as, PMono (rpArgs env as)) ∧
    (∀ env b, PMono (rpBound env b)) := by
  apply rpPlace.mutual_induct
    (motive_1 := fun env p => PMono (rpPlace env p)) (motive_2 := fun env v => PMono (rpView env v))
    (motive_3 := fun env e => PMono (rpExpr env e)) (motive_4 := fun env es => PMono (rpExprs env es))
    (motive_5 := fun env pre b => PMono (rpBlockValue env pre b))
    (motive_6 := fun env ss => PMono (rpStmts env ss)) (motive_7 := fun env s => PMono (rpStmt env s))
    (motive_8 := fun env as => PMono (rpPrintArgs env as)) (motive_9 := fun env as => PMono (rpArgs env as))
    (motive_10 := fun env b => PMono (rpBound env b))
  all_goals (intros; (try cases ‹Option Expr›); (try cases ‹Option Block›); simp only [rpPlace, rpView, rpExpr, rpExprs, rpBlockValue, rpStmts, rpStmt, rpPrintArgs, rpArgs, rpBound, bindRoots, checkResult]; pm)

theorem rpPlace_mono {env : PEnv} {p : Place} {st st' : RState} {a : List RootRef}
    (h : rpPlace env p st = .ok (a, st')) : RLe st st' := rp_mono_all.1 env p _ _ _ h
theorem rpView_mono {env : PEnv} {v : View} {st st' : RState} {a : List RootRef}
    (h : rpView env v st = .ok (a, st')) : RLe st st' := rp_mono_all.2.1 env v _ _ _ h
theorem rpExpr_mono {env : PEnv} {e : Expr} {st st' : RState} {a : List RootRef}
    (h : rpExpr env e st = .ok (a, st')) : RLe st st' := rp_mono_all.2.2.1 env e _ _ _ h
theorem rpExprs_mono {env : PEnv} {es : List Expr} {st st' : RState} {a : Unit}
    (h : rpExprs env es st = .ok (a, st')) : RLe st st' := rp_mono_all.2.2.2.1 env es _ _ _ h
theorem rpBlockValue_mono {env : PEnv} {pre : List VarId} {b : Block} {st st' : RState}
    {a : List RootRef × (Nat × Nat)}
    (h : rpBlockValue env pre b st = .ok (a, st')) : RLe st st' := rp_mono_all.2.2.2.2.1 env pre b _ _ _ h
theorem rpStmts_mono {env : PEnv} {ss : List Stmt} {st st' : RState} {a : Unit}
    (h : rpStmts env ss st = .ok (a, st')) : RLe st st' := rp_mono_all.2.2.2.2.2.1 env ss _ _ _ h
theorem rpStmt_mono {env : PEnv} {x : Stmt} {st st' : RState} {a : Unit}
    (h : rpStmt env x st = .ok (a, st')) : RLe st st' := rp_mono_all.2.2.2.2.2.2.1 env x _ _ _ h
theorem rpPrintArgs_mono {env : PEnv} {as : List PrintArg} {st st' : RState} {a : Unit}
    (h : rpPrintArgs env as st = .ok (a, st')) : RLe st st' := rp_mono_all.2.2.2.2.2.2.2.1 env as _ _ _ h
theorem rpArgs_mono {env : PEnv} {as : List Arg} {st st' : RState} {a : List (List RootRef)}
    (h : rpArgs env as st = .ok (a, st')) : RLe st st' := rp_mono_all.2.2.2.2.2.2.2.2.1 env as _ _ _ h
theorem rpBound_mono {env : PEnv} {b : Bound} {st st' : RState} {a : Unit}
    (h : rpBound env b st = .ok (a, st')) : RLe st st' := rp_mono_all.2.2.2.2.2.2.2.2.2 env b _ _ _ h

/-! ### Helpers of the typing pass -/

@[chk] theorem checkOrg_ok (env : TEnv) (o : OriginId) (s : Nat) (r : Unit × Nat) :
    checkOrg env o s = .ok r ↔ o < env.mod.origins.size ∧ r = ((), s) := by
  unfold checkOrg
  rw [st_ite_ok]
  simp [st_pure_ok, rej_ok]

@[chk] theorem requireInt_ok (w : String) (t : Ty) (s : Nat) (r : IntTy × Nat) :
    requireInt w t s = .ok r ↔ t = .int r.1 ∧ r.2 = s := by
  obtain ⟨i, s'⟩ := r
  cases t <;> simp [requireInt, st_pure_ok, rej_ok]
  intro _; exact ⟨Eq.symm, Eq.symm⟩

@[chk] theorem requireBool_ok (w : String) (t : Ty) (s : Nat) (r : Unit × Nat) :
    requireBool w t s = .ok r ↔ t = .bool ∧ r.2 = s := by
  obtain ⟨i, s'⟩ := r
  cases t <;> simp [requireBool, st_pure_ok, rej_ok]

@[chk] theorem requireWrite_ok (w : String) (b : Bool) (s : Nat) (r : Unit × Nat) :
    requireWrite w b s = .ok r ↔ b = true ∧ r.2 = s := by
  obtain ⟨i, s'⟩ := r
  cases b <;> simp [requireWrite, st_pure_ok, rej_ok]

@[chk] theorem varOf_ok (env : TEnv) (x : VarId) (s : Nat) (r : LocalVar × Nat) :
    varOf env x s = .ok r ↔ x ∈ env.visible ∧ env.vars[x]? = some r.1 ∧ r.2 = s := by
  obtain ⟨lv, s'⟩ := r
  unfold varOf
  by_cases hx : x ∈ env.visible
  · cases hv : env.vars[x]? <;> simp [hx, st_pure_ok, rej_ok]
    intro _; exact ⟨Eq.symm, Eq.symm⟩
  · simp [hx, rej_ok]

/-- Read the facts off a hypothesis saying a validator computation succeeded. -/
macro "inv" "at" h:ident : tactic =>
  `(tactic| simp only [chk, false_and, and_false, exists_false, exists_const, or_false, false_or,
      and_true, true_and, Prod.mk.injEq, Prod.exists, if_true, if_false, Bool.false_eq_true,
      reduceCtorEq, and_assoc, exists_eq_left, exists_eq_left', exists_eq_right, exists_eq_right',
      exists_and_left, exists_eq', StateT.run] at $h:ident)

theorem declare_ok (env : TEnv) (x : VarId) (sc : Nat) (s : Nat) (r : LocalVar × Nat)
    (h : declare env x sc s = .ok r) :
    x = s ∧ env.vars[x]? = some r.1 ∧ r.1.scope = sc ∧ r.1.ty.storable = true ∧ r.2 = s + 1 := by
  obtain ⟨lv, s'⟩ := r
  unfold declare at h
  simp only [st_bind_ok, st_get_ok] at h
  obtain ⟨_, _, hgs, h⟩ := h
  cases hgs
  rcases (st_ite_ok _ _ _ _ _).1 h with ⟨hx, h⟩ | ⟨_, h⟩
  · cases hv : env.vars[x]? with
    | none => simp only [hv] at h; exact ((rej_ok _ _ _ _).1 h).elim
    | some lv' =>
      simp only [hv] at h
      rcases (st_ite_ok _ _ _ _ _).1 h with ⟨h1, h⟩ | ⟨_, h⟩
      · rcases (st_ite_ok _ _ _ _ _).1 h with ⟨h2, h⟩ | ⟨_, h⟩
        · simp only [st_bind_ok, st_set_ok, st_pure_ok] at h
          obtain ⟨_, _, e1, e2⟩ := h
          cases e1; cases e2
          exact ⟨hx, rfl, h1, h2, rfl⟩
        · inv at h
      · inv at h
  · inv at h

/-- Two typing environments that differ at most in the visible variables. -/
structure TSame (a b : TEnv) : Prop where
  mod : b.mod = a.mod
  impl : b.impl = a.impl
  vars : b.vars = a.vars
  loops : b.loops = a.loops
  inExpr : b.inExpr = a.inExpr
  scopes : b.scopes = a.scopes
  sub : ∀ x, x ∈ a.visible → x ∈ b.visible

theorem TSame.refl (a : TEnv) : TSame a a := ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => h⟩

theorem TSame.trans {a b c : TEnv} (h1 : TSame a b) (h2 : TSame b c) : TSame a c :=
  ⟨h2.mod.trans h1.mod, h2.impl.trans h1.impl, h2.vars.trans h1.vars, h2.loops.trans h1.loops,
   h2.inExpr.trans h1.inExpr, h2.scopes.trans h1.scopes, fun x h => h2.sub x (h1.sub x h)⟩

theorem TSame.cons (a : TEnv) (x : VarId) : TSame a { a with visible := x :: a.visible } :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ h => List.mem_cons_of_mem _ h⟩

theorem declarePre_ok : ∀ (pre : List (VarId × Ty)) (env : TEnv) (sc s : Nat) (env1 : TEnv) (s1 : Nat),
    declarePre env sc pre s = .ok (env1, s1) →
    TSame env env1 ∧ (∀ y, y ∈ env1.visible ↔ y ∈ pre.map Prod.fst ∨ y ∈ env.visible) ∧
    (∀ p, p ∈ pre → ∃ lv, env.vars[p.1]? = some lv ∧ lv.scope = sc ∧ lv.ty.storable = true ∧ lv.ty = p.2) ∧
    pre.map Prod.fst = List.range' s pre.length
  | [], env, sc, s, env1, s1, h => by
    simp only [declarePre, st_pure_ok, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨TSame.refl _, by simp, by simp, by simp⟩
  | (x, ty) :: rest, env, sc, s, env1, s1, h => by
    simp only [declarePre, st_bind_ok] at h
    obtain ⟨lv, s2, hd, h⟩ := h
    obtain ⟨rfl, hv, hsc, hst, hs2⟩ := declare_ok _ _ _ _ _ hd
    simp only at hs2 hv hsc hst
    subst hs2
    by_cases hty : (lv.ty == ty) = true
    · simp only [hty, if_true] at h
      obtain ⟨h1, h2, h3, h4⟩ := declarePre_ok rest _ sc _ env1 s1 h
      refine ⟨(TSame.cons env x).trans h1, ?_, ?_, ?_⟩
      · intro y; rw [h2]; simp [or_assoc, or_comm, or_left_comm]
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact ⟨lv, hv, hsc, hst, by simpa using hty⟩
        · exact h3 p hp
      · simp [h4, List.range'_succ]
    · simp only [hty] at h; inv at h

end Goose.Core.Sound
