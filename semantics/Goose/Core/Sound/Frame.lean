import Goose.Core.Sound.Store

/-!
The invariant of one activation: how the validator's view of a function body
(visible variables, open scopes, root annotations) describes the store while
the body runs.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

/-- What is fixed while one function body, or one global initializer, runs:
how many globals are initialized, which roots each parameter's argument may
point into, the effects the body is allowed, and a scope instance below which
every root of a caller lies. -/
structure World where
  G : Nat
  P : Nat → RootInst → Prop
  E : Eff
  base : Nat

/-- The root instance a static root denotes in an activation. -/
def RootIn (env : Env) (P : Nat → RootInst → Prop) (r : RootInst) : RootRef → Prop
  | .local y => ∃ lv si, env.vars[y]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
      r = .local env.act si y
  | .global g => r = .global g
  | .param j => P j r

/-- The root instances a static root set denotes. -/
def Gam (env : Env) (P : Nat → RootInst → Prop) (rho : List RootRef) (r : RootInst) : Prop :=
  ∃ q, q ∈ rho ∧ RootIn env P r q

/-- An activation with no variables: only parameters and globals denote. -/
def noEnv : Env := ⟨#[], 0, [], 0⟩

theorem Gam.subset {env : Env} {P : Nat → RootInst → Prop} {rho rho' : List RootRef} {r : RootInst}
    (h : Gam env P rho r) (hs : ∀ q, q ∈ rho → q ∈ rho') : Gam env P rho' r := by
  obtain ⟨q, hq, hr⟩ := h
  exact ⟨q, hs q hq, hr⟩

theorem subsetRoots_mem {a b : List RootRef} (h : subsetRoots a b = true) :
    ∀ q, q ∈ a → q ∈ b := by
  intro q hq
  simp only [subsetRoots, List.all_eq_true] at h
  simpa using h q hq

theorem unionRoots_left (a b : List RootRef) : ∀ q, q ∈ a → q ∈ unionRoots a b := by
  unfold unionRoots
  induction b generalizing a with
  | nil => intro q hq; simpa using hq
  | cons x xs ih =>
    intro q hq
    simp only [List.foldl_cons]
    apply ih
    split
    · exact hq
    · exact List.mem_append_left _ hq

theorem unionRoots_right (a b : List RootRef) : ∀ q, q ∈ b → q ∈ unionRoots a b := by
  unfold unionRoots
  induction b generalizing a with
  | nil => intro q hq; cases hq
  | cons x xs ih =>
    intro q hq
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hq with rfl | hq
    · have := unionRoots_left (if a.contains q = true then a else a ++ [q]) xs q
        (by split
            · rename_i h; simpa using h
            · simp)
      simpa [unionRoots] using this
    · exact ih _ q hq

/-! ### Effects an activation may have -/

def TargetOk (W : World) : Target → Prop
  | .global g => g < W.G
  | .param j => ∀ r, W.P j r → ∀ g, r = .global g → g < W.G

def EffOk (W : World) (E : Eff) : Prop :=
  E.unknown = false ∧ ∀ t, (t ∈ E.reads ∨ t ∈ E.writes ∨ t ∈ E.grows) → TargetOk W t

/-- Either every global is initialized, or the body's allowed effects touch
only initialized ones. -/
def Perm (m : Module) (W : World) : Prop := m.globals.size ≤ W.G ∨ EffOk W W.E

def EffLe (a b : Eff) : Prop :=
  (∀ t, t ∈ a.reads → t ∈ b.reads) ∧ (∀ t, t ∈ a.writes → t ∈ b.writes) ∧
  (∀ t, t ∈ a.grows → t ∈ b.grows) ∧ (a.unknown = true → b.unknown = true)

theorem EffLe.refl (a : Eff) : EffLe a a := ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun h => h⟩

theorem EffLe.trans {a b c : Eff} (h1 : EffLe a b) (h2 : EffLe b c) : EffLe a c :=
  ⟨fun t h => h2.1 t (h1.1 t h), fun t h => h2.2.1 t (h1.2.1 t h),
   fun t h => h2.2.2.1 t (h1.2.2.1 t h), fun h => h2.2.2.2 (h1.2.2.2 h)⟩

theorem mem_rootsTargets_global {rho : List RootRef} {g : GlobalId} (h : RootRef.global g ∈ rho) :
    Target.global g ∈ rootsTargets rho := by
  simp only [rootsTargets, List.mem_filterMap]
  exact ⟨_, h, rfl⟩

theorem mem_rootsTargets_param {rho : List RootRef} {j : Nat} (h : RootRef.param j ∈ rho) :
    Target.param j ∈ rootsTargets rho := by
  simp only [rootsTargets, List.mem_filterMap]
  exact ⟨_, h, rfl⟩

/-- A location a reference denotes may be used once the access was recorded
as an effect: it then cannot be a global that is not initialized yet. -/
theorem access {m : Module} {W : World} {env : Env} {s : Store} {l : Loc} {T : Ty}
    {rho : List RootRef} (hp : Perm m W) (hl : LocOk m W.G s l T) (hg : Gam env W.P rho l.root)
    (hin : ∀ t, t ∈ rootsTargets rho → t ∈ W.E.reads ∨ t ∈ W.E.writes ∨ t ∈ W.E.grows) :
    LocTy s l T := by
  rcases hl with hl | ⟨g, gl, hG, rfl, hgl, _⟩
  · exact hl
  · exfalso
    have hlt : g < m.globals.size := (Array.getElem?_eq_some_iff.1 hgl).1
    rcases hp with hp | ⟨_, hp⟩
    · omega
    · obtain ⟨q, hq, hr⟩ := hg
      cases q with
      | «local» y => obtain ⟨_, _, _, _, h⟩ := hr; cases h
      | global g' =>
        have hr' : RootInst.global g = RootInst.global g' := hr
        cases hr'
        have h2 : g < W.G := hp _ (hin _ (mem_rootsTargets_global hq))
        omega
      | param j =>
        have h2 : g < W.G := hp _ (hin _ (mem_rootsTargets_param hq)) _ hr g rfl
        omega

/-! ### How a store may change -/

/-- The store after a computation, seen from the code around it: typed
locations stay typed, no scope instance is handed out twice, a stored reference
outside the scope instances `insts` is kept, and no root is added. -/
structure Ext (insts : List Nat) (s s' : St) : Prop where
  le : StoreLe s.store s'.store
  next : s.nextScope ≤ s'.nextScope
  keep : ∀ (r : RootInst) (v : Val), s.store.roots[r]? = some v → IsRef v →
    (∀ a si x, r = RootInst.local a si x → si ∉ insts) → s'.store.roots[r]? = some v
  back : ∀ (r : RootInst) (v : Val), s'.store.roots[r]? = some v → IsRef v →
    (∀ a si x, r = RootInst.local a si x → si ∉ insts) → s.store.roots[r]? = some v
  dom : ∀ (r : RootInst), s'.store.roots[r]? ≠ none → s.store.roots[r]? ≠ none

def insts (env : Env) : List Nat := env.scopes.map Prod.snd

/-- A root of a variable declared in the innermost open block. -/
def TopRoot (env : Env) (r : RootInst) : Prop :=
  ∃ x lv si rest, env.scopes = (lv.scope, si) :: rest ∧ env.vars[x]? = some lv ∧
    r = .local env.act si x

/-- As `Ext`, for statements, which may declare variables of the innermost block. -/
structure ExtS (env : Env) (s s' : St) : Prop where
  le : StoreLe s.store s'.store
  next : s.nextScope ≤ s'.nextScope
  keep : ∀ (r : RootInst) (v : Val), s.store.roots[r]? = some v → IsRef v →
    (∀ a si x, r = RootInst.local a si x → si ∉ insts env) → s'.store.roots[r]? = some v
  back : ∀ (r : RootInst) (v : Val), s'.store.roots[r]? = some v → IsRef v →
    (∀ a si x, r = RootInst.local a si x → si ∉ insts env) → s.store.roots[r]? = some v
  dom : ∀ (r : RootInst), s'.store.roots[r]? ≠ none → s.store.roots[r]? ≠ none ∨ TopRoot env r

theorem Ext.refl (insts : List Nat) (s : St) : Ext insts s s :=
  ⟨StoreLe.refl _, Nat.le_refl _, fun _ _ h _ _ => h, fun _ _ h _ _ => h, fun _ h => h⟩

theorem Ext.trans {insts : List Nat} {a b c : St} (h1 : Ext insts a b) (h2 : Ext insts b c) :
    Ext insts a c :=
  ⟨h1.le.trans h2.le, Nat.le_trans h1.next h2.next,
   fun r v hv hr hn => h2.keep r v (h1.keep r v hv hr hn) hr hn,
   fun r v hv hr hn => h1.back r v (h2.back r v hv hr hn) hr hn,
   fun r h => h1.dom r (h2.dom r h)⟩

theorem Ext.toS {env : Env} {s s' : St} (h : Ext (insts env) s s') : ExtS env s s' :=
  ⟨h.le, h.next, h.keep, h.back, fun r hr => Or.inl (h.dom r hr)⟩

theorem ExtS.trans {env : Env} {a b c : St} (h1 : ExtS env a b) (h2 : ExtS env b c) :
    ExtS env a c :=
  ⟨h1.le.trans h2.le, Nat.le_trans h1.next h2.next,
   fun r v hv hr hn => h2.keep r v (h1.keep r v hv hr hn) hr hn,
   fun r v hv hr hn => h1.back r v (h2.back r v hv hr hn) hr hn,
   fun r h => (h2.dom r h).elim (fun h' => h1.dom r h') Or.inr⟩

theorem Ext.weaken {insts insts' : List Nat} {s s' : St} (h : Ext insts s s')
    (hs : ∀ i, i ∈ insts → i ∈ insts') : Ext insts' s s' :=
  ⟨h.le, h.next, fun r v hv hr hn => h.keep r v hv hr (fun a si x e hi => hn a si x e (hs si hi)),
   fun r v hv hr hn => h.back r v hv hr (fun a si x e hi => hn a si x e (hs si hi)), h.dom⟩

theorem Ext.of_flatStep {insts : List Nat} {s : St} {st' : Store} (h : FlatStep s.store st') :
    Ext insts s { s with store := st' } := by
  refine ⟨h.le, Nat.le_refl _, fun r v hv hr _ => h.keep r v hv hr, ?_, ?_⟩
  · intro r v hv hr _
    rcases h.back r v hv with h0 | ⟨hn, _⟩
    · exact h0
    · exact absurd hr hn
  · intro r hr
    cases hv : st'.roots[r]? with
    | none => exact absurd hv hr
    | some v' =>
      rcases h.back r v' hv with h0 | ⟨_, h1⟩
      · simp [h0]
      · exact h1

/-- The variables bound in the innermost scope instance are numbered in `[lo, cur)`. -/
def TopB (env : Env) (lo cur : Nat) (s : St) : Prop :=
  ∀ sc si rest, env.scopes = (sc, si) :: rest →
    ∀ x, s.store.roots[RootInst.local env.act si x]? ≠ none → lo ≤ x ∧ x < cur

theorem TopB.ext {env : Env} {lo cur cur' : Nat} {s s' : St} (h : TopB env lo cur s)
    (hd : ∀ (r : RootInst), s'.store.roots[r]? ≠ none → s.store.roots[r]? ≠ none)
    (hc : cur ≤ cur') : TopB env lo cur' s' := by
  intro sc si rest he x hx
  obtain ⟨h1, h2⟩ := h sc si rest he x (hd _ hx)
  exact ⟨h1, Nat.lt_of_lt_of_le h2 hc⟩

/-! ### The frame -/

/-- The validator's description of a point in a function body holds of the
store: every visible variable is bound in the instance of its block to a value
of its type, every reference a variable of the activation holds points into
its annotation, and the store invariant holds. -/
structure Frame (m : Module) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St) : Prop where
  mod_t : tenv.mod = m
  mod_p : penv.mod = m
  vars_t : tenv.vars = env.vars
  vars_p : penv.impl.vars = env.vars
  scopes_t : tenv.scopes = env.scopes.map Prod.fst
  scopes_p : penv.scopes = env.scopes.map Prod.fst
  nodup : (env.scopes.map Prod.fst).Nodup
  sorted : env.scopes.Pairwise (fun a b => b.2 < a.2)
  below : ∀ p, p ∈ env.scopes → W.base ≤ p.2 ∧ p.2 < s.nextScope
  base_le : W.base ≤ s.nextScope
  pAge : ∀ (i : Nat) (a : ActId) (si : ScopeInst) (x : VarId), W.P i (.local a si x) → si < W.base
  vis : ∀ x, x ∈ tenv.visible → ∃ lv si v, env.vars[x]? = some lv ∧
      env.scopes.lookup lv.scope = some si ∧ lv.ty.storable = true ∧
      s.store.roots[RootInst.local env.act si x]? = some v ∧ HasTy m W.G s.store v lv.ty
  rooted : ∀ (x : VarId) (lv : LocalVar) (si : ScopeInst) (v : Val), env.vars[x]? = some lv →
      env.scopes.lookup lv.scope = some si →
      s.store.roots[RootInst.local env.act si x]? = some v → ∀ r, Targets v r →
      ∃ ann, penv.ann x = some ann ∧ Gam env W.P ann r
  inv : StoreInv m W.G s

/-- The typing environments agree on everything a frame reads. -/
theorem Frame.tenv_congr {m : Module} {W : World} {t1 t2 : TEnv} {penv : PEnv} {env : Env} {s : St}
    (h : Frame m W t1 penv env s) (h1 : t2.mod = t1.mod) (h2 : t2.vars = t1.vars)
    (h3 : t2.scopes = t1.scopes) (h4 : ∀ x, x ∈ t2.visible → x ∈ t1.visible) :
    Frame m W t2 penv env s :=
  { h with
    mod_t := h1 ▸ h.mod_t, vars_t := h2 ▸ h.vars_t, scopes_t := h3 ▸ h.scopes_t
    vis := fun x hx => h.vis x (h4 x hx) }

theorem hasTy_step {m : Module} {G : Nat} {s s' : Store} {r : RootInst} {v : Val} {T : Ty}
    (hle : StoreLe s s') (hkeep : IsRef v → s'.roots[r]? = some v) (hT : T.storable = true)
    (hv : s.roots[r]? = some v) (ht : HasTy m G s v T) :
    ∃ v', s'.roots[r]? = some v' ∧ HasTy m G s' v' T := by
  cases T <;> simp only [Ty.storable] at hT <;> try cases hT
  case int t => simp only [HasTy] at ht ⊢; exact flat_mono hle hv ht
  case bool => simp only [HasTy] at ht ⊢; exact flat_mono hle hv ht
  case arr E k => simp only [HasTy] at ht ⊢; exact flat_mono hle hv ht
  case grow E => simp only [HasTy] at ht ⊢; exact flat_mono hle hv ht
  case ref mu T =>
    refine ⟨v, hkeep ?_, ht.mono hle⟩
    obtain ⟨l, rfl, _⟩ := ht; trivial
  case slice mu E =>
    refine ⟨v, hkeep ?_, ht.mono hle⟩
    obtain ⟨l, st, n, rfl, _⟩ := ht; trivial

theorem Frame.flatStep {m : Module} {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}
    {st' : Store} (h : Frame m W tenv penv env s) (hs : FlatStep s.store st') :
    Frame m W tenv penv env { s with store := st' } :=
  { h with
    below := h.below, base_le := h.base_le
    vis := by
      intro x hx
      obtain ⟨lv, si, v, h1, h2, h3, h4, h5⟩ := h.vis x hx
      obtain ⟨v', h6, h7⟩ := hasTy_step hs.le (hs.keep _ v h4) h3 h4 h5
      exact ⟨lv, si, v', h1, h2, h3, h6, h7⟩
    rooted := by
      intro x lv si v h1 h2 h3 r ht
      rcases hs.back _ v h3 with h0 | ⟨hn, _⟩
      · exact h.rooted x lv si v h1 h2 h0 r ht
      · exact absurd ht.isRef hn
    inv := h.inv.flatStep hs }

end Goose.Core.Sound
