import Goose.Core.Sound.Store

/-!
The invariant of one activation: how the validator's view of a function body
(visible variables, open scopes, root annotations) describes the store while
the body runs.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

/-- Pilot evaluation preserves existing locations and sampled runs because
its accepted operations write and grow without removing elements. -/
def PilotStoreLe (m : Module) (s s' : St) : Prop :=
  m.profile = .pilot → StoreLe s.store s'.store

/-- What is fixed while one function body, or one global initializer, runs:
how many globals are initialized, which roots each parameter's argument may
point into, the effects the body is allowed, and a scope instance below which
every root of a caller lies. -/
structure World where
  G : Nat
  P : Nat → RootInst → Prop
  /-- Parameter roots authorized by references to resizable owner storage. -/
  ownerP : Nat → RootInst → Prop
  E : Eff
  base : Nat
  /-- The slice variables of callers this activation was given a reference
  to, with their element types. Their slices may be replaced from here. -/
  D : RootInst → Ty → Prop
  /-- The roots a slice stored in such a variable may point into. -/
  A : RootInst → RootInst → Prop

def Dset (W : World) : RootInst → Prop := fun r => ∃ E, W.D r E

/-- The root instance a static root denotes in an activation. -/
def RootIn (env : Env) (P : Nat → RootInst → Prop) (r : RootInst) : RootRef → Prop
  | .local y => ∃ lv si, env.vars[y]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
      r = .local env.act si y
  | .global g => r = .global g
  | .param j => P j r

/-- The root instances a static root set denotes. -/
def Gam (env : Env) (P : Nat → RootInst → Prop) (rho : List RootRef) (r : RootInst) : Prop :=
  ∃ q, q ∈ rho ∧ RootIn env P r q

/-- References that can name resizable owner storage. Limited storage and
slice headers do not grant this authority. -/
def OwnerRefTy (T : Ty) : Prop :=
  ∃ mu el, T = .ref mu (.grow el) ∨ T = .ref mu (.growshrink el)

/-- A parameter slot whose declared reference type grants owner authority. -/
def OwnerRefParam (impl : Impl) (i : Nat) : Prop :=
  ∃ p lv, impl.params[i]? = some p ∧ p.mode = .byRef ∧
    impl.vars[p.var]? = some lv ∧ OwnerRefTy lv.ty

/-- Parameter owner authority is empty outside owner reference slots. -/
def OwnerParameterShape (impl : Impl) (ownerP : Nat → RootInst → Prop) : Prop :=
  ∀ i r, ownerP i r → OwnerRefParam impl i

/-- Owner reference outputs use owner authority for their target annotations. -/
def OwnerRooted (env : Env) (ownerP : Nat → RootInst → Prop)
    (roots : List RootRef) (v : Val) (T : Ty) : Prop :=
  OwnerRefTy T → ∀ r, Targets v r → Gam env ownerP roots r

theorem Gam.mono {env : Env} {P P' : Nat → RootInst → Prop}
    {rho : List RootRef} {r : RootInst}
    (h : Gam env P rho r) (hP : ∀ i r, P i r → P' i r) : Gam env P' rho r := by
  obtain ⟨q, hq, hr⟩ := h
  refine ⟨q, hq, ?_⟩
  cases q with
  | «local» _ => exact hr
  | global _ => exact hr
  | param i => exact hP i r hr

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

/-- Roots a computation may change from its entry state: the static roots it
names, together with local roots allocated after the entry scope counter. -/
def MutationRoots (env : Env) (P : Nat → RootInst → Prop) (base : Nat)
    (roots : List RootRef) (r : RootInst) : Prop :=
  Gam env P roots r ∨ ∃ act si x, r = .local act si x ∧ base ≤ si

/-- A computation with this footprint leaves every other stored root exact. -/
def MutationFootprint (env : Env) (P : Nat → RootInst → Prop) (base : Nat)
    (roots : List RootRef) (s s' : St) : Prop :=
  StoreLeExcept (MutationRoots env P base roots) s.store s'.store

theorem MutationFootprint.refl (env : Env) (P : Nat → RootInst → Prop)
    (base : Nat) (roots : List RootRef) (s : St) :
    MutationFootprint env P base roots s s :=
  fun _ _ => rfl

theorem MutationFootprint.trans {env : Env} {P : Nat → RootInst → Prop}
    {base : Nat} {roots : List RootRef} {s₀ s₁ s₂ : St}
    (h₁ : MutationFootprint env P base roots s₀ s₁)
    (h₂ : MutationFootprint env P base roots s₁ s₂) :
    MutationFootprint env P base roots s₀ s₂ :=
  StoreLeExcept.trans h₁ h₂

theorem MutationFootprint.weaken {env : Env} {P : Nat → RootInst → Prop}
    {base : Nat} {roots roots' : List RootRef} {s s' : St}
    (h : MutationFootprint env P base roots s s')
    (hsubset : ∀ q, q ∈ roots → q ∈ roots') :
    MutationFootprint env P base roots' s s' := by
  intro r hnot
  apply h r
  intro hchanged
  rcases hchanged with ⟨q, hq, hroot⟩ | ⟨act, si, x, heq, hage⟩
  · exact hnot (Or.inl ⟨q, hsubset q hq, hroot⟩)
  · exact hnot (Or.inr ⟨act, si, x, heq, hage⟩)

theorem MutationFootprint.trans_union {env : Env} {P : Nat → RootInst → Prop}
    {base : Nat} {roots₁ roots₂ : List RootRef} {s₀ s₁ s₂ : St}
    (h₁ : MutationFootprint env P base roots₁ s₀ s₁)
    (h₂ : MutationFootprint env P base roots₂ s₁ s₂) :
    MutationFootprint env P base (unionRoots roots₁ roots₂) s₀ s₂ := by
  intro r hnot
  rw [h₂ r (by
    intro h
    apply hnot
    rcases h with ⟨q, hq, hroot⟩ | ⟨act, si, x, heq, hage⟩
    · exact Or.inl ⟨q, unionRoots_right roots₁ roots₂ q hq, hroot⟩
    · exact Or.inr ⟨act, si, x, heq, hage⟩)]
  rw [h₁ r (by
    intro h
    apply hnot
    rcases h with ⟨q, hq, hroot⟩ | ⟨act, si, x, heq, hage⟩
    · exact Or.inl ⟨q, unionRoots_left roots₁ roots₂ q hq, hroot⟩
    · exact Or.inr ⟨act, si, x, heq, hage⟩)]

theorem MutationFootprint.root_eq {env : Env} {P : Nat → RootInst → Prop}
    {base : Nat} {roots : List RootRef} {s s' : St} {r : RootInst}
    (footprint : MutationFootprint env P base roots s s')
    (outside : ¬ MutationRoots env P base roots r) :
    s'.store.roots[r]? = s.store.roots[r]? :=
  footprint r outside

/-! ### Effects an activation may have -/

def TargetOk (G : Nat) (P : Nat → RootInst → Prop) : Target → Prop
  | .global g => g < G
  | .param j => ∀ r, P j r → ∀ g, r = .global g → g < G

def EffOk (G : Nat) (P : Nat → RootInst → Prop) (E : Eff) : Prop :=
  E.unknown = false ∧
    ∀ t, (t ∈ E.reads ∨ t ∈ E.writes ∨ t ∈ E.grows ∨ t ∈ E.shrinks) → TargetOk G P t

/-- Either every global is initialized, or the body's allowed effects touch
only initialized ones. -/
def Perm (m : Module) (W : World) : Prop := m.globals.size ≤ W.G ∨ EffOk W.G W.P W.E

def EffLe (a b : Eff) : Prop :=
  (∀ t, t ∈ a.reads → t ∈ b.reads) ∧ (∀ t, t ∈ a.writes → t ∈ b.writes) ∧
  (∀ t, t ∈ a.grows → t ∈ b.grows) ∧ (∀ t, t ∈ a.shrinks → t ∈ b.shrinks) ∧
  (a.unknown = true → b.unknown = true)

theorem EffLe.refl (a : Eff) : EffLe a a :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h, fun h => h⟩

theorem EffLe.trans {a b c : Eff} (h1 : EffLe a b) (h2 : EffLe b c) : EffLe a c :=
  ⟨fun t h => h2.1 t (h1.1 t h), fun t h => h2.2.1 t (h1.2.1 t h),
   fun t h => h2.2.2.1 t (h1.2.2.1 t h),
   fun t h => h2.2.2.2.1 t (h1.2.2.2.1 t h),
   fun h => h2.2.2.2.2 (h1.2.2.2.2 h)⟩

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
    (hin : ∀ t, t ∈ rootsTargets rho →
      t ∈ W.E.reads ∨ t ∈ W.E.writes ∨ t ∈ W.E.grows ∨ t ∈ W.E.shrinks) :
    LocTy s l T := by
  rcases hl with hl | ⟨g, gl, hG, hroot, hgl, _⟩
  · exact hl
  · exfalso
    rw [hroot] at hg
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
structure Ext (insts : List Nat) (D : RootInst → Prop) (s s' : St) : Prop where
  le : StoreLe s.store s'.store
  next : s.nextScope ≤ s'.nextScope
  keep : ∀ (r : RootInst) (v : Val), s.store.roots[r]? = some v → IsRef v →
    (∀ a si x, r = RootInst.local a si x → si ∉ insts) → ¬ D r → s'.store.roots[r]? = some v
  back : ∀ (r : RootInst) (v : Val), s'.store.roots[r]? = some v → IsRef v →
    (∀ a si x, r = RootInst.local a si x → si ∉ insts) → ¬ D r → s.store.roots[r]? = some v
  dom : ∀ (r : RootInst), s'.store.roots[r]? ≠ none → s.store.roots[r]? ≠ none

def insts (env : Env) : List Nat := env.scopes.map Prod.snd

/-- A root of a variable declared in the innermost open block. -/
def TopRoot (env : Env) (r : RootInst) : Prop :=
  ∃ x lv si rest, env.scopes = (lv.scope, si) :: rest ∧ env.vars[x]? = some lv ∧
    r = .local env.act si x

/-- As `Ext`, for statements, which may declare variables of the innermost block. -/
structure ExtS (env : Env) (D : RootInst → Prop) (s s' : St) : Prop where
  le : StoreLe s.store s'.store
  next : s.nextScope ≤ s'.nextScope
  keep : ∀ (r : RootInst) (v : Val), s.store.roots[r]? = some v → IsRef v →
    (∀ a si x, r = RootInst.local a si x → si ∉ insts env) → ¬ D r → s'.store.roots[r]? = some v
  back : ∀ (r : RootInst) (v : Val), s'.store.roots[r]? = some v → IsRef v →
    (∀ a si x, r = RootInst.local a si x → si ∉ insts env) → ¬ D r → s.store.roots[r]? = some v
  dom : ∀ (r : RootInst), s'.store.roots[r]? ≠ none → s.store.roots[r]? ≠ none ∨ TopRoot env r

/-- The scope and root footprint of an execution, without asserting that typed
locations survive changes to the store. -/
structure Footprint (insts : List Nat) (D : RootInst → Prop) (s s' : St) : Prop where
  next : s.nextScope ≤ s'.nextScope
  keep : ∀ (r : RootInst) (v : Val), s.store.roots[r]? = some v → IsRef v →
    (∀ a si x, r = RootInst.local a si x → si ∉ insts) → ¬ D r → s'.store.roots[r]? = some v
  back : ∀ (r : RootInst) (v : Val), s'.store.roots[r]? = some v → IsRef v →
    (∀ a si x, r = RootInst.local a si x → si ∉ insts) → ¬ D r → s.store.roots[r]? = some v
  dom : ∀ (r : RootInst), s'.store.roots[r]? ≠ none → s.store.roots[r]? ≠ none

/-- The statement footprint also permits roots for variables declared in the
innermost open block. -/
structure FootprintS (env : Env) (D : RootInst → Prop) (s s' : St) : Prop where
  next : s.nextScope ≤ s'.nextScope
  keep : ∀ (r : RootInst) (v : Val), s.store.roots[r]? = some v → IsRef v →
    (∀ a si x, r = RootInst.local a si x → si ∉ insts env) → ¬ D r → s'.store.roots[r]? = some v
  back : ∀ (r : RootInst) (v : Val), s'.store.roots[r]? = some v → IsRef v →
    (∀ a si x, r = RootInst.local a si x → si ∉ insts env) → ¬ D r → s.store.roots[r]? = some v
  dom : ∀ (r : RootInst), s'.store.roots[r]? ≠ none → s.store.roots[r]? ≠ none ∨ TopRoot env r

theorem Footprint.refl (insts : List Nat) (D : RootInst → Prop) (s : St) : Footprint insts D s s :=
  ⟨Nat.le_refl _, fun _ _ h _ _ _ => h, fun _ _ h _ _ _ => h, fun _ h => h⟩

theorem Footprint.trans {insts : List Nat} {D : RootInst → Prop} {a b c : St}
    (h1 : Footprint insts D a b) (h2 : Footprint insts D b c) : Footprint insts D a c :=
  ⟨Nat.le_trans h1.next h2.next,
   fun r v hv hr hn hd => h2.keep r v (h1.keep r v hv hr hn hd) hr hn hd,
   fun r v hv hr hn hd => h1.back r v (h2.back r v hv hr hn hd) hr hn hd,
   fun r h => h1.dom r (h2.dom r h)⟩

theorem Footprint.toS {env : Env} {D : RootInst → Prop} {s s' : St}
    (h : Footprint (insts env) D s s') : FootprintS env D s s' :=
  ⟨h.next, h.keep, h.back, fun r hr => Or.inl (h.dom r hr)⟩

theorem FootprintS.refl (env : Env) (D : RootInst → Prop) (s : St) : FootprintS env D s s :=
  ⟨Nat.le_refl _, fun _ _ h _ _ _ => h, fun _ _ h _ _ _ => h, fun _ h => Or.inl h⟩

theorem FootprintS.trans {env : Env} {D : RootInst → Prop} {a b c : St}
    (h1 : FootprintS env D a b) (h2 : FootprintS env D b c) : FootprintS env D a c :=
  ⟨Nat.le_trans h1.next h2.next,
   fun r v hv hr hn hd => h2.keep r v (h1.keep r v hv hr hn hd) hr hn hd,
   fun r v hv hr hn hd => h1.back r v (h2.back r v hv hr hn hd) hr hn hd,
   fun r h => (h2.dom r h).elim (fun h' => h1.dom r h') Or.inr⟩

theorem Ext.refl (insts : List Nat) (D : RootInst → Prop) (s : St) : Ext insts D s s :=
  ⟨StoreLe.refl _, Nat.le_refl _, fun _ _ h _ _ _ => h, fun _ _ h _ _ _ => h, fun _ h => h⟩

theorem Ext.toFootprint {insts : List Nat} {D : RootInst → Prop} {s s' : St}
    (h : Ext insts D s s') : Footprint insts D s s' :=
  ⟨h.next, h.keep, h.back, h.dom⟩

theorem ExtS.toFootprintS {env : Env} {D : RootInst → Prop} {s s' : St}
    (h : ExtS env D s s') : FootprintS env D s s' :=
  ⟨h.next, h.keep, h.back, h.dom⟩

theorem Ext.trans {insts : List Nat} {D : RootInst → Prop} {a b c : St} (h1 : Ext insts D a b)
    (h2 : Ext insts D b c) : Ext insts D a c :=
  ⟨h1.le.trans h2.le, Nat.le_trans h1.next h2.next,
   fun r v hv hr hn hd => h2.keep r v (h1.keep r v hv hr hn hd) hr hn hd,
   fun r v hv hr hn hd => h1.back r v (h2.back r v hv hr hn hd) hr hn hd,
   fun r h => h1.dom r (h2.dom r h)⟩

theorem Ext.toS {env : Env} {D : RootInst → Prop} {s s' : St} (h : Ext (insts env) D s s') :
    ExtS env D s s' :=
  ⟨h.le, h.next, h.keep, h.back, fun r hr => Or.inl (h.dom r hr)⟩

theorem ExtS.trans {env : Env} {D : RootInst → Prop} {a b c : St} (h1 : ExtS env D a b)
    (h2 : ExtS env D b c) : ExtS env D a c :=
  ⟨h1.le.trans h2.le, Nat.le_trans h1.next h2.next,
   fun r v hv hr hn hd => h2.keep r v (h1.keep r v hv hr hn hd) hr hn hd,
   fun r v hv hr hn hd => h1.back r v (h2.back r v hv hr hn hd) hr hn hd,
   fun r h => (h2.dom r h).elim (fun h' => h1.dom r h') Or.inr⟩

/-- A computation that left more roots alone also left fewer alone. -/
theorem Ext.weaken {insts insts' : List Nat} {D D' : RootInst → Prop} {s s' : St}
    (h : Ext insts D s s')
    (hs : ∀ (r : RootInst), ¬ D' r → (∀ a si x, r = RootInst.local a si x → si ∉ insts') →
      ¬ D r ∧ ∀ a si x, r = RootInst.local a si x → si ∉ insts) : Ext insts' D' s s' :=
  ⟨h.le, h.next,
   fun r v hv hr hn hd => h.keep r v hv hr (hs r hd hn).2 (hs r hd hn).1,
   fun r v hv hr hn hd => h.back r v hv hr (hs r hd hn).2 (hs r hd hn).1, h.dom⟩

/-- A computation that left more roots alone also left fewer alone. -/
theorem Footprint.weaken {insts insts' : List Nat} {D D' : RootInst → Prop} {s s' : St}
    (h : Footprint insts D s s')
    (hs : ∀ (r : RootInst), ¬ D' r → (∀ a si x, r = RootInst.local a si x → si ∉ insts') →
      ¬ D r ∧ ∀ a si x, r = RootInst.local a si x → si ∉ insts) : Footprint insts' D' s s' :=
  ⟨h.next,
   fun r v hv hr hn hd => h.keep r v hv hr (hs r hd hn).2 (hs r hd hn).1,
   fun r v hv hr hn hd => h.back r v hv hr (hs r hd hn).2 (hs r hd hn).1,
   h.dom⟩

theorem Ext.of_flatStep {insts : List Nat} {D : RootInst → Prop} {s : St} {st' : Store}
    (h : FlatStep s.store st') : Ext insts D s { s with store := st' } := by
  refine ⟨h.le, Nat.le_refl _, fun r v hv hr _ _ => h.keep r v hv hr, ?_, ?_⟩
  · intro r v hv hr _ _
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

theorem Footprint.of_flatStep {insts : List Nat} {D : RootInst → Prop} {s : St} {st' : Store}
    (h : FlatStep s.store st') : Footprint insts D s { s with store := st' } := by
  refine ⟨Nat.le_refl _, fun r v hv hr _ _ => h.keep r v hv hr, ?_, ?_⟩
  · intro r v hv hr _ _
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

/-- What a parameter that refers to a slice variable is known to point at:
a slice variable of a caller, whose slices are rooted exactly within the
parameter's content roots. -/
def PRef (P : Nat → RootInst → Prop) (D : RootInst → Ty → Prop) (A : RootInst → RootInst → Prop)
    (penv : PEnv) (vars : Array LocalVar) (x : VarId) (cont : List RootRef) : Prop :=
  (∀ y, RootRef.local y ∉ cont) ∧ penv.ann x = some [.param x] ∧
  ∀ (lv : LocalVar) (mu mu' : Mutability) (E : Ty), vars[x]? = some lv →
    lv.ty = .ref mu (.slice mu' E) → ∀ r, P x r →
    D r E ∧ (∀ t, A r t → Gam noEnv P cont t) ∧ (∀ t, Gam noEnv P cont t → A r t)

/-- Declared types of non-reference local storage slots, including locals
outside the visible continuation. -/
def StorageRootTypes (env : Env) (r : RootInst) (T : Ty) : Prop :=
  ∃ x lv si, env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
    r = RootInst.local env.act si x ∧ lv.ty.isRefLike = false ∧ T = lv.ty

/-- The validator's description of a point in a function body holds of the
store: every visible variable is bound in the instance of its block to a value
of its type, every reference a variable of the activation holds points into
its annotation, and the store invariant holds. -/
structure Frame (m : Module) (W : World) (tenv : TEnv) (penv : PEnv) (env : Env) (s : St)
    (future : List VarId := tenv.visible) : Prop where
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
  ownerSubset : ∀ i r, W.ownerP i r → W.P i r
  ownerShape : OwnerParameterShape penv.impl W.ownerP
  pAge : ∀ (i : Nat) (a : ActId) (si : ScopeInst) (x : VarId), W.P i (.local a si x) → si < W.base
  vis : ∀ x, x ∈ tenv.visible → x ∈ future → ∃ lv si v, env.vars[x]? = some lv ∧
      env.scopes.lookup lv.scope = some si ∧ lv.ty.paramOk = true ∧
      s.store.roots[RootInst.local env.act si x]? = some v ∧ HasTy m W.G s.store v lv.ty
  /-- Every visible binding stays present, even after it leaves the demanded continuation. -/
  bindings : ∀ x, x ∈ tenv.visible → ∃ lv si v, env.vars[x]? = some lv ∧
      env.scopes.lookup lv.scope = some si ∧ lv.ty.paramOk = true ∧
      s.store.roots[RootInst.local env.act si x]? = some v ∧
      (lv.ty.isRefLike = true → IsRef v)
  storage : ∀ r T, StorageRootTypes env r T → ∀ v,
      s.store.roots[r]? = some v → LocTy s.store ⟨r, []⟩ T
  rooted : ∀ (x : VarId) (lv : LocalVar) (si : ScopeInst) (v : Val), env.vars[x]? = some lv →
      env.scopes.lookup lv.scope = some si →
      s.store.roots[RootInst.local env.act si x]? = some v → ∀ r, Targets v r →
      ∃ ann, penv.ann x = some ann ∧ Gam env W.P ann r
  /-- Stored owner references retain authority even outside the continuation. -/
  rootedOwners : ∀ (x : VarId) (lv : LocalVar) (si : ScopeInst) (v : Val),
      env.vars[x]? = some lv → env.scopes.lookup lv.scope = some si →
      s.store.roots[RootInst.local env.act si x]? = some v → OwnerRefTy lv.ty →
      ∀ r, Targets v r → ∃ ann, penv.ann x = some ann ∧ Gam env W.ownerP ann r
  inv : StoreInvAt m W.G env tenv.visible future s
  aOlder : ∀ r t, W.A r t → Older t r
  dOut : ∀ r E, W.D r E → ∃ a si x, r = RootInst.local a si x ∧ si < W.base
  dFun : ∀ r E E', W.D r E → W.D r E' → E = E'
  sa : ∀ r E, W.D r E → ∃ v, s.store.roots[r]? = some v ∧
      HasTy m W.G s.store v (.slice .mutable E) ∧ ∀ t, Targets v t → W.A r t
  pref : ∀ x cont, penv.cont x = some cont → PRef W.P W.D W.A penv env.vars x cont

/-- The typing environments agree on everything a frame reads. -/
theorem Frame.tenv_congr {m : Module} {W : World} {t1 t2 : TEnv} {penv : PEnv} {env : Env} {s : St}
    {future : List VarId} (h : Frame m W t1 penv env s future)
    (h1 : t2.mod = t1.mod) (h2 : t2.vars = t1.vars)
    (h3 : t2.scopes = t1.scopes) (h4 : ∀ x, x ∈ t2.visible → x ∈ t1.visible) :
    Frame m W t2 penv env s future :=
  { h with
    mod_t := h1 ▸ h.mod_t, vars_t := h2 ▸ h.vars_t, scopes_t := h3 ▸ h.scopes_t
    vis := fun x hx hfuture => h.vis x (h4 x hx) hfuture
    bindings := fun x hx => h.bindings x (h4 x hx)
    inv := h.inv.changeDemand (by
      intro r hr
      cases r with
      | global g => exact Or.inl trivial
      | «local» a si x =>
        rcases hr with ⟨ha, hx, hf, lv, hvar, hlk⟩
        exact Or.inl ⟨ha, h4 x hx, hf, lv, hvar, hlk⟩) }

theorem hasTy_step {m : Module} {G : Nat} {s s' : Store} {r : RootInst} {v : Val} {T : Ty}
    (hle : StoreLe s s') (hkeep : IsRef v → s'.roots[r]? = some v) (hT : T.paramOk = true)
    (hv : s.roots[r]? = some v) (ht : HasTy m G s v T) :
    ∃ v', s'.roots[r]? = some v' ∧ HasTy m G s' v' T := by
  cases T <;> simp only [Ty.paramOk, Ty.storable, Ty.isRefSlice, Bool.or_false, Bool.false_or,
    reduceCtorEq] at hT
  case int t => simp only [HasTy] at ht ⊢; exact flat_mono hle hv ht
  case bool => simp only [HasTy] at ht ⊢; exact flat_mono hle hv ht
  case arr E k => simp only [HasTy] at ht ⊢; exact flat_mono hle hv ht
  case grow E => simp only [HasTy] at ht ⊢; exact flat_mono hle hv ht
  case growshrink E => simp only [HasTy] at ht ⊢; exact flat_mono hle hv ht
  case limited E capacity => simp only [HasTy] at ht ⊢; exact flat_mono hle hv ht
  case structT sid ts => simp only [HasTy] at ht ⊢; exact flat_mono hle hv ht
  case ref mu T =>
    refine ⟨v, hkeep ?_, ht.mono hle⟩
    obtain ⟨l, rfl, _⟩ := ht; trivial
  case slice mu E =>
    refine ⟨v, hkeep ?_, ht.mono hle⟩
    obtain ⟨l, st, n, rfl, _⟩ := ht; trivial

theorem Frame.flatStep {m : Module} {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}
    {future : List VarId} {st' : Store} (h : Frame m W tenv penv env s future) (hs : FlatStep s.store st') :
    Frame m W tenv penv env { s with store := st' } future :=
  { h with
    below := h.below, base_le := h.base_le
    vis := by
      intro x hx
      intro hfuture
      obtain ⟨lv, si, v, h1, h2, h3, h4, h5⟩ := h.vis x hx hfuture
      obtain ⟨v', h6, h7⟩ := hasTy_step hs.le (hs.keep _ v h4) h3 h4 h5
      exact ⟨lv, si, v', h1, h2, h3, h6, h7⟩
    bindings := by
      intro x hx
      obtain ⟨lv, si, old, h1, h2, h3, hroot, hold⟩ := h.bindings x hx
      have hpresent : st'.roots[RootInst.local env.act si x]? ≠ none :=
        dom_mono hs.le (by rw [hroot]; simp)
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hpresent
      refine ⟨lv, si, v, h1, h2, h3, hv, ?_⟩
      intro href
      have hkeep := hs.keep _ old hroot (hold href)
      rw [hv] at hkeep
      cases hkeep
      exact hold href
    rooted := by
      intro x lv si v h1 h2 h3 r ht
      rcases hs.back _ v h3 with h0 | ⟨hn, _⟩
      · exact h.rooted x lv si v h1 h2 h0 r ht
      · exact absurd ht.isRef hn
    rootedOwners := by
      intro x lv si v h1 h2 h3 howner r ht
      rcases hs.back _ v h3 with h0 | ⟨hn, _⟩
      · exact h.rootedOwners x lv si v h1 h2 h0 howner r ht
      · exact absurd ht.isRef hn
    storage := by
      intro r T hstorage v' hpost
      cases hroot : s.store.roots[r]? with
      | some old => exact (h.storage r T hstorage old hroot).mono hs.le
      | none =>
          rcases hs.back r v' hpost with hsame | ⟨_, hdom⟩
          · rw [hroot] at hsame
            cases hsame
          · exact False.elim (hdom hroot)
    inv := h.inv.flatStep hs
    sa := by
      intro r E hd
      obtain ⟨v, h1, h2, h3⟩ := h.sa r E hd
      obtain ⟨l, a, b, rfl, _⟩ := h2
      exact ⟨_, hs.keep r _ h1 trivial, HasTy.mono hs.le ⟨l, a, b, rfl, by assumption⟩, h3⟩ }

/-- Change a frame's future when every newly demanded visible variable was already framed. -/
theorem Frame.changeFuture {m : Module} {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future future' : List VarId}
    (h : Frame m W tenv penv env s future)
    (hsub : ∀ x, x ∈ tenv.visible → x ∈ future' → x ∈ future) :
    Frame m W tenv penv env s future' := by
  refine { h with
    vis := ?_
    inv := ?_ }
  · intro x hx hfut
    exact h.vis x hx (hsub x hx hfut)
  · apply h.inv.changeDemand
    intro r hdem
    cases r with
    | global g => exact Or.inl trivial
    | «local» a si x =>
      rcases hdem with ⟨ha, hx, hfut, lv, hvar, hlk⟩
      exact Or.inl ⟨ha, hx, hsub x hx hfut, lv, hvar, hlk⟩

/-- Narrow a frame to variables that remain demanded at the next syntax point. -/
theorem Frame.narrowFuture {m : Module} {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future future' : List VarId}
    (h : Frame m W tenv penv env s future)
    (hsub : ∀ x, x ∈ future' → x ∈ future) :
    Frame m W tenv penv env s future' :=
  h.changeFuture (fun _ _ hfut => hsub _ hfut)

/-- Once a node has finished, only its caller's future remains demanded. -/
theorem Frame.afterNode {m : Module} {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future current : List VarId}
    (h : Frame m W tenv penv env s (future ++ current)) :
    Frame m W tenv penv env s future :=
  h.narrowFuture (fun _ hx => List.mem_append_left _ hx)

/-- Reordering or duplicating future variables does not change a frame. -/
theorem Frame.future_congr {m : Module} {W : World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {s : St} {future future' : List VarId}
    (h : Frame m W tenv penv env s future)
    (heq : ∀ x, x ∈ future' ↔ x ∈ future) :
    Frame m W tenv penv env s future' :=
  h.narrowFuture (fun x hx => (heq x).1 hx)

end Goose.Core.Sound
