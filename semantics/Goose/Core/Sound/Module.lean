import Goose.Core.Sound.Spec

/-!
What `validate` establishes about each item of an accepted module.
-/

namespace Goose.Core.Sound
open Goose.Core

/-- The module type-table check covers every local type in every implementation. -/
theorem checkStructTables_impl_var_ok (m : Module) (h : checkStructTables m = .ok ())
    {i : Nat} {impl : Impl} {x : VarId} {lv : LocalVar}
    (hi : m.impls[i]? = some impl) (hv : impl.vars[x]? = some lv) :
    checkResolvedType m lv.ty = .ok () := by
  unfold checkStructTables at h
  inv at h
  obtain ⟨_, _, _, _, himpls⟩ := h
  have himpl := (forAll_ok _ _).1 himpls impl
    (Array.mem_toList_iff.2 (Array.mem_of_getElem? hi))
  obtain ⟨_, hvars, _⟩ := (ex_bind_ok _ _ _).1 himpl
  exact (forAll_ok _ _).1 hvars lv
    (Array.mem_toList_iff.2 (Array.mem_of_getElem? hv))

theorem checkEntry_ok (m : Module) (h : checkEntry m = .ok ()) :
    ∃ ctx impl, m.contexts[m.entry]? = some ctx ∧ m.impls[ctx.impl]? = some impl ∧
      impl.params.size = 0 ∧ impl.results.toList = [] := by
  unfold checkEntry at h
  cases hc : m.contexts[m.entry]? with
  | none => simp only [hc] at h; inv at h
  | some ctx =>
    cases hi : m.impls[ctx.impl]? with
    | none => simp only [hc, hi] at h; inv at h
    | some impl =>
      simp only [hc, hi] at h; inv at h
      simp only [Bool.and_eq_true, Array.isEmpty_iff_size_eq_zero] at h
      refine ⟨ctx, impl, rfl, hi, h.1, ?_⟩
      have := h.2
      exact Array.toList_eq_nil_iff.2 (Array.eq_empty_of_size_eq_zero this)

theorem checkParam_ok (impl : Impl) (i : Nat) (p : Param) (h : checkParam impl i = .ok ())
    (hp : impl.params[i]? = some p) :
    p.var = i ∧ ∃ lv : LocalVar, impl.vars[i]? = some lv ∧ lv.scope = 0 ∧ lv.ty.paramOk = true := by
  unfold checkParam at h
  simp only [hp] at h
  cases hv : impl.vars[i]? with
  | none => simp only [hv] at h; inv at h
  | some lv =>
    simp only [hv] at h; inv at h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, lv, rfl, h2, ?_⟩
    cases hm : p.mode <;> cases hty : lv.ty <;> simp only [hm, hty] at h3 <;> inv at h3 <;>
      first
        | (simp_all [Ty.paramOk, Ty.storable, Ty.isRefSlice, Ty.isSlice]; done)
        | (rename_i tgt
           cases tgt <;> simp_all [Ty.paramOk, Ty.storable, Ty.isRefSlice, Ty.isSlice, Ty.refTarget])

theorem checkImpl_ok (m : Module) (impl : Impl) (h : checkImpl m impl = .ok ()) : ImplOk m impl := by
  unfold checkImpl at h
  cases hscope : scopeOrderError (blockScopes none impl.body) 0 with
  | some message =>
    simp only [hscope] at h
    inv at h
  | none =>
    simp only [hscope] at h
    inv at h
    obtain ⟨_, _, hpar, _, hsc, _, bodyTy, tn, htb, hres⟩ := h
    refine ⟨?_, hsc, bodyTy, tn, htb, ?_⟩
    · intro i p hp
      have hlt : i < impl.params.size := (Array.getElem?_eq_some_iff.1 hp).1
      exact checkParam_ok impl i p ((forAll_ok _ _).1 hpar i (List.mem_range.2 hlt)) hp
    · rcases hr : impl.results.toList with _ | ⟨t, _ | _⟩ <;> simp only [hr] at hres <;> inv at hres
      · exact Or.inl ⟨rfl, by simpa using hres⟩
      · refine Or.inr ⟨t, rfl, ?_, ?_⟩
        · intro hs
          rcases hres with ⟨_, h2⟩ | ⟨h1, _⟩
          · simpa using h2
          · exact absurd hs h1
        · intro hs
          rcases hres with ⟨h1, _⟩ | ⟨_, h2⟩
          · rw [hs] at h1; cases h1
          · exact h2

theorem checkGlobal_ok (m : Module) (g : GlobalId) (gl : Global) (h : checkGlobal m g gl = .ok ()) :
    (gl.ty.storable = true ∧ gl.ty.isRefLike = false) ∧
    ∃ tn, tyExpr (initEnv m g) gl.init 0 = .ok (gl.ty, tn) := by
  unfold checkGlobal at h
  cases hscope : scopeOrderError (exprScopes none gl.init) 0 with
  | some message =>
    simp only [hscope] at h
    inv at h
  | none =>
    simp only [hscope] at h
    inv at h
    obtain ⟨hty, _, t, tn, hte, howner⟩ := h
    obtain ⟨_, _, hbeq⟩ := howner
    have : t = gl.ty := eq_of_beq hbeq
    subst this
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hty
    exact ⟨hty, tn, hte⟩

theorem checkInitRoots_ok (m : Module) (g : GlobalId) (gl : Global) (hg : m.globals[g]? = some gl)
    (h : checkInitRoots m g = .ok ()) :
    ∃ rho st, rpExpr ⟨m, initImpl, initContext, []⟩ gl.init ⟨0, {}⟩ = .ok (rho, st) ∧
      st.eff.unknown = false ∧
      ∀ t : Target,
        (t ∈ st.eff.reads ∨ t ∈ st.eff.writes ∨ t ∈ st.eff.grows ∨ t ∈ st.eff.shrinks) →
        ∀ h, t = .global h → h < g := by
  unfold checkInitRoots at h
  simp only [hg] at h
  inv at h
  obtain ⟨rho, st, hre, hu, hall⟩ := h
  refine ⟨rho, st, hre, by simpa using hu, ?_⟩
  intro t ht k hk
  subst hk
  have hmem : Target.global k ∈ st.eff.reads ++ st.eff.writes ++ st.eff.grows ++ st.eff.shrinks := by
    simp only [List.mem_append]
    rcases ht with h | h | h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have := (forAll_ok _ _).1 hall _ hmem
  simp only at this
  inv at this
  exact this

theorem checkContext_ok (m : Module) (ctx : Context) (h : checkContext m ctx = .ok ()) :
    ∃ impl, m.impls[ctx.impl]? = some impl ∧ CtxOk m impl ctx := by
  unfold checkContext at h
  cases hi : m.impls[ctx.impl]? with
  | none => simp only [hi] at h; inv at h
  | some impl =>
    simp only [hi] at h; inv at h
    obtain ⟨hann, hrs, hcont, st, ⟨rho, a, b, s1, hrb, hck⟩, hcs⟩ := h
    refine ⟨impl, rfl, ?_, ?_, ?_, rho, (a, b), st, ?_, ?_, hcs⟩
    · intro i ann hlt hf q hq
      unfold checkAnnotationShape at hann
      simp only [ex_bind_ok] at hann
      obtain ⟨_, _, _, _, hlast⟩ := hann
      have hi' := (forAll_ok _ _).1 hlast i (List.mem_range.2 hlt)
      cases hfind : ctx.varRoots.find? (·.1 == i) with
      | none => simp [hfind] at hf
      | some pr =>
        obtain ⟨x, rs⟩ := pr
        simp only [hfind, Option.map_some, Option.some.injEq] at hf
        subst hf
        simp only [hfind] at hi'
        have hq' := (forAll_ok _ _).1 hi' q hq
        cases q with
        | «local» y => simp only at hq'; inv at hq'
        | global g => exact Or.inr ⟨g, rfl⟩
        | param j =>
          simp only at hq'; inv at hq'
          exact Or.inl (by rw [hq'])
    · unfold checkResultShape at hrs
      inv at hrs
      exact hrs.1
    · intro x cont hf
      cases hfind : ctx.contentRoots.find? (·.1 == x) with
      | none => simp [hfind] at hf
      | some pr =>
        obtain ⟨x', cont'⟩ := pr
        simp only [hfind, Option.map_some, Option.some.injEq] at hf
        subst hf
        have hx : x' = x := by simpa using List.find?_some hfind
        subst hx
        unfold checkContentShape at hcont
        have h1 := (forAll_ok _ _).1 hcont _ (List.mem_of_find?_eq_some hfind)
        simp only at h1
        inv at h1
        obtain ⟨hlt, h1⟩ := h1
        cases hv : impl.vars[x']? with
        | none => simp only [hv] at h1; inv at h1
        | some lv =>
          simp only [hv] at h1; inv at h1
          obtain ⟨_, hannx, hall⟩ := h1
          refine ⟨hlt, by simpa using hannx, ?_⟩
          intro y hy
          have h2 := (forAll_ok _ _).1 hall _ hy
          simp only at h2
          inv at h2
    · rcases hck with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> exact hrb
    · intro hs
      rcases hck with ⟨_, h2, _⟩ | ⟨h1, _⟩
      · exact h2
      · exact absurd hs h1

/-- `validate` accepting a module gives the per-item facts the proof uses. -/
theorem validate_modOk (m : Module) (h : validate m = .ok ()) : ModOk m := by
  unfold validate at h
  inv at h
  obtain ⟨hstruct, hentry, _, hglob, himpl, hctx, hinit, hdemand⟩ := h
  refine ⟨hstruct, ?_, ?_, ?_, checkEntry_ok m hentry, hdemand,
    deriveModuleDemand_ok_wellFormed m hdemand⟩
  · intro i impl hi
    exact checkImpl_ok m impl ((forAll_ok _ _).1 himpl impl
      (Array.mem_toList_iff.2 (Array.mem_of_getElem? hi)))
  · intro c ctx hc
    exact checkContext_ok m ctx ((forAll_ok _ _).1 hctx ctx
      (Array.mem_toList_iff.2 (Array.mem_of_getElem? hc)))
  · intro g gl hg
    have hlt : g < m.globals.size := (Array.getElem?_eq_some_iff.1 hg).1
    have h1 := (forAll_ok _ _).1 hglob g (List.mem_range.2 hlt)
    simp only [hg] at h1
    obtain ⟨hty, hinit'⟩ := checkGlobal_ok m g gl h1
    obtain ⟨rho, st, k1, k2, k3⟩ := checkInitRoots_ok m g gl hg
      ((forAll_ok _ _).1 hinit g (List.mem_range.2 hlt))
    exact ⟨hty, hinit', rho, st, k1, k2, k3⟩

end Goose.Core.Sound
