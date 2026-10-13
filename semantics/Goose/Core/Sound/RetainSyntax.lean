import Goose.Core.Sound.Retain
import Goose.Core.Sound.Spec
import Goose.Core.Sound.AccessReplay

/-!
Convert validated places and sampled views into the value form used by the
retention algebra.
-/

namespace Goose.Core.Sound
open Goose.Core Goose.Proofs.Memory

/-- A place is represented by a reference to its location when that reference
type is expressible by the runtime `HasTy` relation. -/
theorem AliasAt.ofPlace {m : Module} {W : World} {penv : PEnv} {env : Env} {s : Store}
    {alias : RetainedAlias} {p : Place} {l : Loc} {t : Ty}
    (hty : alias.ty = .ref .mutable t)
    (hrepresentable : t.refTarget = true ∨ t.isSlice = true)
    (hplace : PlaceOk m W.G W.P penv env s p l t)
    (hroot : Gam env W.P alias.roots l.root) :
    AliasAt m W env s alias (.ref l) := by
  unfold AliasAt
  rw [hty]
  constructor
  · refine ⟨l, rfl, ?_⟩
    rcases hplace with ⟨href, hl⟩ | ⟨x, lv, si, v, _, _, _, hl, _, hlike, hv, hval⟩ |
      ⟨x, lv, mu0, mu, E, ann, hp, hvars, hLv, ht, hflat, hpath, hann, hgam, hrootExists⟩
    · exact Or.inl ⟨href, hl⟩
    · have hs : t.isSlice = true := by
        cases t <;> simp_all [Ty.isRefLike, Ty.isSlice, Ty.refTarget]
      have hpath : l.path = [] := by simp [hl]
      have hrootExists : s.roots[l.root]? ≠ none := by
        rw [hl, hv]
        simp
      exact Or.inr ⟨hs, hpath, hrootExists⟩
    · subst t
      exact Or.inr ⟨by simpa [Ty.isSlice] using hflat, hpath, hrootExists⟩
  · intro r hr
    change l.root = r at hr
    subst r
    exact hroot

/-- A sampled view is represented by its run as a synthetic slice value. -/
theorem AliasAt.ofView {m : Module} {W : World} {env : Env} {s : Store}
    {alias : RetainedAlias} {vw : ViewVal} {el : Ty}
    (hty : alias.ty = .slice .readOnly el)
    (hview : ViewOk s vw el)
    (hroot : Gam env W.P alias.roots vw.loc.root) :
    AliasAt m W env s alias (.slice vw.loc vw.start vw.len) := by
  unfold AliasAt
  rw [hty]
  constructor
  · exact ⟨vw.loc, vw.start, vw.len, rfl, hview.1, hview.2.1⟩
  · intro r hr
    change vw.loc.root = r at hr
    subst r
    exact hroot

/-- A checked place alias is realized by the location from place evaluation. -/
theorem AliasAt.ofAliasPlace {m : Module} {W : World} {penv : PEnv} {env : Env} {s : Store}
    {alias : RetainedAlias} {path : List Nat} {p : Place} {l : Loc} {t : Ty}
    {state : RState} {rho : List RootRef} {state' : RState}
    (halias : penv.access.aliasPlace path p = .ok [alias])
    (htype : penv.access.placeType? p = some t)
    (hreplay : rpPlace penv p state = .ok (rho, state'))
    (hplace : PlaceOk m W.G W.P penv env s p l t)
    (hroot : Gam env W.P rho l.root)
    (hrepresentable : t.refTarget = true ∨ t.isSlice = true) :
    AliasAt m W env s alias (.ref l) := by
  obtain ⟨aliasTy, roots, hlookup, hroots, haliasShape⟩ :=
    AccessEnv.aliasPlace_singleton penv.access path p alias halias
  have htypeEq : aliasTy = t := Option.some.inj (hlookup.symm.trans htype)
  have hty : alias.ty = .ref .mutable t := by
    rw [haliasShape, htypeEq]
  have hroot' : Gam env W.P roots l.root :=
    Gam.subset hroot (fun q hq =>
      rpPlace_accessRoots penv p state rho state' roots hreplay hroots q hq)
  have hrootAlias : Gam env W.P alias.roots l.root := by
    rw [haliasShape]
    exact hroot'
  exact AliasAt.ofPlace hty hrepresentable hplace hrootAlias

/-- A checked view alias is realized by the run returned from view evaluation. -/
theorem AliasAt.ofAliasView {m : Module} {W : World} {penv : PEnv} {env : Env} {s : Store}
    {alias : RetainedAlias} {path : List Nat} {view : View} {vw : ViewVal} {el : Ty}
    {state : RState} {rho : List RootRef} {state' : RState}
    (halias : penv.access.aliasView path view = .ok [alias])
    (htype : penv.access.viewElement? view = some el)
    (hreplay : rpView penv view state = .ok (rho, state'))
    (hview : ViewOk s vw el)
    (hroot : Gam env W.P rho vw.loc.root) :
    AliasAt m W env s alias (.slice vw.loc vw.start vw.len) := by
  obtain ⟨aliasEl, roots, hlookup, hroots, haliasShape⟩ :=
    AccessEnv.aliasView_singleton penv.access path view alias halias
  have htypeEq : aliasEl = el := Option.some.inj (hlookup.symm.trans htype)
  have hty : alias.ty = .slice .readOnly el := by
    rw [haliasShape, htypeEq]
  have hroot' : Gam env W.P roots vw.loc.root :=
    Gam.subset hroot (fun q hq =>
      rpView_accessRoots penv view state rho state' roots hreplay hroots q hq)
  have hrootAlias : Gam env W.P alias.roots vw.loc.root := by
    rw [haliasShape]
    exact hroot'
  exact AliasAt.ofView hty hview hrootAlias

/-- A checked read cannot use a reference to an uninitialized global. This
fact depends only on the declared roots and permitted effects. -/
theorem Gam.notUnbound_of_access {m : Module} {W : World} {env : Env} {l : Loc} {t : Ty}
    {rho : List RootRef} (hp : Perm m W) (hg : Gam env W.P rho l.root)
    (hin : ∀ target, target ∈ rootsTargets rho →
      target ∈ W.E.reads ∨ target ∈ W.E.writes ∨
        target ∈ W.E.grows ∨ target ∈ W.E.shrinks) : ¬ Unbound m W.G l t := by
  rintro ⟨g, global, hG, hroot, hglobal, _⟩
  rw [hroot] at hg
  have hlt : g < m.globals.size := (Array.getElem?_eq_some_iff.mp hglobal).1
  rcases hp with hp | ⟨_, hp⟩
  · omega
  · obtain ⟨q, hq, hr⟩ := hg
    cases q with
    | «local» x => obtain ⟨_, _, _, _, h⟩ := hr; cases h
    | global g' =>
      have heq : RootInst.global g = RootInst.global g' := hr
      cases heq
      have hbound : g < W.G := hp _ (hin _ (mem_rootsTargets_global hq))
      omega
    | param i =>
      have hbound : g < W.G := hp _ (hin _ (mem_rootsTargets_param hq)) _ hr g rfl
      omega

/-- Fixed views retain the run produced by their checked evaluation. -/
theorem ViewAliases.ofFixed {m : Module} {W : World} {penv : PEnv} {env : Env} {s : Store}
    {source : View} {vw : ViewVal} {el : Ty} {state state' : RState} {rho : List RootRef}
    (hresizable : vw.resizable = false)
    (htype : penv.access.viewElement? source = some el)
    (hreplay : rpView penv source state = .ok (rho, state'))
    (hview : ViewOk s vw el) (hroot : Gam env W.P rho vw.loc.root) :
    ViewAliases m W penv env s source vw el := by
  apply ViewAliases.fixed hresizable
  intro path alias halias
  obtain ⟨aliasEl, roots, hlookup, _, hshape⟩ :=
    AccessEnv.aliasView_singleton penv.access path source alias halias
  have heq : aliasEl = el := Option.some.inj (hlookup.symm.trans htype)
  refine ⟨?_, AliasAt.ofAliasView halias htype hreplay hview hroot⟩
  rw [hshape, heq]

/-- Resizable views retain the checked owner location rather than its old length. -/
theorem ViewAliases.ofOwner {m : Module} {W : World} {penv : PEnv} {env : Env} {s : Store}
    {p : Place} {vw : ViewVal} {el owner : Ty} {state state' : RState} {rho : List RootRef}
    (hresizable : vw.resizable = true) (hflat : el.flat = true)
    (howner : owner = .grow el ∨ owner = .growshrink el)
    (htype : penv.access.placeType? p = some owner)
    (hreplay : rpPlace penv p state = .ok (rho, state'))
    (hplace : PlaceOk m W.G W.P penv env s p vw.loc owner)
    (hroot : Gam env W.P rho vw.loc.root) (hbound : ¬ Unbound m W.G vw.loc owner) :
    ViewAliases m W penv env s (.of p) vw el := by
  apply ViewAliases.owner hresizable p owner rfl howner htype hbound
  intro path alias halias
  obtain ⟨aliasTy, roots, hlookup, _, hshape⟩ :=
    AccessEnv.aliasPlace_singleton penv.access path p alias halias
  have heq : aliasTy = owner := Option.some.inj (hlookup.symm.trans htype)
  refine ⟨?_, AliasAt.ofAliasPlace halias htype hreplay hplace hroot ?_⟩
  · rw [hshape, heq]
  · rcases howner with rfl | rfl <;> exact Or.inl (by simpa [Ty.refTarget] using hflat)

/-- A pilot store extension preserves either kind of source realization. -/
theorem ViewAliases.mono {m : Module} {W : World} {penv : PEnv} {env : Env}
    {s s' : Store} {source : View} {vw : ViewVal} {el : Ty}
    (hle : StoreLe s s') (h : ViewAliases m W penv env s source vw el) :
    ViewAliases m W penv env s' source vw el := by
  cases h with
  | fixed hresize hrealized =>
    apply ViewAliases.fixed hresize
    intro path alias halias
    obtain ⟨hty, hvalue, hroots⟩ := hrealized path alias halias
    exact ⟨hty, hvalue.mono hle, hroots⟩
  | owner hresize p owner hsource howner htype hbound hrealized =>
    apply ViewAliases.owner hresize p owner hsource howner htype hbound
    intro path alias halias
    obtain ⟨hty, hvalue, hroots⟩ := hrealized path alias halias
    exact ⟨hty, hvalue.mono hle, hroots⟩

/-- A retained, bound owner reference supplies its current location typing. -/
theorem AliasAt.ownerLocation {m : Module} {W : World} {env : Env} {s : Store}
    {alias : RetainedAlias} {l : Loc} {owner el : Ty}
    (htype : alias.ty = .ref .mutable owner)
    (howner : owner = .grow el ∨ owner = .growshrink el)
    (hbound : ¬ Unbound m W.G l owner)
    (h : AliasAt m W env s alias (.ref l)) : LocTy s l owner := by
  have htyped := h.1
  rw [htype] at htyped
  obtain ⟨l', heq, hloc⟩ := htyped
  cases heq
  rcases hloc with ⟨_, hloc, _⟩ | ⟨hslice, _, _⟩
  · exact hloc.resolve_right hbound
  · rcases howner with rfl | rfl <;> simp [Ty.isSlice] at hslice

end Goose.Core.Sound
