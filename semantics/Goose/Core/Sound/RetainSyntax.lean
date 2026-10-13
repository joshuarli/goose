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

end Goose.Core.Sound
