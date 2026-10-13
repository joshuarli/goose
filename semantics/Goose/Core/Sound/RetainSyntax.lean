import Goose.Core.Sound.Retain
import Goose.Core.Sound.Spec

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

end Goose.Core.Sound
