import Goose.Core.Sound.Frame

/-!
Static predicates for protecting slice targets from effects that may shrink
their backing owners. This module stays below statement and call proof contexts.
-/

namespace Goose.Core.Sound
open Goose.Core

/-- Whether an effect target denotes a root in this activation. -/
def TargetDenotes (P : Nat → RootInst → Prop) : Target → RootInst → Prop
  | .global g, r => r = .global g
  | .param i, r => P i r

/-- A summary may shrink explicit targets, or any global and parameter root
when its effects are unknown. -/
def MayShrinkEff (P : Nat → RootInst → Prop) (E : Eff) (root : RootInst) : Prop :=
  ∃ target, (target ∈ E.shrinks ∨ E.unknown = true) ∧ TargetDenotes P target root

/-- A protected slice cannot point into any root that the effect may shrink. -/
def ShrinkProtected (D : RootInst → Ty → Prop)
    (A : RootInst → RootInst → Prop) (shrinking : RootInst → Prop) : Prop :=
  ∀ holder element target, D holder element → A holder target →
    ∀ shrinkingRoot, shrinking shrinkingRoot → target ≠ shrinkingRoot

theorem ShrinkProtected.mono
    {D D' : RootInst → Ty → Prop} {A A' : RootInst → RootInst → Prop}
    {shrinking shrinking' : RootInst → Prop}
    (hProtected : ShrinkProtected D A shrinking)
    (hD : ∀ holder element, D' holder element → D holder element)
    (hA : ∀ holder target, A' holder target → A holder target)
    (hShrinking : ∀ root, shrinking' root → shrinking root) :
    ShrinkProtected D' A' shrinking' := by
  intro holder element target hD' hA' shrinkingRoot hShrinking'
  exact hProtected holder element target (hD holder element hD')
    (hA holder target hA') shrinkingRoot (hShrinking shrinkingRoot hShrinking')

theorem TargetDenotes.mono {P P' : Nat → RootInst → Prop} {target : Target}
    {root : RootInst} (hP : ∀ i r, P' i r → P i r)
    (h : TargetDenotes P' target root) : TargetDenotes P target root := by
  cases target with
  | global g => exact h
  | param i => exact hP i root h

theorem MayShrinkEff.mono {P P' : Nat → RootInst → Prop} {E E' : Eff}
    {root : RootInst}
    (hP : ∀ i r, P' i r → P i r)
    (hShrinks : ∀ target, target ∈ E'.shrinks → target ∈ E.shrinks)
    (hUnknown : E'.unknown = true → E.unknown = true)
    (h : MayShrinkEff P' E' root) : MayShrinkEff P E root := by
  obtain ⟨target, hMay, hDenotes⟩ := h
  refine ⟨target, ?_, TargetDenotes.mono hP hDenotes⟩
  rcases hMay with hExplicit | hUnknown'
  · exact Or.inl (hShrinks target hExplicit)
  · exact Or.inr (hUnknown hUnknown')

theorem MayShrinkEff.known_iff {P : Nat → RootInst → Prop} {E : Eff}
    {root : RootInst} (hUnknown : E.unknown = false) :
    MayShrinkEff P E root ↔
      ∃ target, target ∈ E.shrinks ∧ TargetDenotes P target root := by
  simp [MayShrinkEff, hUnknown]

/-- An unknown-free world protects its inherited slices against its summary. -/
def KnownEffectShrinkProtected (W : World) : Prop :=
  W.E.unknown = false ∧ ShrinkProtected W.D W.A (MayShrinkEff W.ownerP W.E)

/-- Narrowing the slice facts and shrink summary preserves protection. -/
theorem KnownEffectShrinkProtected.mono {W W' : World}
    (hProtected : KnownEffectShrinkProtected W)
    (hD : ∀ holder element, W'.D holder element → W.D holder element)
    (hA : ∀ holder target, W'.A holder target → W.A holder target)
    (hP : ∀ i root, W'.ownerP i root → W.ownerP i root)
    (hShrinks : ∀ target, target ∈ W'.E.shrinks → target ∈ W.E.shrinks)
    (hUnknown : W'.E.unknown = true → W.E.unknown = true) :
    KnownEffectShrinkProtected W' := by
  refine ⟨?_, ?_⟩
  · cases h : W'.E.unknown with
    | false => rfl
    | true =>
      exfalso
      have hcontradiction : false = true := hProtected.1.symm.trans (hUnknown h)
      cases hcontradiction
  · apply ShrinkProtected.mono hProtected.2 hD hA
    intro root hMay
    exact MayShrinkEff.mono hP hShrinks hUnknown hMay

end Goose.Core.Sound
