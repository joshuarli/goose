import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceControlBlockAction

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

theorem blockOccurrenceValue {module : GIR.Module} {results : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {target : Core.Eff} {le : LEnv}
    {scopeCount : Nat} {slots : Array (List RootRef)} {initial : LS} {upper : Prov}
    {expected : List RootRef} {env : PEnv} {root siteRoot : DemandNode} {siteTargets : List BlockId}
    (want : Bool) (value : Option Expr) (sourceRoots : List RootRef) (type : VTy)
    (ready : ReplayBuilder module results vt func target le scopeCount slots initial upper)
    (sites : OccurrenceSitesBuilder env siteRoot siteTargets le initial func vt upper)
    (missing : value = none → sourceRoots = [] ∧ type = .data .unit)
    (free : ReturnFreeValue value)
    (child : ∀ expression, value = some expression →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots
          (lowerExpr expression le initial).2 next ∧
        ((lowerExpr expression le initial).2.cur.isSome = true →
          ReplayValue func next (lowerExpr expression le initial).2
            (lowerExpr expression le initial).1 sourceRoots type) ∧
        (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
        OccurrenceLedger env root func vt next initial (lowerExpr expression le initial).2 ∧
        OccurrenceSitesBuilder env siteRoot siteTargets le (lowerExpr expression le initial).2 func vt next) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (lowerBlockValue want value le initial).2 next ∧
      (want = true → (lowerBlockValue want value le initial).2.cur.isSome = true →
        ReplayValue func next (lowerBlockValue want value le initial).2
          (lowerBlockValue want value le initial).1 sourceRoots type) ∧
      (∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) ∧
      ReturnBoundsPreserved expected initial upper (lowerBlockValue want value le initial).2 next ∧
      OccurrenceLedger env root func vt next initial (lowerBlockValue want value le initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets le (lowerBlockValue want value le initial).2 func vt next := by
  have frame (next : Prov) (retained : ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index) :
      ∀ expected, ReturnBoundsPreserved expected initial upper (lowerBlockValue want value le initial).2 next := by
    intro expected
    exact ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize retained
      (ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_lowerBlockValue want value free)
        le initial _ _ rfl)
  cases value with
  | some expression =>
    obtain ⟨next, completed, returned, retained, ledger, finalSites⟩ := child expression rfl
    exact ⟨next, completed, (fun _ => returned), retained, frame next retained expected, ledger, finalSites⟩
  | none =>
    obtain ⟨next, completed, returned, retained⟩ := ready.blockValue want none sourceRoots type missing
      (by intro expression impossible; cases impossible)
    have growth : upper.vals.size ≤ next.vals.size := by
      rw [ready.roots.valueSize, completed.roots.valueSize]
      exact (advB_lowerBlockValue want none le initial _ _ rfl).vals
    have initialSites := sites.ghost_retained growth retained
    cases want with
    | false => exact ⟨next, completed, returned, retained, frame next retained expected, .refl _ _, initialSites⟩
    | true =>
      exact ⟨next, completed, returned, retained, frame next retained expected,
        occurrence_emitDef_live rfl (fun _ => InstructionOccurrences.constUnit _ _ _ _ _ _),
        initialSites.emitDef rfl (Nat.le_refl _) (fun _ _ => rfl)⟩

#print axioms blockOccurrenceValue

end Goose.Lower.Validation.ReplacementContentFlowSource
