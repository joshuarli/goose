import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceSites
import Goose.Lower.Validation.SummaryPreservationReplayReferences
import Goose.Lower.Validation.SummaryPreservationReplayEmit

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {initial : LS} {upper : Prov}

private theorem argumentBorrowReplay (mutability : Mutability) (targetType : Ty)
    (address : ValueId) (sourceRoots : List RootRef)
    (ready : ReplayBuilder module results vt func target le scopeCount slots initial upper)
    (input : initial.cur.isSome = true → address < initial.vals.size ∧
      GIR.RootsRefine func (rootsAt upper.vals address) sourceRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (borrowTo mutability address le initial).2 next ∧
      ((borrowTo mutability address le initial).2.cur.isSome = true →
        ReplayValue func next (borrowTo mutability address le initial).2
          (borrowTo mutability address le initial).1 sourceRoots (.data (.ref mutability targetType))) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ((borrowTo mutability address le initial).2.cur.isSome = true →
        rootsAt next.vals (borrowTo mutability address le initial).1 = rootsAt upper.vals address) := by
  let Complete (next : Prov) := ReplayBuilder module results vt func target le scopeCount slots
        (borrowTo mutability address le initial).2 next ∧
      ((borrowTo mutability address le initial).2.cur.isSome = true →
        ReplayValue func next (borrowTo mutability address le initial).2
          (borrowTo mutability address le initial).1 sourceRoots (.data (.ref mutability targetType))) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      ((borrowTo mutability address le initial).2.cur.isSome = true →
        rootsAt next.vals (borrowTo mutability address le initial).1 = rootsAt upper.vals address)
  change ∃ next, Complete next
  cases current : initial.cur with
  | none =>
    obtain ⟨next, completed, returned, retained⟩ :=
      ready.borrowReference mutability targetType address sourceRoots input
    have dead : (borrowTo mutability address le initial).2.cur = none :=
      (stopped_borrowTo mutability address le initial
        (borrowTo mutability address le initial).1 (borrowTo mutability address le initial).2 rfl current).1
    exact ⟨next, completed, returned, retained, by simp [dead]⟩
  | some block =>
    obtain ⟨bound, refined⟩ := input (by simp [current])
    have emitted (operation : Op)
        (run : borrowTo mutability address le initial = Goose.Lower.emitDef operation le initial)
        (uses : ∀ value ∈ operation.uses, value < initial.vals.size)
        (origin : ∀ candidate, operation.origin = some candidate → candidate < le.mod.origins.size)
        (references : Op.SymbolRefsValid le operation)
        (relay : rootsOfDef results vt func upper initial.vals.size operation = rootsAt upper.vals address)
        (neutral : func.effectStep module vt upper {} (.def initial.vals.size operation) = {}) :
        ∃ next, Complete next := by
      obtain ⟨next, completed, returned, retained⟩ := ready.emitDef operation sourceRoots uses origin references
        (by rw [neutral]; exact effectRefinement_empty func target) (by rw [relay]; exact refined)
      refine ⟨next, ?_⟩
      dsimp only [Complete]
      rw [run]
      refine ⟨completed, ?_, retained, ?_⟩
      · intro live
        exact ⟨(returned live).1, (returned live).2.2, by simp [VTy.refLike, Ty.isRefLike]⟩
      · intro live
        exact (returned live).2.1.trans relay
    rcases borrowTo_cases (rfl : borrowTo mutability address le initial = _) with frozen | borrowed
    · rcases freezeTo_cases frozen with same | frozen
      · have run : borrowTo mutability address le initial = (address, initial) := Prod.ext same.1 same.2
        refine ⟨upper, ?_⟩
        dsimp only [Complete]
        rw [run]
        exact ⟨ready, (fun _ => ⟨bound, refined, by simp [VTy.refLike, Ty.isRefLike]⟩), fun _ _ => rfl, fun _ => rfl⟩
      · exact emitted (.refFreeze address) frozen.symm
          (by simpa [Op.uses] using bound) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]) rfl rfl
    · exact emitted (.ownerBorrow address) borrowed.symm
        (by simpa [Op.uses] using bound) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]) rfl rfl

theorem argumentBorrowOccurrence {env : PEnv} {root siteRoot : DemandNode} {siteTargets : List BlockId}
    (mutability : Mutability) (targetType : Ty) (address : ValueId) (sourceRoots : List RootRef)
    (ready : ReplayBuilder module results vt func target le scopeCount slots initial upper)
    (sites : OccurrenceSitesBuilder env siteRoot siteTargets le initial func vt upper)
    (input : initial.cur.isSome = true → address < initial.vals.size ∧
      GIR.RootsRefine func (rootsAt upper.vals address) sourceRoots) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (borrowTo mutability address le initial).2 next ∧
      ((borrowTo mutability address le initial).2.cur.isSome = true →
        ReplayValue func next (borrowTo mutability address le initial).2
          (borrowTo mutability address le initial).1 sourceRoots (.data (.ref mutability targetType))) ∧
      (∀ old, old < upper.vals.size → rootsAt next.vals old = rootsAt upper.vals old) ∧
      OccurrenceLedger env root func vt next initial (borrowTo mutability address le initial).2 ∧
      OccurrenceSitesBuilder env siteRoot siteTargets le
        (borrowTo mutability address le initial).2 func vt next ∧
      ((borrowTo mutability address le initial).2.cur.isSome = true →
        rootsAt next.vals (borrowTo mutability address le initial).1 = rootsAt upper.vals address) := by
  obtain ⟨next, completed, returned, retained, physical⟩ :=
    argumentBorrowReplay mutability targetType address sourceRoots ready input
  have growth : upper.vals.size ≤ next.vals.size := by
    rw [ready.roots.valueSize, completed.roots.valueSize]
    exact (advB_borrowTo mutability address le initial _ _ rfl).vals
  have emitted : OccurrenceLedger env root func vt next initial (borrowTo mutability address le initial).2 ∧
      EmitsOnly NotReplacement initial (borrowTo mutability address le initial).2 := by
    rcases borrowTo_cases (rfl : borrowTo mutability address le initial = _) with frozen | borrowed
    · rcases freezeTo_cases frozen with same | frozen
      · exact ⟨same.2.symm ▸ .refl _ _, same.2.symm ▸ .refl _ _⟩
      · exact ⟨emitsOnly_emitDef frozen (by simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands]),
          emitsOnly_emitDef frozen trivial⟩
    · exact ⟨emitsOnly_emitDef borrowed (by simp [InstructionOccurrences, GIR.ReplacementContentFlow.Model.accessOperands]),
        emitsOnly_emitDef borrowed trivial⟩
  exact ⟨next, completed, returned, retained, emitted.1,
    sites.of_emits emitted.2 (types_borrowTo mutability address le initial _ _ rfl)
      (.of_run (generatedTargetFrame_borrowTo none mutability address) rfl) growth retained, physical⟩

#print axioms argumentBorrowOccurrence

end Goose.Lower.Validation.ReplacementContentFlowSource
