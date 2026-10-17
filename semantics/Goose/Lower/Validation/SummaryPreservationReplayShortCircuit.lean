import Goose.Lower.Validation.SummaryPreservationReplayShortCircuitBuilder
import Goose.Lower.Validation.SummaryPreservationReplayValue

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

theorem shortCircuit (isAnd : Bool) (value : ValueId) (rhs : B ValueId)
    (grows : AdvB rhs)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (input : ls.cur.isSome = true → value < ls.vals.size ∧ rootsAt upper.vals value = [])
    (rhsChild : ∀ provenance, ls.cur.isSome = true →
      let entry := { (scFork isAnd value le ls).2 with cur := some (scFork isAnd value le ls).1.1 }
      ReplayBuilder module results vt func target le scopeCount slots entry provenance →
      ∃ next, ReplayBuilder module results vt func target le scopeCount slots (rhs le entry).2 next ∧
        ((rhs le entry).2.cur.isSome = true →
          (rhs le entry).1 < (rhs le entry).2.vals.size ∧ rootsAt next.vals (rhs le entry).1 = []) ∧
        ∀ index, index < provenance.vals.size → rootsAt next.vals index = rootsAt provenance.vals index) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (Goose.Lower.shortCircuit isAnd value rhs le ls).2 next ∧
      ((Goose.Lower.shortCircuit isAnd value rhs le ls).2.cur.isSome = true →
        ReplayValue func next (Goose.Lower.shortCircuit isAnd value rhs le ls).2
          (Goose.Lower.shortCircuit isAnd value rhs le ls).1 [] (.data .bool)) ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  cases current : ls.cur with
  | none =>
    rw [Goose.Lower.shortCircuit, whenLive_none _ _ _ current]
    exact ⟨upper, ready, by simp [current], fun _ _ => rfl⟩
  | some block =>
    obtain ⟨bound, scalar⟩ := input (by simp [current])
    obtain ⟨middle, forkReady, parameterRoots, forkPrefix⟩ := ready.scalarFork isAnd value bound scalar
    let forked := scFork isAnd value le ls
    let entry := { forked.2 with cur := some forked.1.1 }
    have rightBound : forked.1.1 < forked.2.blocks.size := by
      simp [forked, scFork_run _ _ _ current]
      exact Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)
    have joinBound : forked.1.2.1 < forked.2.blocks.size := by
      simp [forked, scFork_run _ _ _ current]
    have parameterBound : forked.1.2.2 < forked.2.vals.size := by
      simp [forked, scFork_run _ _ _ current]
    have exactParameter : rootsAt middle.vals forked.1.2.2 = [] := by
      simpa only [forked, scFork_run _ _ _ current] using parameterRoots
    have entryReady : ReplayBuilder module results vt func target le scopeCount slots entry middle := by
      have selected := forkReady.setCur (some forked.1.1) (by
        intro candidate row
        cases row
        exact rightBound)
      simpa only [setCur_run] using selected
    obtain ⟨next, rhsReady, rhsValue, rhsPrefix⟩ := rhsChild middle (by simp [current]) entryReady
    let produced := rhs le entry
    have rhsGrowth := grows le entry produced.1 produced.2 rfl
    have producedJoin : forked.1.2.1 < produced.2.blocks.size :=
      Nat.lt_of_lt_of_le joinBound rhsGrowth.ext.1
    have termReady := rhsReady.emitTerm (.br forked.1.2.1 [produced.1])
      (fun live => by
        apply Inst.SymbolsWithin.term
        · simpa [Term.uses] using (rhsValue live).1
        · simp [Term.origin]
        · simpa [Term.successors] using producedJoin)
      (fun live => by
        intro target row pair member root rootMember
        have argument := (List.of_mem_zip member).2
        simp only [List.mem_singleton] at argument
        rw [argument, (rhsValue live).2] at rootMember
        cases rootMember)
      (fun _ => effectRefinement_empty func target)
    have completed := termReady.setCur (some forked.1.2.1) (by
      intro candidate row
      cases row
      change forked.1.2.1 < (Goose.Lower.emitTerm (.br forked.1.2.1 [produced.1]) le produced.2).2.blocks.size
      cases live : produced.2.cur with
      | none => simpa only [emitTerm_none _ _ live] using producedJoin
      | some currentBlock => simpa only [emitTerm_run _ _ live, Array.size_modify] using producedJoin)
    have whole : Goose.Lower.shortCircuit isAnd value rhs le ls =
        (forked.1.2.2, (Goose.Lower.setCur (some forked.1.2.1) le
          (Goose.Lower.emitTerm (.br forked.1.2.1 [produced.1]) le produced.2).2).2) := by
      simp only [Goose.Lower.shortCircuit, whenLive_some _ _ _ current, bind_run, setCur_run, pure_run]
      rfl
    rw [whole]
    refine ⟨next, completed, ?_, ?_⟩
    · intro _
      have sameRoots : rootsAt next.vals forked.1.2.2 = [] := by
        rw [rhsPrefix forked.1.2.2 (by rw [forkReady.roots.valueSize]; exact parameterBound)]
        exact exactParameter
      refine ⟨?_, ?_, fun _ => sameRoots⟩
      · change forked.1.2.2 < (Goose.Lower.setCur (some forked.1.2.1) le
          (Goose.Lower.emitTerm (.br forked.1.2.1 [produced.1]) le produced.2).2).2.vals.size
        rw [setCur_run]
        have valueBound : forked.1.2.2 < produced.2.vals.size :=
          Nat.lt_of_lt_of_le parameterBound rhsGrowth.vals
        cases live : produced.2.cur with
        | none => simpa only [emitTerm_none _ _ live] using valueBound
        | some currentBlock => simpa only [emitTerm_run _ _ live] using valueBound
      · rw [sameRoots]
        intro root member
        cases member
    · intro index bound
      have growth : upper.vals.size ≤ middle.vals.size := by
        rw [ready.roots.valueSize, forkReady.roots.valueSize]
        simp [scFork_run _ _ _ current]
      exact (rhsPrefix index (Nat.lt_of_lt_of_le bound growth)).trans (forkPrefix index bound)

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
