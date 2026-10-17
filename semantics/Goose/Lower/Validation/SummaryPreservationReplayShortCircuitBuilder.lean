import Goose.Lower.Validation.SummaryPreservationReplayLoopsBuilder
import Goose.Lower.Validation.SummaryPreservationReplayTerm

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {ls : LS} {upper : Prov}

private theorem emptyEdge {func : Func} {upper : Prov} {destination : BlockId} {arguments : List ValueId}
    (scalar : ∀ value ∈ arguments, rootsAt upper.vals value = []) :
    EdgeRootsClosed func upper destination arguments := by
  intro block row pair member root rootMember
  rw [scalar pair.2 (List.of_mem_zip member).2] at rootMember
  cases rootMember

theorem scalarFork (isAnd : Bool) (value : ValueId)
    (ready : ReplayBuilder module results vt func target le scopeCount slots ls upper)
    (bound : value < ls.vals.size) (scalar : rootsAt upper.vals value = []) :
    ∃ next, ReplayBuilder module results vt func target le scopeCount slots
        (scFork isAnd value le ls).2 next ∧
      rootsAt next.vals ls.vals.size = [] ∧
      ∀ index, index < upper.vals.size → rootsAt next.vals index = rootsAt upper.vals index := by
  have first := ready.loopEmptyBlock
  obtain ⟨next, allocated, resultRoots, retained⟩ := first.loopScalarBlock (.data .bool)
  let allocatedState := (newBlock [.data .bool] le (newBlock [] le ls).2).2
  have valueBound : value < allocatedState.vals.size := by
    simpa [allocatedState, newBlock0_run, newBlock1_run] using Nat.lt_succ_of_lt bound
  have emptyValue : rootsAt next.vals value = [] := by
    rw [retained value (by simpa only [newBlock0_run, ready.roots.valueSize] using bound)]
    exact scalar
  have firstBlock : ls.blocks.size < allocatedState.blocks.size := by
    simp only [allocatedState, newBlock0_run, newBlock1_run, Array.size_push]
    omega
  have joinBlock : ls.blocks.size + 1 < allocatedState.blocks.size := by
    simp [allocatedState, newBlock0_run, newBlock1_run]
  have emitted : ReplayBuilder module results vt func target le scopeCount slots
      (Goose.Lower.emitTerm (scTerm isAnd value ls.blocks.size (ls.blocks.size + 1)) le allocatedState).2 next := by
    apply allocated.emitTerm
    · intro _
      apply Inst.SymbolsWithin.term
      · cases isAnd <;> simpa [scTerm, Term.uses] using valueBound
      · cases isAnd <;> simp [scTerm, Term.origin]
      · cases isAnd
        · simpa [scTerm, Term.successors] using And.intro joinBlock firstBlock
        · simpa [scTerm, Term.successors] using And.intro firstBlock joinBlock
    · intro _
      cases isAnd <;> constructor
      all_goals apply emptyEdge
      all_goals intro input member
      all_goals simp at member
      all_goals subst input
      all_goals exact emptyValue
    · intro _
      cases isAnd <;> exact effectRefinement_empty func target
  have whole : scFork isAnd value le ls =
      let produced := Goose.Lower.emitTerm (scTerm isAnd value ls.blocks.size (ls.blocks.size + 1)) le allocatedState
      ((ls.blocks.size, ls.blocks.size + 1, ls.vals.size), produced.2) := by
    cases isAnd <;> simp only [scFork, scTerm, bind_run, newBlock0_run, newBlock1_run,
      Array.size_push, pure_run, Bool.false_eq_true, ite_false, ite_true]
    all_goals rfl
  rw [whole]
  exact ⟨next, emitted, resultRoots, retained⟩

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
