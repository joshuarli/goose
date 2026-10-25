import Goose.Lower.Validation.ValueTypes
import Goose.Lower.Validation.SummaryPreservationReplayLoopsBuilder
import Goose.Lower.Validation.SummaryPreservationReplayTerm
import Goose.Lower.Validation.SummaryPreservationReturnTransfer

namespace Goose.Lower.Validation.SummaryPreservation.ReplayBuilder

open Goose.Core Goose.GIR

theorem types_finishFunction (impl : Impl) (value : ValueId) :
    TypeRun (Goose.Lower.finishFunction impl value) := by
  unfold Goose.Lower.finishFunction
  refine TypeRun.bind types_read fun le => TypeRun.bind types_isLive fun live => ?_
  cases live
  · exact TypeRun.pure _
  · by_cases sink : !impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn
    · rw [if_pos sink]
      exact TypeRun.bind (types_newBlock []) fun _ =>
        TypeRun.bind (types_emitTerm _) fun _ => TypeRun.bind (types_setCur _) fun _ => types_emitTerm _
    · rw [if_neg sink]
      exact types_emitTerm _

variable {module : GIR.Module} {results : Array (List RootRef)} {vt : Array (Option VTy)}
  {func : Func} {target : Core.Eff} {le : LEnv} {scopeCount : Nat}
  {slots : Array (List RootRef)} {state : LS} {upper : Prov}

private theorem returnFrame_newBlock_empty (le : LEnv) (state : LS) :
    ReturnMembershipFrame state (newBlock [] le state).2 :=
  ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_newBlock []) le state _ _ rfl

private theorem returnFrame_setCur (current : Option BlockId) (le : LEnv) (state : LS) :
    ReturnMembershipFrame state (Goose.Lower.setCur current le state).2 :=
  ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_setCur current) le state _ _ rfl

theorem finishFunction (impl : Impl) (value : ValueId) (expected : List RootRef)
    (ready : ReplayBuilder module results vt func target le scopeCount slots state upper)
    (valueBound : state.cur.isSome = true → impl.body.value.isSome = true → value < state.vals.size)
    (returned : state.cur.isSome = true → impl.body.value.isSome = true →
      ∀ root ∈ rootsAt upper.vals value, root ∈ expected) :
    ReplayBuilder module results vt func target le scopeCount slots
        (Goose.Lower.finishFunction impl value le state).2 upper ∧
      ReturnBoundsPreserved expected state upper (Goose.Lower.finishFunction impl value le state).2 upper := by
  cases current : state.cur with
  | none =>
    have stopped : Goose.Lower.finishFunction impl value le state = ((), state) := by
      simp only [Goose.Lower.finishFunction, bind_run, read_apply, isLive_none current, Bool.false_eq_true, ite_false, pure_run]
    rw [stopped]
    exact ⟨ready, ReturnBoundsPreserved.refl expected state upper⟩
  | some block =>
    have live : state.cur.isSome = true := by simp [current]
    by_cases sink : !impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn
    · let fresh := newBlock [] le state
      let first := Goose.Lower.emitTerm (.br fresh.1.1 []) le fresh.2
      let selected := (Goose.Lower.setCur (some fresh.1.1) le first.2).2
      have freshReady := ready.loopEmptyBlock
      have freshBound : fresh.1.1 < fresh.2.blocks.size := by simp [fresh, newBlock0_run]
      have firstReady := freshReady.loopBranch fresh.1.1 [] freshBound (by simp) (by simp)
      have selectedReady := firstReady.setCur (some fresh.1.1) (by
        intro destination same
        cases Option.some.inj same
        exact Nat.lt_of_lt_of_le freshBound (advB_emitTerm (.br fresh.1.1 []) le fresh.2 first.1 first.2 rfl).ext.1)
      have selectedBound : fresh.1.1 < selected.blocks.size := by
        simpa only [selected, setCur_run] using
          (Nat.lt_of_lt_of_le freshBound (advB_emitTerm (.br fresh.1.1 []) le fresh.2 first.1 first.2 rfl).ext.1)
      have completed := selectedReady.loopBranch fresh.1.1 [] selectedBound (by simp) (by simp)
      have whole : Goose.Lower.finishFunction impl value le state =
          Goose.Lower.emitTerm (.br fresh.1.1 []) le selected := by
        simp only [Goose.Lower.finishFunction, bind_run, read_apply, isLive_run current, ite_true, sink,
          fresh, first, selected]
      rw [whole]
      refine ⟨completed, ?_⟩
      apply ReturnBoundsPreserved.frame ready.symbols ready.roots.valueSize (fun _ _ => rfl)
      apply (returnFrame_newBlock_empty le state).trans
      apply (ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_emitTerm (.br fresh.1.1 [])
        (by intro values origin same; cases same)) le fresh.2 _ _ rfl).trans
      apply (returnFrame_setCur (some fresh.1.1) le first.2).trans
      exact ReturnFrameRun.of_absence (fun _ => ReturnFrames.returnAbsent_emitTerm (.br fresh.1.1 [])
        (by intro values origin same; cases same)) le selected _ _ rfl
    · let term := Term.ret (if impl.body.value.isSome then [value] else []) none
      have whole : Goose.Lower.finishFunction impl value le state = Goose.Lower.emitTerm term le state := by
        simp only [Goose.Lower.finishFunction, bind_run, read_apply, isLive_run current, ite_true,
          sink, Bool.false_eq_true, ite_false, term]
      rw [whole]
      constructor
      · apply ready.emitTerm term
        · intro _
          apply Inst.SymbolsWithin.term
          · intro operand member
            by_cases present : impl.body.value.isSome = true
            · have same : operand = value := by simpa only [term, Term.uses, present, ite_true, List.mem_singleton] using member
              simpa only [same] using valueBound live present
            · simp [term, Term.uses, present] at member
          · simp [term, Term.origin]
          · simp [term, Term.successors]
        · intros; trivial
        · intro _; exact effectRefinement_empty func target
      · apply ReturnBoundsPreserved.emitTerm ready.current term
        intro found origin same root member
        by_cases present : impl.body.value.isSome = true
        · have identity : found = value := by simpa [term, present] using (Term.ret.inj same).1.symm
          subst found
          exact returned live present root member
        · simp [term, present] at same

#print axioms types_finishFunction
#print axioms finishFunction

end Goose.Lower.Validation.SummaryPreservation.ReplayBuilder
