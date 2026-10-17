import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceSites
import Goose.Lower.Validation.ReplacementContentFlowSourceOccurrenceScalarsBasic
import Goose.Lower.Validation.SummaryPreservationReplayFunctionFinish

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation

private theorem emitsOnlyRun_unchanged {property : Inst → Prop} {action : B α}
    (unchanged : ∀ le state, (action le state).2.blocks = state.blocks) :
    EmitsOnlyRun property action := by
  intro le before result after run
  apply EmitsOnly.of_blocks
  simpa only [run] using unchanged le before

private theorem emitsOnlyRun_newBlock (property : Inst → Prop) (types : List VTy) :
    EmitsOnlyRun property (Goose.Lower.newBlock types) := by
  intro le before result after run
  rw [newBlock_run_general] at run
  cases run
  exact (EmitsOnly.newBlock before _).trans (.of_blocks rfl)

theorem finishFunction_emitsOnly {property : Inst → Prop} (impl : Impl) (value : ValueId)
    (terms : ∀ term, property (.term term)) :
    EmitsOnlyRun property (Goose.Lower.finishFunction impl value) := by
  simp only [Goose.Lower.finishFunction]
  refine EmitsOnlyRun.bind (emitsOnlyRun_unchanged (by intros; rfl)) fun env => ?_
  refine EmitsOnlyRun.bind (emitsOnlyRun_unchanged (by intros; rfl)) fun live => ?_
  cases live <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact EmitsOnlyRun.pure _ _
  · split
    · refine EmitsOnlyRun.bind (emitsOnlyRun_newBlock _ []) fun pair => ?_
      refine EmitsOnlyRun.bind (emitsOnly_emitTerm _ (terms _)) fun _ => ?_
      refine EmitsOnlyRun.bind (emitsOnlyRun_unchanged (by intros; rfl)) fun _ => ?_
      exact emitsOnly_emitTerm _ (terms _)
    · exact emitsOnly_emitTerm _ (terms _)

theorem OccurrenceLedger.finishFunction {env : PEnv} {root : DemandNode} {func : Func}
    {types : Array (Option VTy)} {upper : Prov} {initial before after : LS} {le : LEnv}
    (ledger : OccurrenceLedger env root func types upper initial before)
    (impl : Impl) (value : ValueId)
    (run : Goose.Lower.finishFunction impl value le before = ((), after)) :
    OccurrenceLedger env root func types upper initial after :=
  ledger.trans (finishFunction_emitsOnly impl value
    (InstructionOccurrences.term env root func types upper) le before () after run)

theorem generatedTargetFrame_finishFunction (impl : Impl) (value : ValueId) :
    GeneratedTargetFrameRun none (Goose.Lower.finishFunction impl value) := by
  intro base le before result after baseBefore frames framed run
  cases current : before.cur with
  | none =>
    have identity : Goose.Lower.finishFunction impl value le before = ((), before) := by
      simp only [Goose.Lower.finishFunction, bind_run, read_apply, isLive_none current,
        Bool.false_eq_true, ite_false, pure_run]
    rw [identity] at run
    cases run
    exact ⟨framed, .refl _⟩
  | some block =>
    by_cases sink : !impl.results.isEmpty && impl.body.value.isNone && impl.body.diverges le.mod.noReturn
    · let fresh := Goose.Lower.newBlock [] le before
      let first := Goose.Lower.emitTerm (.br fresh.1.1 []) le fresh.2
      let selected := (Goose.Lower.setCur (some fresh.1.1) le first.2).2
      have whole : Goose.Lower.finishFunction impl value le before =
          Goose.Lower.emitTerm (.br fresh.1.1 []) le selected := by
        simp only [Goose.Lower.finishFunction, bind_run, read_apply, isLive_run current,
          ite_true, sink, fresh, first, selected]
      rw [whole] at run
      have allocated := generatedTargetFrame_newBlock none [] base le before fresh.1 fresh.2
        baseBefore frames framed rfl
      have targets : ∀ target, target ∈ (Term.br fresh.1.1 []).successors →
          target < base.blocks.size → LoopBuilderFrameTarget none target := by
        intro target member bound
        have identity : target = before.blocks.size := by
          simpa only [Term.successors, List.mem_singleton, fresh, newBlock0_run] using member
        rw [identity] at bound
        have lower := baseBefore.1
        exact False.elim ((Nat.not_lt_of_ge lower) bound)
      have firstFramed := allocated.1.emitTermAt (show Goose.Lower.emitTerm (.br fresh.1.1 []) le fresh.2 = first from rfl) targets
      have selectedFramed : TermEdgesFramed none base selected := firstFramed.of_blocks rfl
      exact ⟨selectedFramed.emitTermAt run targets,
        allocated.2.trans ((advB_emitTerm _ le fresh.2 first.1 first.2 rfl).ext.trans
          ((EmitsOnly.of_blocks (property := fun _ => True) (before := first.2) (after := selected) rfl).extension.trans (advB_emitTerm _ le selected result after run).ext))⟩
    · have whole : Goose.Lower.finishFunction impl value le before =
          Goose.Lower.emitTerm (.ret (if impl.body.value.isSome then [value] else []) none) le before := by
        simp only [Goose.Lower.finishFunction, bind_run, read_apply, isLive_run current,
          ite_true, sink, Bool.false_eq_true, ite_false]
      rw [whole] at run
      exact ⟨framed.emitTermAt run (by simp [Term.successors]), (advB_emitTerm _ le before result after run).ext⟩

theorem OccurrenceSitesBuilder.finishFunction {env : PEnv} {root : DemandNode}
    {targets : List BlockId} {le : LEnv} {state : LS} {func : Func} {types : Array (Option VTy)} {upper : Prov}
    (sites : OccurrenceSitesBuilder env root targets le state func types upper)
    (impl : Impl) (value : ValueId) :
    OccurrenceSitesBuilder env root targets le (Goose.Lower.finishFunction impl value le state).2 func types upper := by
  apply sites.of_emits
    (finishFunction_emitsOnly impl value (by intro term; trivial) le state _ _ rfl)
    (ReplayBuilder.types_finishFunction impl value le state _ _ rfl)
    (ReplacementIntervalsPreserved.of_run (generatedTargetFrame_finishFunction impl value) rfl)
    (Nat.le_refl _) (fun _ _ => rfl)

#print axioms finishFunction_emitsOnly
#print axioms OccurrenceLedger.finishFunction
#print axioms generatedTargetFrame_finishFunction
#print axioms OccurrenceSitesBuilder.finishFunction

end Goose.Lower.Validation.ReplacementContentFlowSource
