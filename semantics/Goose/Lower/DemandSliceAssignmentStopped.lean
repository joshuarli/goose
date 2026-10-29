import Goose.Lower.DemandSliceAssignmentFamily
import Goose.Lower.DemandSliceAssignmentPath
import Goose.Lower.DemandStoppedStatementFamily

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_slice_assignment_stopped_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (reference : Expr) (mutability : Mutability) (global : GlobalId)
    (intType : IntTy) (number : Int) (sliceOrigin origin : OriginId)
    (slice : ∀ {state : St} (source : StmtSource cfg env (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) state),
      ∃ ty, sliceRefTy source.typingEnv reference = some ty) :
    GeneratedStoppedStatementPrefixFamily cx results selected loop (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps targetFuel stop after stopped nonTimeout
  obtain ⟨ty, sliceTy⟩ := slice source
  by_cases short : taken < 2
  · exact False.elim (accepted_generated_slice_assignment_destination_noStop source sliceTy selected owned occurrence rows coverage admitted bounded
      realized input extended short steps stopped nonTimeout)
  · by_cases atTwo : taken = 2
    · obtain ⟨point, frame, alias, child, canonical, remaining, count, residual, demanded, progress, instruction⟩ :=
        accepted_generated_slice_assignment_value_entry_split source sliceTy selected owned occurrence rows coverage admitted bounded realized input extended (by omega) steps
      have zero : remaining = 0 := by omega
      subst remaining
      cases residual
      exact False.elim (stopped.excludes_step_nonTimeout nonTimeout (progress targetFuel))
    · by_cases atThree : taken = 3
      · obtain ⟨location, point, frame, alias, destination, canonical, placed, executed,
          traversal, destinationPost, query, child, childTyping, childRoots, childAt, childOwner, valueOccurrence, valueRows, valueCoverage,
          valueBounded, valueAdmitted, valueRealized, valueInput⟩ :=
          accepted_generated_slice_assignment_entry source sliceTy selected owned occurrence rows coverage admitted bounded realized input extended
        obtain ⟨view, viewAt, viewOccurrence, viewRows, globalPlace, globalPost, addressStep⟩ :=
          accepted_generated_slice_global_address child valueOccurrence valueRows destinationPost.pp destinationPost.rel
            (generated_assignment_value_extended extended)
        have throughAddress := executed.append (.next ((addressStep 0).runtime) (.zero _))
        obtain ⟨remaining, count, residual⟩ := throughAddress.split_at (by omega) steps
        have zero : remaining = 0 := by omega
        subst remaining
        cases residual
        obtain ⟨_, sourceStop⟩ := accepted_generated_slice_assignment_snapshot_stop source child placed destinationPost valueRows extended stopped nonTimeout
        apply StoppedStatementPrefix.aborted 4
        simp only [bind_apply, sourceStop]
      · by_cases atFour : taken = 4
        · obtain ⟨point, frame, sampled, alias, child, view, canonical, viewAt, remaining, count, residual, demanded, progress, instruction⟩ :=
            accepted_generated_slice_assignment_snapshot_result_split source sliceTy selected owned occurrence rows coverage admitted bounded realized input extended (by omega) steps
          have zero : remaining = 0 := by omega
          subst remaining
          cases residual
          exact False.elim (stopped.excludes_step_nonTimeout nonTimeout (progress targetFuel))
        · by_cases atFive : taken = 5
          · obtain ⟨point, frame, sampled, alias, aliases, child, upper, canonical, upperAt, remaining, count, residual, demanded, instruction, sliceStop, next⟩ :=
              accepted_generated_slice_assignment_literal_stage source sliceTy selected owned occurrence rows coverage admitted bounded realized input extended (by omega) steps
            have zero : remaining = 0 := by omega
            subst remaining
            cases residual
            have sourceStop := sliceStop stopped nonTimeout
            apply StoppedStatementPrefix.aborted 4
            simp only [bind_apply, sourceStop]
          · by_cases atSix : taken = 6
            · obtain ⟨point, frame, sampled, alias, aliases, child, upper, canonical, upperAt, remaining, count, residual, demanded, instruction, sliceStop, next⟩ :=
                accepted_generated_slice_assignment_literal_stage source sliceTy selected owned occurrence rows coverage admitted bounded realized input extended (by omega) steps
              rcases residual.uncons with ⟨empty, _⟩ | ⟨rest, middle, countStep, sliceStep, restSteps⟩
              · omega
              · have zero : rest = 0 := by omega
                subst rest
                cases restSteps
                cases reached with
                | mk slicePoint sliceFrame sliceState =>
                  obtain ⟨destinationFrame, runAliases, value, evaluated, site, boundary, storeStop, complete⟩ :=
                    next slicePoint sliceFrame sliceState sliceStep
                  have sourceStop := storeStop stopped nonTimeout
                  apply StoppedStatementPrefix.aborted 4
                  simp only [bind_apply, sourceStop]
            · have progress := accepted_generated_slice_assignment_completed_prefix source sliceTy selected owned occurrence rows coverage admitted bounded realized input extended
                (fun _ => False) (by omega) steps
              cases progress.progress with
              | interior impossible => exact False.elim impossible
              | complete count executed residual evaluated post => exact .complete count executed residual evaluated post

#print axioms accepted_generated_slice_assignment_stopped_family
end Goose.Lower
