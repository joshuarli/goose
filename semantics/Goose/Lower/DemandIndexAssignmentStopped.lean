import Goose.Lower.DemandIndexAssignmentPrefix
import Goose.Lower.DemandStoppedStatementFamily

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

theorem accepted_generated_index_assignment_stopped {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {rootOwner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root rootOwner)
    (loop : Option LoopCtx) (owner : Place) (form : ScalarReadPlace owner) (index value : Expr) (indexOrigin origin : OriginId)
    (target : ∀ {state after : St} (source : StmtSource cfg env (.assign (.elem (.of owner) index indexOrigin) value origin) state)
      (child : ExprSource cfg env value after), source.AssignmentValueAt child → child.ty.refTarget = true)
    (indexFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop index)
    (valueFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop value) :
    GeneratedStoppedStatementPrefixFamily cx results selected loop (.assign (.elem (.of owner) index indexOrigin) value origin) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps targetFuel stop after stopped nonTimeout
  let le := lowerEnv cfg.mod env.vars results
  let place := Place.elem (.of owner) index indexOrigin
  obtain ⟨destination, destinationTyping, destinationRoots, destinationWorld, _, destinationAt, _⟩ := source.assignChildrenDemand
  have destinationOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root destination.path (.place place) before := by
    rw [destinationAt.path]
    exact .assignmentPlace occurrence
  have destinationRows : GeneratedDemandRows cfg.mod destination.rootsEnv.access destinationOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.assignmentPlace occurrence) required := .assignmentPlace rows
    simpa only [destinationRoots, destinationAt.path] using inherited
  have destinationRealized : map.Realizes cfg.mod destination.world env ⟨start, initial, state⟩ := by
    simpa only [destinationWorld] using realized
  have destinationAdmitted : map.Admitted cfg.mod.profile destination.context.retained := by
    intro shrink alias member
    exact destinationAt.retained alias (admitted shrink alias member)
  have destinationOwner : GeneratedSourceOwner selected destination.context :=
    (owned.child rfl 0 (.place place) .place rfl (by trivial)).transport
      destinationAt.plans.symm destinationAt.path.symm rfl destinationAt.context.symm
  have destinationInput : GeneratedPrefixInput cfg env cx results loop destination.typingEnv destination.rootsEnv before initial start := by
    simpa only [destinationTyping, destinationRoots] using input
  have placeExtended := generated_assignment_place_extended extended
  obtain ⟨location, placed, addressPost, addressStep, addressed⟩ := accepted_generated_index_owner_address destination form
    destinationOccurrence destinationRows bounded destinationRealized input.atPoint input.related placeExtended
  let middle : DemandRuntimePoint := ⟨(start.1, start.2 + 1),
    initial.set (lowerPlace owner le before).1 (.val (.ref location)), state⟩
  rcases steps.uncons with ⟨rfl, rfl⟩ | ⟨remaining, current, rfl, first, tail⟩
  · exact (stopped.excludes_step_nonTimeout nonTimeout (addressStep targetFuel)).elim
  · obtain ⟨fuel, firstStep⟩ := runtimeStep_demandInstructionStep first
    have same := firstStep.deterministic (addressStep fuel)
    have currentEq : current = middle := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
    subst current
    rcases tail.uncons with ⟨rfl, rfl⟩ | ⟨remaining, snapshot, rfl, snapshotStep, tail⟩
    · have done := accepted_generated_index_assignment_snapshot_stop source form occurrence rows bounded realized input.atPoint input.related extended
        (.next first (.zero _)) nonTimeout stopped
      refine .aborted 4 ?_
      simp only [bind_apply, done]
    · obtain ⟨sample, aliases, child, viewed, childCanonical, viewQuery, viewPost, progress⟩ :=
        accepted_generated_index_expression_stopped destination form selected destinationOwner destinationOccurrence destinationRows
          coverage destinationAdmitted bounded destinationRealized destinationInput placed addressPost addressed placeExtended snapshotStep
          indexFamily tail stopped nonTimeout
      have baseCoverage : (map.addRuns (lowerView (.of owner) le before).1 aliases).Covers map := by
        constructor
        · intro cell member; exact member
        · intro cell member; exact List.mem_append_right _ member
      cases progress with
      | aborted indexFuel indexStop =>
        have done := indexed_assignment_expression_stop nonTimeout viewed indexStop (value := value) (origin := origin) (indexOrigin := indexOrigin)
        refine .aborted (max 2 indexFuel + 2) ?_
        simp only [bind_apply, done]
      | @complete indexFuel indexCount left boundary indexValue count indexTrace residual indexDone indexBoundary =>
        let common := max 2 indexFuel
        have viewed' : evalView common cfg env (.of owner) state = .ok sample snapshot.state :=
          ((monoAll 2 common (by dsimp [common]; exact Nat.le_max_left _ _)).view cfg env (.of owner) state).1 _ _ viewed
        have indexed' : evalExpr common cfg env index snapshot.state = .ok indexValue boundary.state :=
          ((monoAll indexFuel common (by dsimp [common]; exact Nat.le_max_right _ _)).expr cfg env index snapshot.state).1 _ _ indexDone
        have indexRealized : (map.addRuns (lowerView (.of owner) le before).1 aliases).Realizes
            cfg.mod source.world env ⟨boundary.point, boundary.frame, boundary.state⟩ := by
          simpa only [RetainedSsaMap.Realizes, childCanonical.world, destinationWorld] using indexBoundary.demanded.operands
        have query : source.rootsEnv.access.aliasView (source.path ++ [0, 0]) (.of owner) = .ok aliases := by
          simpa only [destinationRoots, destinationAt.path, List.append_assoc, List.singleton_append] using viewQuery
        rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨remaining, afterCheck, rfl, checkStep, rest⟩
        · obtain ⟨_, _, done⟩ := accepted_generated_index_assignment_bounds_stop source occurrence rows query
            (coverage.addRuns _ aliases) viewed' indexed' viewPost indexBoundary.post indexRealized extended nonTimeout stopped
          refine .aborted (common + 2) ?_
          simp only [bind_apply, done]
        · have suffix := accepted_generated_index_assignment_store_stopped source form occurrence rows coverage admitted query viewed' indexed'
            viewPost indexBoundary.post indexBoundary.bounded indexRealized bounded realized input extended
            (fun child childAt => target source child childAt) selected owned valueFamily checkStep rest stopped nonTimeout
          cases suffix with
          | aborted fuel done => exact .aborted fuel done
          | @complete statementFuel consumed remaining endPoint flow suffixCount suffixTrace suffixRest evaluated finalPost =>
            exact .complete (consumed := indexCount + consumed + 2) (by omega)
              (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (DemandRuntimePrefix.next first (DemandRuntimePrefix.next snapshotStep (indexTrace.append suffixTrace))))
              suffixRest evaluated finalPost

#print axioms accepted_generated_index_assignment_stopped
end Goose.Lower
