import Goose.Lower.DemandIndexAssignmentPrefix
import Goose.Lower.DemandStoppedStatementFamily

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

theorem accepted_generated_index_assignment_stopped {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {rootOwner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root rootOwner)
    (loop : Option LoopCtx) (owner : Place) (form : IndexOwnerPlace owner) (index value : Expr) (indexOrigin origin : OriginId)
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
  obtain ⟨ownerFuel, location, addressedPoint, placed, addressedState, addressPost, addressSteps, addressed⟩ :=
    accepted_generated_index_owner_general destination form destinationOccurrence destinationRows bounded destinationRealized
      input.atPoint input.related placeExtended
  obtain ⟨ownerCount, remaining, ownerCountEq, ownerTrace, tail⟩ := addressSteps.stopped_prefix steps stopped nonTimeout
  rcases addressedPoint with ⟨addressPoint, addressFrame, addressState⟩
  dsimp only at addressedState
  subst addressState
  rcases tail.uncons with ⟨rfl, rfl⟩ | ⟨remaining, snapshot, rfl, snapshotStep, tail⟩
  · obtain ⟨_, view, viewTyping, viewRoots, viewCanonical, _⟩ := destination.elemChildren indexOrigin
    have viewOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root view.path (.view (.of owner)) before := by
      rw [viewCanonical.path]
      exact .first destinationOccurrence (.placeView rfl)
    have viewRows : GeneratedDemandRows cfg.mod view.rootsEnv.access viewOccurrence required := by
      have inherited : GeneratedDemandRows cfg.mod destination.rootsEnv.access (.first destinationOccurrence (.placeView rfl)) required :=
        .first (first := .placeView rfl) destinationRows
      simpa only [viewRoots, viewCanonical.path] using inherited
    have viewStop := accepted_generated_snapshot_runtime_stop view viewOccurrence viewRows placed addressPost
      (generated_index_view_extended placeExtended) nonTimeout stopped
    have done : execStmt (ownerFuel + 3) cfg env (.assign place value origin) state = .stop stop after := by
      dsimp only [place]
      simp only [execStmt, evalPlace, bind_apply, viewStop]
    change execStmt (ownerFuel + 3) cfg env (.assign (.elem (.of owner) index indexOrigin) value origin) state = .stop stop after at done
    exact .aborted (ownerFuel + 3) (by simp only [bind_apply, done])
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
      refine .aborted (max (ownerFuel + 1) indexFuel + 2) ?_
      simp only [bind_apply, done]
    | @complete indexFuel indexCount left boundary indexValue count indexTrace residual indexDone indexBoundary =>
      let common := max (ownerFuel + 1) indexFuel
      have viewed' : evalView common cfg env (.of owner) state = .ok sample snapshot.state :=
        ((monoAll (ownerFuel + 1) common (by dsimp [common]; exact Nat.le_max_left _ _)).view cfg env (.of owner) state).1 _ _ viewed
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
          exact .complete (consumed := ownerCount + indexCount + consumed + 1) (by omega)
            (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              (ownerTrace.append (DemandRuntimePrefix.next snapshotStep (indexTrace.append suffixTrace))))
            suffixRest evaluated finalPost

#print axioms accepted_generated_index_assignment_stopped
end Goose.Lower
