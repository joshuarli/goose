import Goose.Lower.DemandScalarAssignmentPrefix
import Goose.Lower.DemandStoppedStatementFamily

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

theorem accepted_generated_scalar_assignment_stopped {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (place : Place) (form : ScalarReadPlace place) (expression : Expr) (origin : OriginId)
    (target : ∀ {state after : St} (source : StmtSource cfg env (.assign place expression origin) state)
      (child : ExprSource cfg env expression after), source.AssignmentValueAt child → child.ty.refTarget = true)
    (valueFamily : GeneratedStoppedExpressionPrefixFamily cx results selected loop expression) :
    GeneratedStoppedStatementPrefixFamily cx results selected loop (.assign place expression origin) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps targetFuel stop after stopped nonTimeout
  let le := lowerEnv cfg.mod env.vars results
  let addressed := lowerPlace place le before
  obtain ⟨destination, destinationTyping, destinationRoots, destinationWorld, destinationObservation, destinationAt, next⟩ :=
    source.assignChildrenDemand
  have destinationOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root destination.path (.place place) before := by
    rw [destinationAt.path]
    exact .assignmentPlace occurrence
  have destinationRows : GeneratedDemandRows cfg.mod destination.rootsEnv.access destinationOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.assignmentPlace occurrence) required := .assignmentPlace rows
    simpa only [destinationRoots, destinationAt.path] using inherited
  obtain ⟨location, placed, addressPost, addressStep⟩ := accepted_generated_scalar_place_address destination form
    destinationOccurrence destinationRows input.atPoint input.related (generated_assignment_place_extended extended)
  let middle : DemandRuntimePoint := ⟨(start.1, start.2 + 1), initial.set addressed.1 (.val (.ref location)), state⟩
  have destinationRealized : map.Realizes cfg.mod destination.world env ⟨start, initial, state⟩ := by
    simpa only [destinationWorld] using realized
  rcases steps.uncons with ⟨rfl, rfl⟩ | ⟨remaining, current, rfl, first, tail⟩
  · exact (stopped.excludes_step_nonTimeout nonTimeout (addressStep targetFuel)).elim
  · obtain ⟨fuel, firstStep⟩ := runtimeStep_demandInstructionStep first
    have same := firstStep.deterministic (addressStep fuel)
    have currentEq : current = middle := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
    subst current
    obtain ⟨child, childTyping, childRoots, childWorld, childObservation, typeEq, childAt⟩ := next 1 location state placed
    have destinationTarget : destination.ty.refTarget = true := by
      rw [← typeEq]
      exact target source child childAt
    have middleCarried := realized.retained addressPost.same bounded.1 bounded.2 RetainsAliases.refl
    have addressBounded := bounded.mono addressPost.mono
    obtain ⟨aliases, query, nextCoverage, nextBounded, nextAdmitted, nextRealized, childInput⟩ :=
      accepted_assignment_scalar_value_demand source form destination destinationRoots destinationWorld rfl destinationTarget placed
        child childAt childTyping childRoots coverage admitted addressBounded input addressPost middleCarried
    have childOwner : GeneratedSourceOwner selected child.context :=
      (owned.child rfl 1 (.expression expression) .expression rfl (by trivial)).transport
        childAt.plans.symm childAt.path.symm rfl childAt.context.symm
    have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.expression expression) addressed.2 := by
      rw [childAt.path]
      exact .assignmentValue occurrence
    have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence
        (required.addValues addressed.1 aliases) := by
      have inherited := GeneratedDemandRows.assignmentValue rows query
      simpa only [childRoots, childAt.path] using inherited
    have childExtended := generated_assignment_value_extended extended
    have childProgress := valueFamily
      child childOwner childOccurrence childRows nextCoverage nextAdmitted nextBounded nextRealized childInput childExtended tail stopped nonTimeout
    cases childProgress with
    | aborted fuel evaluated =>
      let common := max 1 fuel
      have placed' : evalPlace common cfg env place state = .ok location state :=
        ((monoAll 1 common (by dsimp [common]; exact Nat.le_max_left _ _)).place cfg env place state).1 _ _ placed
      have evaluated' : evalExpr common cfg env expression state = .stop stop after := by
        rcases ((monoAll fuel common (by dsimp [common]; exact Nat.le_max_right _ _)).expr cfg env expression state).2 _ _ evaluated with timeout | done
        · cases stop <;> simp_all [Goose.Proofs.Fuel.isTimeout]
        · exact done
      refine .aborted (common + 1) ?_
      simp [execStmt, bind_apply, placed', evaluated']
    | @complete rightFuel rightCount left boundary result count rightTrace residual rightDone rightBoundary =>
      have post := addressPost.comp rightBoundary.post
      have combinedPost : Post cfg env cx before initial
          (lowerExpr expression le addressed.2).2 boundary.frame boundary.point
          [(addressed.1, .val (.ref location)), ((lowerExpr expression le addressed.2).1, .val result)] := by
        simpa only [List.singleton_append] using post
      have site : GeneratedAssignmentStoreSite cfg.mod source.rootsEnv.access cx.fn le root source.path before loop place
          expression origin required boundary.point := ⟨occurrence, rows, ⟨aliases, query⟩, combinedPost.pp, extended⟩
      let common := max 1 rightFuel
      have placed' : evalPlace common cfg env place state = .ok location state :=
        ((monoAll 1 common (by dsimp [common]; exact Nat.le_max_left _ _)).place cfg env place state).1 _ _ placed
      have rightDone' : evalExpr common cfg env expression state = .ok result boundary.state :=
        ((monoAll rightFuel common (by dsimp [common]; exact Nat.le_max_right _ _)).expr cfg env expression state).1 _ _ rightDone
      rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨rest, final, rfl, store, afterStore⟩
      · have done := accepted_generated_assignment_store_stop source site placed' rightDone' combinedPost stopped nonTimeout
        refine .aborted (common + 1) ?_
        simp only [bind_apply, done]
      · obtain ⟨_, _, done, finalPost, finalResult, finalBounded, finalDemand⟩ :=
          accepted_generated_assignment_store_step source site admitted bounded realized placed' rightDone' combinedPost store
        have prepared : (execStmt (common + 1) cfg env (.assign place expression origin) >>= prepareLoopFlow env loop) state =
            .ok (.normal .unit) final.state := by
          simp only [bind_apply, done]
          cases loop <;> rfl
        exact .complete (by omega) (.next first (rightTrace.append (.next store (.zero _)))) afterStore prepared
          (.normal finalPost finalResult finalBounded finalDemand.operands)

#print axioms accepted_generated_scalar_assignment_stopped

end Goose.Lower
