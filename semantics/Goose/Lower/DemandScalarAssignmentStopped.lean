import Goose.Lower.DemandScalarAssignmentPrefix
import Goose.Lower.DemandStoppedStatementFamily

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

theorem accepted_generated_literal_assignment_stopped {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (place : Place) (form : ScalarReadPlace place) (type : IntTy) (number : Int) (origin : OriginId) :
    GeneratedStoppedStatementPrefixFamily cx results selected loop (.assign place (.lit type number) origin) := by
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
    have childType : child.ty = .int type := by
      have typed := child.typed
      simp only [tyExpr] at typed
      split at typed
      · exact (congrArg Prod.fst (Except.ok.inj typed)).symm
      · cases typed
    have destinationType : destination.ty = .int type := typeEq.symm.trans childType
    have middleCarried := realized.retained addressPost.same bounded.1 bounded.2 RetainsAliases.refl
    have addressBounded := bounded.mono addressPost.mono
    obtain ⟨aliases, query, nextCoverage, nextBounded, nextAdmitted, nextRealized, childInput⟩ :=
      accepted_assignment_scalar_value_demand source form destination destinationRoots destinationWorld destinationType placed
        child childAt childTyping childRoots coverage admitted addressBounded input addressPost middleCarried
    have childOwner : GeneratedSourceOwner selected child.context :=
      (owned.child rfl 1 (.expression (.lit type number)) .expression rfl (by trivial)).transport
        childAt.plans.symm childAt.path.symm rfl childAt.context.symm
    have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.expression (.lit type number)) addressed.2 := by
      rw [childAt.path]
      exact .assignmentValue occurrence
    have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence
        (required.addValues addressed.1 aliases) := by
      have inherited := GeneratedDemandRows.assignmentValue rows query
      simpa only [childRoots, childAt.path] using inherited
    have childExtended := generated_assignment_value_extended extended
    have childProgress := accepted_generated_leaf_stopped_family selected loop (.literal type number) rfl ()
      child childOwner childOccurrence childRows nextCoverage nextAdmitted nextBounded nextRealized childInput childExtended tail stopped nonTimeout
    cases childProgress with
    | aborted fuel evaluated =>
      cases fuel with
      | zero => simp [evalExpr, timeout, M.stop] at evaluated; exact (nonTimeout evaluated.1.symm).elim
      | succ fuel => simp [evalExpr, pure_apply] at evaluated
    | @complete rightFuel rightCount left boundary result count rightTrace residual rightDone rightBoundary =>
      have post := addressPost.comp rightBoundary.post
      have combinedPost : Post cfg env cx before initial
          (lowerExpr (.lit type number) le addressed.2).2 boundary.frame boundary.point
          [(addressed.1, .val (.ref location)), ((lowerExpr (.lit type number) le addressed.2).1, .val result)] := by
        simpa only [List.singleton_append] using post
      have site : GeneratedAssignmentStoreSite cfg.mod source.rootsEnv.access cx.fn le root source.path before loop place
          (.lit type number) origin required boundary.point := ⟨occurrence, rows, ⟨aliases, query⟩, combinedPost.pp, extended⟩
      let common := max 1 rightFuel
      have placed' : evalPlace common cfg env place state = .ok location state :=
        ((monoAll 1 common (by dsimp [common]; exact Nat.le_max_left _ _)).place cfg env place state).1 _ _ placed
      have rightDone' : evalExpr common cfg env (.lit type number) state = .ok result boundary.state :=
        ((monoAll rightFuel common (by dsimp [common]; exact Nat.le_max_right _ _)).expr cfg env (.lit type number) state).1 _ _ rightDone
      rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨rest, final, rfl, store, afterStore⟩
      · have done := accepted_generated_assignment_store_stop source site placed' rightDone' combinedPost stopped nonTimeout
        refine .aborted (common + 1) ?_
        simp only [bind_apply, done]
      · obtain ⟨_, _, done, finalPost, finalResult, finalBounded, finalDemand⟩ :=
          accepted_generated_assignment_store_step source site admitted bounded realized placed' rightDone' combinedPost store
        have prepared : (execStmt (common + 1) cfg env (.assign place (.lit type number) origin) >>= prepareLoopFlow env loop) state =
            .ok (.normal .unit) final.state := by
          simp only [bind_apply, done]
          cases loop <;> rfl
        exact .complete (by omega) (.next first (rightTrace.append (.next store (.zero _)))) afterStore prepared
          (.normal finalPost finalResult finalBounded finalDemand.operands)

#print axioms accepted_generated_literal_assignment_stopped

end Goose.Lower
