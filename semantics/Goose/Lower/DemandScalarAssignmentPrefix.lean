import Goose.Lower.DemandShortCircuitPrefixFamily
import Goose.Lower.DemandScalarPlaceAddress
import Goose.Lower.DemandAssignmentStore

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

inductive ScalarAssignmentPrefixCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | destination {place : Place} {expression : Expr} {origin : OriginId} {state : St}
      {source : StmtSource cfg env (.assign place expression origin) state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
      (child : PlaceSource cfg env place state) (canonical : source.PlaceChildAt child rfl)
      (demanded : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.inputFuture
        map.values map.runs ⟨start, initial, state⟩) :
      ScalarAssignmentPrefixCursor cx results source before built initial start map required ⟨start, initial, state⟩
  | value {place : Place} {expression : Expr} {origin : OriginId} {state after : St}
      {source : StmtSource cfg env (.assign place expression origin) state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (child : ExprSource cfg env expression after) (canonical : source.AssignmentValueAt child)
      (aliases : List RetainedAlias)
      (demanded : CanonicalExpressionDemand (map.addValues (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1 aliases)
        cx child runtime) :
      ScalarAssignmentPrefixCursor cx results source before built initial start map required runtime
  | store {place : Place} {expression : Expr} {origin : OriginId} {state after : St}
      {source : StmtSource cfg env (.assign place expression origin) state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      {root : DemandNode} {loop : Option LoopCtx}
      (child : ExprSource cfg env expression after) (canonical : source.AssignmentValueAt child)
      (aliases : List RetainedAlias)
      (site : GeneratedAssignmentStoreSite cfg.mod source.rootsEnv.access cx.fn (lowerEnv cfg.mod env.vars results)
        root source.path before loop place expression origin required runtime.point)
      (demanded : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        (map.addValues (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1 aliases).values
        (map.addValues (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1 aliases).runs runtime) :
      ScalarAssignmentPrefixCursor cx results source before built initial start map required runtime

theorem accepted_generated_scalar_assignment_prefix {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (place : Place) (form : ScalarReadPlace place) (expression : Expr) (origin : OriginId)
    (target : ∀ {state after : St} (source : StmtSource cfg env (.assign place expression origin) state)
      (child : ExprSource cfg env expression after), source.AssignmentValueAt child → child.ty.refTarget = true)
    (valueFamily : GeneratedExpressionPrefixFamily cx results selected loop expression (@CanonicalExpressionPrefixCursor cfg env cx)) :
    GeneratedStatementPrefixFamily cx results selected loop (.assign place expression origin)
      (@ScalarAssignmentPrefixCursor cfg env cx results) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
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
  refine ⟨owned, coverage, ?_⟩
  rcases steps.uncons with ⟨rfl, rfl⟩ | ⟨remaining, current, rfl, first, tail⟩
  · exact .interior (.destination destination destinationAt ⟨⟨_, input.atPoint, input.related⟩, destination.frame, destinationRealized⟩)
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
      child childOwner childOccurrence childRows nextCoverage nextAdmitted nextBounded nextRealized childInput childExtended tail
    cases childProgress.progress with
    | interior demanded => exact .interior (.value child childAt aliases demanded)
    | @complete rightFuel rightCount left boundary result count rightTrace residual rightDone rightBoundary =>
      have post := addressPost.comp rightBoundary.post
      have combinedPost : Post cfg env cx before initial
          (lowerExpr expression le addressed.2).2 boundary.frame boundary.point
          [(addressed.1, .val (.ref location)), ((lowerExpr expression le addressed.2).1, .val result)] := by
        simpa only [List.singleton_append] using post
      have site : GeneratedAssignmentStoreSite cfg.mod source.rootsEnv.access cx.fn le root source.path before loop place
          expression origin required boundary.point := ⟨occurrence, rows, ⟨aliases, query⟩, combinedPost.pp, extended⟩
      rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨rest, final, rfl, store, afterStore⟩
      · exact .interior (.store child childAt aliases site rightBoundary.demanded)
      · let common := max 1 rightFuel
        have placed' : evalPlace common cfg env place state = .ok location state :=
          ((monoAll 1 common (by dsimp [common]; exact Nat.le_max_left _ _)).place cfg env place state).1 _ _ placed
        have rightDone' : evalExpr common cfg env expression state = .ok result boundary.state :=
          ((monoAll rightFuel common (by dsimp [common]; exact Nat.le_max_right _ _)).expr cfg env expression state).1 _ _ rightDone
        obtain ⟨_, _, done, finalPost, finalResult, finalBounded, finalDemand⟩ :=
          accepted_generated_assignment_store_step source site admitted bounded realized placed' rightDone' combinedPost store
        have prepared : (execStmt (common + 1) cfg env (.assign place expression origin) >>= prepareLoopFlow env loop) state =
            .ok (.normal .unit) final.state := by
          simp only [bind_apply, done]
          cases loop <;> rfl
        exact .complete (by omega) (.next first (rightTrace.append (.next store (.zero _)))) afterStore prepared
          (.normal finalPost finalResult finalBounded finalDemand.operands)

theorem ScalarAssignmentPrefixCursor.realizes {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : ScalarAssignmentPrefixCursor cx results source before built initial start map required runtime) :
    map.Realizes cfg.mod source.world env runtime := by
  cases cursor with
  | destination child canonical demanded =>
    change RetainedOperandsAt cfg.mod source.world env state.store initial map.values map.runs
    simpa only [canonical.world] using demanded.operands
  | value child canonical aliases demanded =>
    have coverage (id : ValueId) : (map.addValues id aliases).Covers map := by
      constructor
      · intro cell member
        exact List.mem_append_right _ member
      · intro cell member
        exact member
    simpa only [canonical.world] using (coverage _).realizes demanded.carried
  | store child canonical aliases site demanded =>
    have coverage (id : ValueId) : (map.addValues id aliases).Covers map := by
      constructor
      · intro cell member
        exact List.mem_append_right _ member
      · intro cell member
        exact member
    simpa only [canonical.world] using (coverage _).realizes demanded.operands

#print axioms accepted_generated_scalar_assignment_prefix
#print axioms ScalarAssignmentPrefixCursor.realizes

end Goose.Lower
