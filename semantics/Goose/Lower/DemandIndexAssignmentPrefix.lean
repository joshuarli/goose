import Goose.Lower.DemandIndexAssignmentValueEntry
import Goose.Lower.DemandControlBlockPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Fuel

inductive IndexAssignmentPrefixCursor {cfg : Cfg} {env : Env} (cx : FnCtx) (results : List Ty) :
    {statement : Stmt} → {state : St} → StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop
  | frame {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      {typing : TEnv} {roots : PEnv} {future : _}
      (frame : DemandFrameAt cfg env cx source.world typing roots future map.values map.runs runtime) :
      IndexAssignmentPrefixCursor cx results source before built initial start map required runtime
  | value {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
      (cursor : ScalarAssignmentPrefixCursor cx results source before built initial start map required runtime) :
      IndexAssignmentPrefixCursor cx results source before built initial start map required runtime

theorem accepted_generated_index_assignment_prefix {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {rootOwner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root rootOwner)
    (loop : Option LoopCtx) (owner : Place) (form : ScalarReadPlace owner) (index value : Expr) (indexOrigin origin : OriginId)
    (target : ∀ {state after : St} (source : StmtSource cfg env (.assign (.elem (.of owner) index indexOrigin) value origin) state)
      (child : ExprSource cfg env value after), source.AssignmentValueAt child → child.ty.refTarget = true)
    (indexFamily : GeneratedExpressionPrefixFamily cx results selected loop index (@CanonicalExpressionPrefixCursor cfg env cx))
    (valueFamily : GeneratedExpressionPrefixFamily cx results selected loop value (@CanonicalExpressionPrefixCursor cfg env cx)) :
    GeneratedStatementPrefixFamily cx results selected loop (.assign (.elem (.of owner) index indexOrigin) value origin)
      (@IndexAssignmentPrefixCursor cfg env cx results) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
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
  refine ⟨owned, coverage, ?_⟩
  rcases steps.uncons with ⟨rfl, rfl⟩ | ⟨remaining, current, rfl, first, tail⟩
  · exact .interior (.frame ⟨⟨_, input.atPoint, input.related⟩, source.frame, realized⟩)
  · obtain ⟨fuel, firstStep⟩ := runtimeStep_demandInstructionStep first
    have same := firstStep.deterministic (addressStep fuel)
    have currentEq : current = middle := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
    subst current
    rcases tail.uncons with ⟨rfl, rfl⟩ | ⟨remaining, snapshot, rfl, snapshotStep, tail⟩
    · apply DemandPrefixDecomposition.interior
      apply IndexAssignmentPrefixCursor.frame
      exact ⟨⟨_, addressPost.pp, addressPost.rel⟩, source.frame, by simpa only [RetainedSsaMap.Realizes, destinationWorld, middle] using addressed⟩
    · obtain ⟨sample, aliases, child, viewed, childCanonical, viewQuery, viewPost, progress⟩ :=
        accepted_generated_index_expression_prefix destination form selected destinationOwner destinationOccurrence destinationRows
          coverage destinationAdmitted bounded destinationRealized destinationInput placed addressPost addressed placeExtended snapshotStep indexFamily tail
      have baseCoverage : (map.addRuns (lowerView (.of owner) le before).1 aliases).Covers map := by
        constructor
        · intro cell member; exact member
        · intro cell member; exact List.mem_append_right _ member
      cases progress with
      | interior demanded =>
        obtain ⟨typing, roots, future, frame⟩ := demanded.frame
        have carried := baseCoverage.realizes demanded.carried
        exact .interior (.frame ⟨frame.builder, by simpa only [childCanonical.world, destinationWorld] using frame.source,
          by simpa only [RetainedSsaMap.Realizes, childCanonical.world, destinationWorld] using carried⟩)
      | @complete indexFuel indexCount left boundary indexValue count indexTrace residual indexDone indexBoundary =>
        rcases residual.uncons with ⟨rfl, rfl⟩ | ⟨remaining, afterCheck, rfl, checkStep, rest⟩
        · apply DemandPrefixDecomposition.interior
          apply IndexAssignmentPrefixCursor.frame
          have carried := baseCoverage.realizes indexBoundary.demanded.operands
          exact ⟨indexBoundary.demanded.builder,
            by simpa only [childCanonical.world, destinationWorld] using indexBoundary.demanded.source,
            by simpa only [RetainedSsaMap.Realizes, childCanonical.world, destinationWorld] using carried⟩
        · let common := max 2 indexFuel
          have viewed' : evalView common cfg env (.of owner) state = .ok sample snapshot.state :=
            ((monoAll 2 common (by dsimp [common]; exact Nat.le_max_left _ _)).view cfg env (.of owner) state).1 _ _ viewed
          have indexed' : evalExpr common cfg env index snapshot.state = .ok indexValue boundary.state :=
            ((monoAll indexFuel common (by dsimp [common]; exact Nat.le_max_right _ _)).expr cfg env index snapshot.state).1 _ _ indexDone
          have indexRealized : (map.addRuns (lowerView (.of owner) le before).1 aliases).Realizes
              cfg.mod source.world env ⟨boundary.point, boundary.frame, boundary.state⟩ := by
            simpa only [RetainedSsaMap.Realizes, childCanonical.world, destinationWorld] using indexBoundary.demanded.operands
          have query : source.rootsEnv.access.aliasView (source.path ++ [0, 0]) (.of owner) = .ok aliases := by
            simpa only [destinationRoots, destinationAt.path, List.append_assoc, List.singleton_append] using viewQuery
          have suffix := accepted_generated_index_assignment_store_prefix source form occurrence rows coverage admitted query viewed' indexed'
            viewPost indexBoundary.post indexBoundary.bounded indexRealized bounded realized input extended
            (fun child childAt => target source child childAt) selected owned valueFamily checkStep rest
          cases suffix with
          | interior cursor => exact .interior (.value cursor)
          | @complete statementFuel consumed remaining endPoint flow suffixCount suffixTrace suffixRest evaluated finalPost =>
            exact .complete (consumed := indexCount + consumed + 2) (by omega)
              (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                (DemandRuntimePrefix.next first (DemandRuntimePrefix.next snapshotStep (indexTrace.append suffixTrace))))
              suffixRest evaluated finalPost

theorem IndexAssignmentPrefixCursor.realizes {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : IndexAssignmentPrefixCursor cx results source before built initial start map required runtime) :
    map.Realizes cfg.mod source.world env runtime := by
  cases cursor with
  | frame frame => exact frame.operands
  | value cursor => exact cursor.realizes

#print axioms IndexAssignmentPrefixCursor.realizes
#print axioms accepted_generated_index_assignment_prefix
end Goose.Lower
