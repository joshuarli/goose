import Goose.Lower.DemandSliceReferencePlace
import Goose.Lower.DemandAssignmentScalarAlias

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_slice_assignment_entry {cfg : Cfg} {env : Env} {state : St}
    {reference value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign (.deref reference) value origin) state)
    {ty : Ty} (slice : sliceRefTy source.typingEnv reference = some ty)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.assign (.deref reference) value origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerStmt loop (.assign (.deref reference) value origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (location : Loc) (point : Pt) (frame : GIR.Frame) (alias : RetainedAlias)
      (destination : PlaceSource cfg env (.deref reference) state),
      let le := lowerEnv cfg.mod env.vars results
      let id := (lowerPlace (.deref reference) le before).1
      source.PlaceChildAt destination rfl ∧
      evalPlace 3 cfg env (.deref reference) state = .ok location state ∧
      DemandRuntimePrefix cx 2 ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      DemandUniformTraversal cx (DemandFrameAt cfg env cx destination.world destination.typingEnv destination.rootsEnv
        destination.context.inputFuture map.values map.runs) 2 ⟨start, initial, state⟩ ⟨point, frame, state⟩ ∧
      Post cfg env cx before initial (lowerPlace (.deref reference) le before).2 frame point [(id, .val (.ref location))] ∧
      source.rootsEnv.access.aliasPlace (source.path ++ [0]) (.deref reference) = .ok [alias] ∧
      ∃ child : ExprSource cfg env value state,
        child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧
        source.AssignmentValueAt child ∧ GeneratedSourceOwner selected child.context ∧
        ∃ valueOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.expression value)
            (lowerPlace (.deref reference) le before).2,
        GeneratedDemandRows cfg.mod child.rootsEnv.access valueOccurrence (required.addValues id [alias]) ∧
        (map.addValues id [alias]).Covers (required.addValues id [alias]) ∧
        (map.addValues id [alias]).Bounded (lowerPlace (.deref reference) le before).2.vals.size ∧
        (map.addValues id [alias]).Admitted cfg.mod.profile child.context.retained ∧
        (map.addValues id [alias]).Realizes cfg.mod child.world env ⟨point, frame, state⟩ ∧
        GeneratedPrefixInput cfg env cx results loop child.typingEnv child.rootsEnv
          (lowerPlace (.deref reference) le before).2 frame point := by
  obtain ⟨destination, typing, roots, canonical, destinationOwner, destinationOccurrence, destinationRows, next⟩ :=
    accepted_generated_assignment_children source selected owned occurrence rows
  have destinationSlice : sliceRefTy destination.typingEnv reference = some ty := by simpa only [typing] using slice
  have destinationRealized : map.Realizes cfg.mod destination.world env ⟨start, initial, state⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using realized
  obtain ⟨location, point, frame, alias, placed, steps, traversal, post, query, retained⟩ :=
    accepted_generated_slice_reference_retained destination destinationSlice (source.path ++ [0]) input.atPoint input.related
      map bounded destinationRealized (generated_assignment_place_extended extended)
  have sourceQuery : source.rootsEnv.access.aliasPlace (source.path ++ [0]) (.deref reference) = .ok [alias] := by
    simpa only [roots] using query
  obtain ⟨child, childTyping, childRoots, childType, childAt, childOwner, valueOccurrence, valueRows⟩ :=
    next 3 location state placed [alias] sourceQuery
  have sourceRetained : (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).Realizes
      cfg.mod source.world env ⟨point, frame, state⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using retained
  obtain ⟨nextCoverage, nextBounded, nextAdmitted, nextRealized, nextInput⟩ :=
    accepted_assignment_value_demand_of_retained source child childAt childTyping childRoots coverage admitted
      (bounded.mono post.mono) input post sourceQuery sourceRetained
  exact ⟨location, point, frame, alias, destination, canonical, placed, steps, traversal, post, sourceQuery,
    child, childTyping, childRoots, childAt, childOwner, valueOccurrence, valueRows, nextCoverage, nextBounded, nextAdmitted, nextRealized, nextInput⟩

#print axioms accepted_generated_slice_assignment_entry
end Goose.Lower
