import Goose.Lower.DemandGeneratedAssignment
import Goose.Lower.DemandGeneratedOwner
import Goose.Lower.SourceContexts

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

theorem accepted_generated_assignment_children {cfg : Cfg} {env : Env} {state : St}
    {place : Place} {value : Expr} {origin : OriginId}
    (source : StmtSource cfg env (.assign place value origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.assign place value origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required) :
    ∃ destination : PlaceSource cfg env place state,
      destination.typingEnv = source.typingEnv ∧ destination.rootsEnv = source.rootsEnv ∧
      source.PlaceChildAt destination rfl ∧ GeneratedSourceOwner selected destination.context ∧
      ∃ destinationOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
          root destination.path (.place place) before,
        GeneratedDemandRows cfg.mod destination.rootsEnv.access destinationOccurrence required ∧
        ∀ fuel location after, evalPlace fuel cfg env place state = .ok location after →
          ∀ aliases, source.rootsEnv.access.aliasPlace (source.path ++ [0]) place = .ok aliases →
          ∃ child : ExprSource cfg env value after,
            child.typingEnv = source.typingEnv ∧ child.rootsEnv = source.rootsEnv ∧ child.ty = destination.ty ∧
            source.AssignmentValueAt child ∧ GeneratedSourceOwner selected child.context ∧
            ∃ valueOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
                root child.path (.expression value) (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2,
              GeneratedDemandRows cfg.mod child.rootsEnv.access valueOccurrence
                (required.addValues (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1 aliases) := by
  obtain ⟨destination, typing, roots, world, observation, canonical, next⟩ := source.assignChildrenDemand
  have destinationOwner : GeneratedSourceOwner selected destination.context :=
    (owned.child rfl 0 (.place place) .place rfl (by trivial)).transport
      canonical.plans.symm canonical.path.symm rfl canonical.context.symm
  have destinationOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root destination.path (.place place) before := by
    rw [canonical.path]
    exact .assignmentPlace occurrence
  have destinationRows : GeneratedDemandRows cfg.mod destination.rootsEnv.access destinationOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.assignmentPlace occurrence) required :=
      .assignmentPlace rows
    simpa only [roots, canonical.path] using inherited
  refine ⟨destination, typing, roots, canonical, destinationOwner, destinationOccurrence, destinationRows, ?_⟩
  intro fuel location after placed aliases query
  obtain ⟨child, childTyping, childRoots, childWorld, childObservation, childType, childAt⟩ := next fuel location after placed
  have childOwner : GeneratedSourceOwner selected child.context :=
    (owned.child rfl 1 (.expression value) .expression rfl (by trivial)).transport
      childAt.plans.symm childAt.path.symm rfl childAt.context.symm
  have valueOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root child.path (.expression value) (lowerPlace place (lowerEnv cfg.mod env.vars results) before).2 := by
    rw [childAt.path]
    exact .assignmentValue occurrence
  have valueRows : GeneratedDemandRows cfg.mod child.rootsEnv.access valueOccurrence
      (required.addValues (lowerPlace place (lowerEnv cfg.mod env.vars results) before).1 aliases) := by
    have inherited := GeneratedDemandRows.assignmentValue rows query
    simpa only [childRoots, childAt.path] using inherited
  exact ⟨child, childTyping, childRoots, childType, childAt, childOwner, valueOccurrence, valueRows⟩

#print axioms StmtSource.assignChildrenDemand
#print axioms accepted_generated_assignment_children

end Goose.Lower
