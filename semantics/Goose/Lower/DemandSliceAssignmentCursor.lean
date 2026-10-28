import Goose.Lower.DemandSliceAssignmentStore

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_slice_assignment_store_cursor {cfg : Cfg} {env : Env} {state sampledState sliceState : St}
    {reference : Expr} {mutability : Mutability} {global : GlobalId} {sliceOrigin origin : OriginId}
    {intType : IntTy} {number : Int}
    (source : StmtSource cfg env (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) state)
    (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.assign (.deref reference)
        (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {initial destinationFrame : GIR.Frame} {destinationPoint : Pt}
    {location : Loc}
    (destinationPost : Post cfg env cx before initial (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2
      destinationFrame destinationPoint [((lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    {alias : RetainedAlias} (query : source.rootsEnv.access.aliasPlace (source.path ++ [0]) (.deref reference) = .ok [alias])
    {valueOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root child.path
      (.expression (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin))
      (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2}
    (valueRows : GeneratedDemandRows cfg.mod child.rootsEnv.access valueOccurrence
      (required.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]))
    (valueCoverage : (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).Covers
      (required.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]))
    (valueAdmitted : (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).Admitted
      cfg.mod.profile child.context.retained)
    (valueBounded : (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).Bounded
      (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2.vals.size)
    (valueRealized : (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).Realizes
      cfg.mod child.world env ⟨destinationPoint, destinationFrame, state⟩)
    (extended : ExtT (lowerStmt loop (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {snapshotPoint : Pt} {snapshotFrame : GIR.Frame}
    (snapshot : RuntimeStep cx.cfg cx.fn (destinationPoint.1, destinationPoint.2 + 1)
      (destinationFrame.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results)
        (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 (.val (.ref ⟨.global global, []⟩)))
      state snapshotPoint snapshotFrame sampledState)
    {slicePoint : Pt} {sliceFrame : GIR.Frame}
    (sliceStep : RuntimeStep cx.cfg cx.fn (snapshotPoint.1, snapshotPoint.2 + 1)
      (snapshotFrame.set (lowerExpr (.lit intType number) (lowerEnv cfg.mod env.vars results)
        (sliceUpperBefore (.of (.global global)) .omitted (lowerEnv cfg.mod env.vars results)
          (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2)).1 (.val (.int intType number)))
      sampledState slicePoint sliceFrame sliceState)
 :
    ∃ (aliases : List RetainedAlias) (value : Val),
      DemandRuntimePrefix cx 4 ⟨destinationPoint, destinationFrame, state⟩ ⟨slicePoint, sliceFrame, sliceState⟩ ∧
      evalExpr 3 cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state = .ok value sliceState ∧
      GeneratedAssignmentStoreSite cfg.mod source.rootsEnv.access cx.fn (lowerEnv cfg.mod env.vars results) root source.path before loop
        (.deref reference) (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin required slicePoint ∧
      ExpressionDemandBoundary child
        ((map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).addRuns
          (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 aliases)
        cx (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2 destinationFrame
        (lowerExpr (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin)
          (lowerEnv cfg.mod env.vars results) (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).2
        (lowerExpr (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin)
          (lowerEnv cfg.mod env.vars results) (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1
        value sliceState slicePoint sliceFrame := by
  let le := lowerEnv cfg.mod env.vars results
  let value := Expr.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin
  have valueExtended := generated_assignment_value_extended extended
  obtain ⟨sample, view, canonical, firstStep, viewed, viewPost, viewDemand, viewRetained⟩ :=
    accepted_generated_slice_global_snapshot child valueOccurrence valueRows valueCoverage valueBounded
      destinationPost.pp destinationPost.rel valueRealized valueExtended snapshot
  obtain ⟨aliases, upper, viewQuery, literalStep, operands, upperRows, upperCoverage, upperAt, upperAdmitted, upperBounded, upperPost, upperDemand⟩ :=
    accepted_generated_slice_global_literal_bound child valueOccurrence valueRows valueCoverage valueAdmitted valueBounded
      valueRealized viewed viewPost valueExtended
  obtain ⟨retained, result, evaluated, boundary⟩ :=
    accepted_generated_slice_global_literal_boundary child valueOccurrence valueRows valueCoverage valueAdmitted valueBounded
      valueRealized viewed viewPost valueExtended sliceStep
  have combined := destinationPost.comp boundary.post
  have site : GeneratedAssignmentStoreSite cfg.mod source.rootsEnv.access cx.fn le root source.path before loop
      (.deref reference) value origin required slicePoint :=
    ⟨occurrence, rows, ⟨[alias], query⟩, combined.pp, extended⟩
  exact ⟨retained, result, .next ((firstStep 0).runtime) (.next snapshot (.next ((literalStep 0).runtime) (.next sliceStep (.zero _)))), evaluated, site, boundary⟩

#print axioms accepted_generated_slice_assignment_store_cursor
theorem accepted_generated_slice_assignment_entry_store_cursor {cfg : Cfg} {env : Env} {state : St}
    {reference : Expr} {mutability : Mutability} {global : GlobalId} {sliceOrigin origin : OriginId}
    {intType : IntTy} {number : Int}
    (source : StmtSource cfg env (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) state)
    {ty : Ty} (slice : sliceRefTy source.typingEnv reference = some ty)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {owner : Nat} {before : LS} {loop : Option LoopCtx}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (owned : GeneratedSourceOwner selected source.context)
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.assign (.deref reference)
        (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (coverage : map.Covers required) (admitted : map.Admitted cfg.mod.profile source.context.retained)
    (bounded : map.Bounded before.vals.size) {initial : GIR.Frame} {start : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    (input : GeneratedPrefixInput cfg env cx results loop source.typingEnv source.rootsEnv before initial start)
    (extended : ExtT (lowerStmt loop (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (destinationPoint : Pt) (destinationFrame : GIR.Frame) (alias : RetainedAlias)
      (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state),
      source.AssignmentValueAt child ∧
      DemandRuntimePrefix cx 2 ⟨start, initial, state⟩ ⟨destinationPoint, destinationFrame, state⟩ ∧
      ∀ (snapshotPoint : Pt) (snapshotFrame : GIR.Frame) (sampledState : St),
      RuntimeStep cx.cfg cx.fn (destinationPoint.1, destinationPoint.2 + 1)
        (destinationFrame.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results)
          (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 (.val (.ref ⟨.global global, []⟩)))
        state snapshotPoint snapshotFrame sampledState →
      ∀ (slicePoint : Pt) (sliceFrame : GIR.Frame) (sliceState : St),
      RuntimeStep cx.cfg cx.fn (snapshotPoint.1, snapshotPoint.2 + 1)
        (snapshotFrame.set (lowerExpr (.lit intType number) (lowerEnv cfg.mod env.vars results)
          (sliceUpperBefore (.of (.global global)) .omitted (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2)).1 (.val (.int intType number)))
        sampledState slicePoint sliceFrame sliceState →
    ∃ (aliases : List RetainedAlias) (value : Val),
      DemandRuntimePrefix cx 6 ⟨start, initial, state⟩ ⟨slicePoint, sliceFrame, sliceState⟩ ∧
      evalExpr 3 cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state = .ok value sliceState ∧
      GeneratedAssignmentStoreSite cfg.mod source.rootsEnv.access cx.fn (lowerEnv cfg.mod env.vars results) root source.path before loop
        (.deref reference) (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin required slicePoint ∧
      ExpressionDemandBoundary child
        ((map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).addRuns
          (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 aliases)
        cx (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2 destinationFrame
        (lowerExpr (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin)
          (lowerEnv cfg.mod env.vars results) (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).2
        (lowerExpr (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin)
          (lowerEnv cfg.mod env.vars results) (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1
        value sliceState slicePoint sliceFrame := by
  obtain ⟨location, destinationPoint, destinationFrame, alias, destination, canonical, placed, destinationSteps,
    traversal, destinationPost, query, child, childTyping, childRoots, childAt, childOwner, valueOccurrence, valueRows, valueCoverage,
    valueBounded, valueAdmitted, valueRealized, valueInput⟩ :=
    accepted_generated_slice_assignment_entry source slice selected owned occurrence rows coverage admitted bounded realized input extended
  refine ⟨destinationPoint, destinationFrame, alias, child, childAt, destinationSteps, ?_⟩
  intro snapshotPoint snapshotFrame sampledState snapshot slicePoint sliceFrame sliceState sliceStep
  obtain ⟨aliases, value, rhsSteps, evaluated, site, boundary⟩ :=
    accepted_generated_slice_assignment_store_cursor source child occurrence rows destinationPost query valueRows valueCoverage
      valueAdmitted valueBounded valueRealized extended snapshot sliceStep
  exact ⟨aliases, value, destinationSteps.append rhsSteps, evaluated, site, boundary⟩

#print axioms accepted_generated_slice_assignment_entry_store_cursor
end Goose.Lower
