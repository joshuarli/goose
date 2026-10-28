import Goose.Lower.DemandSliceAssignmentEntry
import Goose.Lower.DemandSliceGlobalLiteral
import Goose.Lower.DemandAssignmentStore

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_slice_assignment_store {cfg : Cfg} {env : Env} {state sampledState sliceState after : St}
    {reference : Expr} {mutability : Mutability} {global : GlobalId} {sliceOrigin origin : OriginId}
    (source : StmtSource cfg env (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin) state)
    (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) state)
    (childAt : source.AssignmentValueAt child)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.assign (.deref reference)
        (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained) (bounded : map.Bounded before.vals.size)
    {initial destinationFrame : GIR.Frame} {start destinationPoint : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {location : Loc} (placed : evalPlace 3 cfg env (.deref reference) state = .ok location state)
    (destinationPost : Post cfg env cx before initial (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2
      destinationFrame destinationPoint [((lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    {alias : RetainedAlias} (query : source.rootsEnv.access.aliasPlace (source.path ++ [0]) (.deref reference) = .ok [alias])
    (childTyping : child.typingEnv = source.typingEnv) (childRoots : child.rootsEnv = source.rootsEnv)
    {valueOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root child.path
      (.expression (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin))
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
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {snapshotPoint : Pt} {snapshotFrame : GIR.Frame}
    (snapshot : RuntimeStep cx.cfg cx.fn (destinationPoint.1, destinationPoint.2 + 1)
      (destinationFrame.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results)
        (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 (.val (.ref ⟨.global global, []⟩)))
      state snapshotPoint snapshotFrame sampledState)
    {slicePoint : Pt} {sliceFrame : GIR.Frame}
    (sliceStep : RuntimeStep cx.cfg cx.fn (snapshotPoint.1, snapshotPoint.2 + 1)
      (snapshotFrame.set (lowerExpr (.lit .i64 0) (lowerEnv cfg.mod env.vars results)
        (sliceUpperBefore (.of (.global global)) .omitted (lowerEnv cfg.mod env.vars results)
          (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2)).1 (.val (.int .i64 0)))
      sampledState slicePoint sliceFrame sliceState)
    {finalPoint : Pt} {finalFrame : GIR.Frame}
    (store : RuntimeStep cx.cfg cx.fn slicePoint sliceFrame sliceState finalPoint finalFrame after) :
    DemandRuntimePrefix cx 5 ⟨destinationPoint, destinationFrame, state⟩ ⟨finalPoint, finalFrame, after⟩ ∧
    execStmt 4 cfg env (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin) state = .ok (.normal .unit) after ∧
    Post cfg env cx before initial (lowerStmt loop (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin)
      (lowerEnv cfg.mod env.vars results) before).2 finalFrame finalPoint [] ∧
    StmtResult source (.normal .unit) after ∧
    DemandFrameAt cfg env cx source.world source.typingAfter source.rootsEnv source.context.outputFuture
      map.values map.runs ⟨finalPoint, finalFrame, after⟩ := by
  let le := lowerEnv cfg.mod env.vars results
  let destination := lowerPlace (.deref reference) le before
  let value := Expr.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin
  have valueExtended := generated_assignment_value_extended extended
  obtain ⟨sample, view, canonical, firstStep, viewed, viewPost, viewDemand, viewRetained⟩ :=
    accepted_generated_slice_global_snapshot child valueOccurrence valueRows valueCoverage valueBounded
      destinationPost.pp destinationPost.rel valueRealized valueExtended snapshot
  obtain ⟨aliases, upper, viewQuery, literalStep, operands, upperRows, upperCoverage, upperAt, upperAdmitted, upperBounded, upperPost, upperDemand⟩ :=
    accepted_generated_slice_global_literal_bound child valueOccurrence valueRows valueCoverage valueAdmitted valueBounded
      valueRealized viewed viewPost valueExtended
  obtain ⟨result, evaluated, valuePost⟩ :=
    accepted_generated_slice_global_literal_step child valueOccurrence valueRows valueCoverage valueAdmitted valueBounded
      valueRealized viewed viewPost valueExtended sliceStep
  have combined := destinationPost.comp valuePost
  have site : GeneratedAssignmentStoreSite cfg.mod source.rootsEnv.access cx.fn le root source.path before loop
      (.deref reference) value origin required slicePoint :=
    ⟨occurrence, rows, ⟨[alias], query⟩, combined.pp, extended⟩
  obtain ⟨pointEq, frameEq, done, post, resultSource, finalBounded, demanded⟩ :=
    accepted_generated_assignment_store_step source site admitted bounded realized placed evaluated combined store
  have lastStep : DemandRuntimePrefix cx 1 ⟨slicePoint, sliceFrame, sliceState⟩ ⟨finalPoint, finalFrame, after⟩ :=
    .next store (.zero _)
  have sliceAndStore : DemandRuntimePrefix cx 2
      ⟨(snapshotPoint.1, snapshotPoint.2 + 1), snapshotFrame.set
        (lowerExpr (.lit .i64 0) le (sliceUpperBefore (.of (.global global)) .omitted le destination.2)).1
          (.val (.int .i64 0)), sampledState⟩ ⟨finalPoint, finalFrame, after⟩ :=
    .next sliceStep lastStep
  exact ⟨.next ((firstStep 0).runtime) (.next snapshot (.next ((literalStep 0).runtime) sliceAndStore)),
    done, post, resultSource, demanded⟩

theorem accepted_generated_slice_assignment_snapshot_stop {cfg : Cfg} {env : Env} {state after : St}
    {reference : Expr} {mutability : Mutability} {global : GlobalId} {sliceOrigin origin : OriginId}
    (source : StmtSource cfg env (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin) state)
    (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    {required : RetainedSsaMap} {initial destinationFrame : GIR.Frame} {destinationPoint : Pt}
    {location : Loc} (placed : evalPlace 3 cfg env (.deref reference) state = .ok location state)
    (destinationPost : Post cfg env cx before initial (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2
      destinationFrame destinationPoint [((lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    {valueOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root child.path
      (.expression (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin))
      (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2}
    (valueRows : GeneratedDemandRows cfg.mod child.rootsEnv.access valueOccurrence required)
    (extended : ExtT (lowerStmt loop (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {targetFuel : Nat} {stop : Stop}
    (stopped : DemandInstructionStop cx targetFuel
      ⟨(destinationPoint.1, destinationPoint.2 + 1),
        destinationFrame.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results)
          (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1
            (.val (.ref ⟨.global global, []⟩)), state⟩ stop after) (nonTimeout : stop ≠ .timeout) :
    DemandRuntimePrefix cx 1 ⟨destinationPoint, destinationFrame, state⟩
      ⟨(destinationPoint.1, destinationPoint.2 + 1),
        destinationFrame.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results)
          (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1
            (.val (.ref ⟨.global global, []⟩)), state⟩ ∧
    execStmt 4 cfg env (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin) state = .stop stop after := by
  obtain ⟨first, sourceStop⟩ := accepted_generated_slice_global_snapshot_stop child valueOccurrence valueRows
    destinationPost.pp destinationPost.rel (generated_assignment_value_extended extended) stopped nonTimeout
  exact ⟨.next ((first 0).runtime) (.zero _), by simpa only [execStmt, bind_apply, placed, sourceStop] using sourceStop⟩

#print axioms accepted_generated_slice_assignment_snapshot_stop

theorem accepted_generated_slice_assignment_slice_stop {cfg : Cfg} {env : Env} {state sampledState sliceState after : St}
    {reference : Expr} {mutability : Mutability} {global : GlobalId} {sliceOrigin origin : OriginId}
    (source : StmtSource cfg env (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin) state)
    (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) state)
    (childAt : source.AssignmentValueAt child)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.assign (.deref reference)
        (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained) (bounded : map.Bounded before.vals.size)
    {initial destinationFrame : GIR.Frame} {start destinationPoint : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {location : Loc} (placed : evalPlace 3 cfg env (.deref reference) state = .ok location state)
    (destinationPost : Post cfg env cx before initial (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2
      destinationFrame destinationPoint [((lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    {alias : RetainedAlias} (query : source.rootsEnv.access.aliasPlace (source.path ++ [0]) (.deref reference) = .ok [alias])
    (childTyping : child.typingEnv = source.typingEnv) (childRoots : child.rootsEnv = source.rootsEnv)
    {valueOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root child.path
      (.expression (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin))
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
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {snapshotPoint : Pt} {snapshotFrame : GIR.Frame}
    (snapshot : RuntimeStep cx.cfg cx.fn (destinationPoint.1, destinationPoint.2 + 1)
      (destinationFrame.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results)
        (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 (.val (.ref ⟨.global global, []⟩)))
      state snapshotPoint snapshotFrame sampledState)
    {targetFuel : Nat} {stop : Stop}
    (stopped : DemandInstructionStop cx targetFuel
      ⟨(snapshotPoint.1, snapshotPoint.2 + 1),
        snapshotFrame.set (lowerExpr (.lit .i64 0) (lowerEnv cfg.mod env.vars results)
          (sliceUpperBefore (.of (.global global)) .omitted (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2)).1 (.val (.int .i64 0)),
        sampledState⟩ stop after) (nonTimeout : stop ≠ .timeout) :
    DemandRuntimePrefix cx 3 ⟨destinationPoint, destinationFrame, state⟩
      ⟨(snapshotPoint.1, snapshotPoint.2 + 1),
        snapshotFrame.set (lowerExpr (.lit .i64 0) (lowerEnv cfg.mod env.vars results)
          (sliceUpperBefore (.of (.global global)) .omitted (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2)).1 (.val (.int .i64 0)),
        sampledState⟩ ∧
    execStmt 4 cfg env (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin) state = .stop stop after := by
  have valueExtended := generated_assignment_value_extended extended
  obtain ⟨sample, view, canonical, firstStep, viewed, viewPost, viewDemand, viewRetained⟩ :=
    accepted_generated_slice_global_snapshot child valueOccurrence valueRows valueCoverage valueBounded
      destinationPost.pp destinationPost.rel valueRealized valueExtended snapshot
  obtain ⟨aliases, upper, viewQuery, literalStep, operands, upperRows, upperCoverage, upperAt, upperAdmitted, upperBounded, upperPost, upperDemand⟩ :=
    accepted_generated_slice_global_literal_bound child valueOccurrence valueRows valueCoverage valueAdmitted valueBounded
      valueRealized viewed viewPost valueExtended
  have sourceStop := accepted_generated_slice_global_literal_stop child valueOccurrence valueRows valueCoverage valueAdmitted valueBounded
      valueRealized viewed viewPost valueExtended stopped nonTimeout
  constructor
  · exact .next ((firstStep 0).runtime) (.next snapshot (.next ((literalStep 0).runtime) (.zero _)))
  · simpa only [execStmt, bind_apply, placed, sourceStop] using sourceStop

#print axioms accepted_generated_slice_assignment_slice_stop

theorem accepted_generated_slice_assignment_store_stop {cfg : Cfg} {env : Env} {state sampledState sliceState after : St}
    {reference : Expr} {mutability : Mutability} {global : GlobalId} {sliceOrigin origin : OriginId}
    (source : StmtSource cfg env (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin) state)
    (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) state)
    (childAt : source.AssignmentValueAt child)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS} {loop : Option LoopCtx}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.statement loop (.assign (.deref reference)
        (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin)) before)
    {required map : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    (admitted : map.Admitted cfg.mod.profile source.context.retained) (bounded : map.Bounded before.vals.size)
    {initial destinationFrame : GIR.Frame} {start destinationPoint : Pt}
    (realized : map.Realizes cfg.mod source.world env ⟨start, initial, state⟩)
    {location : Loc} (placed : evalPlace 3 cfg env (.deref reference) state = .ok location state)
    (destinationPost : Post cfg env cx before initial (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2
      destinationFrame destinationPoint [((lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1, .val (.ref location))])
    {alias : RetainedAlias} (query : source.rootsEnv.access.aliasPlace (source.path ++ [0]) (.deref reference) = .ok [alias])
    (childTyping : child.typingEnv = source.typingEnv) (childRoots : child.rootsEnv = source.rootsEnv)
    {valueOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root child.path
      (.expression (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin))
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
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)
    {snapshotPoint : Pt} {snapshotFrame : GIR.Frame}
    (snapshot : RuntimeStep cx.cfg cx.fn (destinationPoint.1, destinationPoint.2 + 1)
      (destinationFrame.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results)
        (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 (.val (.ref ⟨.global global, []⟩)))
      state snapshotPoint snapshotFrame sampledState)
    {slicePoint : Pt} {sliceFrame : GIR.Frame}
    (sliceStep : RuntimeStep cx.cfg cx.fn (snapshotPoint.1, snapshotPoint.2 + 1)
      (snapshotFrame.set (lowerExpr (.lit .i64 0) (lowerEnv cfg.mod env.vars results)
        (sliceUpperBefore (.of (.global global)) .omitted (lowerEnv cfg.mod env.vars results)
          (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2)).1 (.val (.int .i64 0)))
      sampledState slicePoint sliceFrame sliceState)
    {targetFuel : Nat} {stop : Stop}
    (stopped : DemandInstructionStop cx targetFuel ⟨slicePoint, sliceFrame, sliceState⟩ stop after)
    (nonTimeout : stop ≠ .timeout) :
    DemandRuntimePrefix cx 4 ⟨destinationPoint, destinationFrame, state⟩ ⟨slicePoint, sliceFrame, sliceState⟩ ∧
    execStmt 4 cfg env (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin) origin) state = .stop stop after := by
  let le := lowerEnv cfg.mod env.vars results
  let value := Expr.slice mutability (.of (.global global)) .omitted (.expr (.lit .i64 0)) sliceOrigin
  have valueExtended := generated_assignment_value_extended extended
  obtain ⟨sample, view, canonical, firstStep, viewed, viewPost, viewDemand, viewRetained⟩ :=
    accepted_generated_slice_global_snapshot child valueOccurrence valueRows valueCoverage valueBounded
      destinationPost.pp destinationPost.rel valueRealized valueExtended snapshot
  obtain ⟨aliases, upper, viewQuery, literalStep, operands, upperRows, upperCoverage, upperAt, upperAdmitted, upperBounded, upperPost, upperDemand⟩ :=
    accepted_generated_slice_global_literal_bound child valueOccurrence valueRows valueCoverage valueAdmitted valueBounded
      valueRealized viewed viewPost valueExtended
  obtain ⟨result, evaluated, valuePost⟩ :=
    accepted_generated_slice_global_literal_step child valueOccurrence valueRows valueCoverage valueAdmitted valueBounded
      valueRealized viewed viewPost valueExtended sliceStep
  have combined := destinationPost.comp valuePost
  have site : GeneratedAssignmentStoreSite cfg.mod source.rootsEnv.access cx.fn le root source.path before loop
      (.deref reference) value origin required slicePoint :=
    ⟨occurrence, rows, ⟨[alias], query⟩, combined.pp, extended⟩
  have sourceStop := accepted_generated_assignment_store_stop source site placed evaluated combined stopped nonTimeout
  have lastStep : DemandRuntimePrefix cx 1
      ⟨(snapshotPoint.1, snapshotPoint.2 + 1), snapshotFrame.set
        (lowerExpr (.lit .i64 0) le (sliceUpperBefore (.of (.global global)) .omitted le
          (lowerPlace (.deref reference) le before).2)).1 (.val (.int .i64 0)), sampledState⟩
      ⟨slicePoint, sliceFrame, sliceState⟩ := .next sliceStep (.zero _)
  exact ⟨.next ((firstStep 0).runtime) (.next snapshot (.next ((literalStep 0).runtime) lastStep)), sourceStop⟩

#print axioms accepted_generated_slice_assignment_store_stop

#print axioms accepted_generated_slice_assignment_store
end Goose.Lower
