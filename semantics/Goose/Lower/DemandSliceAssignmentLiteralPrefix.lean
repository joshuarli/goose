import Goose.Lower.DemandSliceGlobalAddressDemand
import Goose.Lower.DemandSliceGlobalLiteral
import Goose.Lower.DemandSliceAssignmentCursor

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_slice_assignment_literal_stage {cfg : Cfg} {env : Env} {state : St}
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
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)

    {taken : Nat} {reached : DemandRuntimePoint} (enough : 5 ≤ taken)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    ∃ (snapshotPoint : Pt) (snapshotFrame : GIR.Frame) (sampledState : St)
      (alias : RetainedAlias) (aliases : List RetainedAlias)
      (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state)
      (upper : BoundSource cfg env (.expr (.lit intType number)) sampledState),
      source.AssignmentValueAt child ∧ child.BoundChildAt upper 2 rfl ∧
      ∃ remaining, taken = 5 + remaining ∧
      DemandRuntimePrefix cx remaining
        ⟨(snapshotPoint.1, snapshotPoint.2 + 1),
          snapshotFrame.set (lowerExpr (.lit intType number) (lowerEnv cfg.mod env.vars results)
            (sliceUpperBefore (.of (.global global)) .omitted (lowerEnv cfg.mod env.vars results)
              (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2)).1 (.val (.int intType number)), sampledState⟩ reached ∧
      DemandFrameAt cfg env cx upper.world upper.typingEnv upper.rootsEnv upper.context.outputFuture
        ((map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).addRuns
          (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 aliases).values
        ((map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).addRuns
          (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 aliases).runs
        ⟨(snapshotPoint.1, snapshotPoint.2 + 1),
          snapshotFrame.set (lowerExpr (.lit intType number) (lowerEnv cfg.mod env.vars results)
            (sliceUpperBefore (.of (.global global)) .omitted (lowerEnv cfg.mod env.vars results)
              (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2)).1 (.val (.int intType number)), sampledState⟩ ∧
      ∀ (slicePoint : Pt) (sliceFrame : GIR.Frame) (sliceState : St),
      RuntimeStep cx.cfg cx.fn (snapshotPoint.1, snapshotPoint.2 + 1)
        (snapshotFrame.set (lowerExpr (.lit intType number) (lowerEnv cfg.mod env.vars results)
          (sliceUpperBefore (.of (.global global)) .omitted (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2)).1 (.val (.int intType number)))
        sampledState slicePoint sliceFrame sliceState →
      ∃ (destinationFrame : GIR.Frame) (runAliases : List RetainedAlias) (value : Val),
      evalExpr 3 cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state = .ok value sliceState ∧
      GeneratedAssignmentStoreSite cfg.mod source.rootsEnv.access cx.fn (lowerEnv cfg.mod env.vars results) root source.path before loop
        (.deref reference) (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin required slicePoint ∧
      ExpressionDemandBoundary child
        ((map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).addRuns
          (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 runAliases)
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
  obtain ⟨view, viewAt, viewOccurrence, viewRows, globalPlace, globalPost, addressStep⟩ :=
    accepted_generated_slice_global_address child valueOccurrence valueRows destinationPost.pp destinationPost.rel
      (generated_assignment_value_extended extended)
  have throughAddress := destinationSteps.append (.next ((addressStep 0).runtime) (.zero _))
  obtain ⟨remaining, count, residual⟩ := throughAddress.split_at (by omega) steps
  rcases residual.uncons with ⟨empty, _⟩ | ⟨rest, next, countNext, snapshot, tail⟩
  · omega
  · cases next with
    | mk snapshotPoint snapshotFrame sampledState =>
      obtain ⟨sample, view, canonical, firstStep, viewed, viewPost, viewDemand, viewRetained⟩ :=
        accepted_generated_slice_global_snapshot child valueOccurrence valueRows valueCoverage valueBounded
          destinationPost.pp destinationPost.rel valueRealized (generated_assignment_value_extended extended) snapshot
      obtain ⟨aliases, upper, viewQuery, literalStep, operands, upperRows, upperCoverage, upperAt, upperAdmitted, upperBounded, upperPost, upperDemand⟩ :=
        accepted_generated_slice_global_literal_bound child valueOccurrence valueRows valueCoverage valueAdmitted valueBounded
          valueRealized viewed viewPost (generated_assignment_value_extended extended)
      have literalPrefix : DemandRuntimePrefix cx 1 _ _ := .next ((literalStep 0).runtime) (.zero _)
      obtain ⟨suffix, suffixCount, suffixSteps⟩ := literalPrefix.split_at (by omega) tail
      refine ⟨snapshotPoint, snapshotFrame, sampledState, alias, aliases, child, upper, childAt, upperAt,
        suffix, by omega, suffixSteps, upperDemand, ?_⟩
      intro slicePoint sliceFrame sliceState sliceStep
      obtain ⟨runAliases, value, rhsSteps, evaluated, site, boundary⟩ :=
        accepted_generated_slice_assignment_store_cursor source child occurrence rows destinationPost query valueRows valueCoverage
          valueAdmitted valueBounded valueRealized extended snapshot sliceStep
      exact ⟨destinationFrame, runAliases, value, evaluated, site, boundary⟩


#print axioms accepted_generated_slice_assignment_literal_stage

theorem accepted_generated_slice_assignment_literal_split {cfg : Cfg} {env : Env} {state : St}
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
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)

    {taken : Nat} {reached : DemandRuntimePoint} (enough : 5 ≤ taken)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    ∃ (snapshotPoint : Pt) (snapshotFrame : GIR.Frame) (sampledState : St)
      (alias : RetainedAlias) (aliases : List RetainedAlias)
      (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state)
      (upper : BoundSource cfg env (.expr (.lit intType number)) sampledState),
      source.AssignmentValueAt child ∧ child.BoundChildAt upper 2 rfl ∧
      ∃ remaining, taken = 5 + remaining ∧
      DemandRuntimePrefix cx remaining
        ⟨(snapshotPoint.1, snapshotPoint.2 + 1),
          snapshotFrame.set (lowerExpr (.lit intType number) (lowerEnv cfg.mod env.vars results)
            (sliceUpperBefore (.of (.global global)) .omitted (lowerEnv cfg.mod env.vars results)
              (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2)).1 (.val (.int intType number)), sampledState⟩ reached ∧
      DemandFrameAt cfg env cx upper.world upper.typingEnv upper.rootsEnv upper.context.outputFuture
        ((map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).addRuns
          (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 aliases).values
        ((map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).addRuns
          (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 aliases).runs
        ⟨(snapshotPoint.1, snapshotPoint.2 + 1),
          snapshotFrame.set (lowerExpr (.lit intType number) (lowerEnv cfg.mod env.vars results)
            (sliceUpperBefore (.of (.global global)) .omitted (lowerEnv cfg.mod env.vars results)
              (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2)).1 (.val (.int intType number)), sampledState⟩ := by
  obtain ⟨snapshotPoint, snapshotFrame, sampledState, alias, aliases, child, upper, childAt, upperAt,
    suffix, count, suffixSteps, upperDemand, next⟩ :=
    accepted_generated_slice_assignment_literal_stage source slice selected owned occurrence rows coverage admitted bounded realized input extended enough steps
  exact ⟨snapshotPoint, snapshotFrame, sampledState, alias, aliases, child, upper, childAt, upperAt,
    suffix, count, suffixSteps, upperDemand⟩
#print axioms accepted_generated_slice_assignment_literal_split
theorem accepted_generated_slice_assignment_store_split {cfg : Cfg} {env : Env} {state : St}
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
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks)

    {taken : Nat} {reached : DemandRuntimePoint} (enough : 6 ≤ taken)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    ∃ (destinationFrame : GIR.Frame) (slicePoint : Pt) (sliceFrame : GIR.Frame) (sliceState : St)
      (alias : RetainedAlias) (aliases : List RetainedAlias) (value : Val)
      (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state),
      source.AssignmentValueAt child ∧
      ∃ remaining, taken = 6 + remaining ∧ DemandRuntimePrefix cx remaining ⟨slicePoint, sliceFrame, sliceState⟩ reached ∧
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
  obtain ⟨snapshotPoint, snapshotFrame, sampledState, alias, aliases, child, upper, childAt, upperAt,
    suffix, count, suffixSteps, upperDemand, next⟩ :=
    accepted_generated_slice_assignment_literal_stage source slice selected owned occurrence rows coverage admitted bounded realized input extended (by omega) steps
  rcases suffixSteps.uncons with ⟨empty, _⟩ | ⟨restCount, sliceEnd, countSlice, sliceStep, remainingSteps⟩
  · omega
  · cases sliceEnd with
    | mk slicePoint sliceFrame sliceState =>
      obtain ⟨destinationFrame, runAliases, value, evaluated, site, boundary⟩ :=
        next slicePoint sliceFrame sliceState sliceStep
      exact ⟨destinationFrame, slicePoint, sliceFrame, sliceState, alias, runAliases, value, child, childAt,
        restCount, by omega, remainingSteps, evaluated, site, boundary⟩

#print axioms accepted_generated_slice_assignment_store_split
end Goose.Lower
