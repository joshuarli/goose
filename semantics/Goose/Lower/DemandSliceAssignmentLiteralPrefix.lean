import Goose.Lower.DemandSliceAssignmentSnapshotPrefix
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
      (∃ id op, instAt cx.fn (snapshotPoint.1, snapshotPoint.2 + 1) = some (.def id op)) ∧
      (∀ {targetFuel : Nat} {stop : Stop} {after : St},
        DemandInstructionStop cx targetFuel
          ⟨(snapshotPoint.1, snapshotPoint.2 + 1),
            snapshotFrame.set (lowerExpr (.lit intType number) (lowerEnv cfg.mod env.vars results)
              (sliceUpperBefore (.of (.global global)) .omitted (lowerEnv cfg.mod env.vars results)
                (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2)).1 (.val (.int intType number)), sampledState⟩ stop after →
        stop ≠ .timeout → execStmt 4 cfg env (.assign (.deref reference)
          (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) state = .stop stop after) ∧
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
        value sliceState slicePoint sliceFrame ∧
      (∀ {targetFuel : Nat} {stop : Stop} {after : St},
        DemandInstructionStop cx targetFuel ⟨slicePoint, sliceFrame, sliceState⟩ stop after → stop ≠ .timeout →
        execStmt 4 cfg env (.assign (.deref reference)
          (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) state = .stop stop after) ∧
      ∀ (finalPoint : Pt) (finalFrame : GIR.Frame) (after : St),
      RuntimeStep cx.cfg cx.fn slicePoint sliceFrame sliceState finalPoint finalFrame after →
      DemandRuntimePrefix cx 7 ⟨start, initial, state⟩ ⟨finalPoint, finalFrame, after⟩ ∧
      execStmt 4 cfg env (.assign (.deref reference)
        (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) state = .ok (.normal .unit) after ∧
      Post cfg env cx before initial (lowerStmt loop (.assign (.deref reference)
        (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin)
        (lowerEnv cfg.mod env.vars results) before).2 finalFrame finalPoint [] ∧
      StmtResult source (.normal .unit) after ∧
      map.Bounded (lowerStmt loop (.assign (.deref reference)
        (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin)
        (lowerEnv cfg.mod env.vars results) before).2.vals.size ∧
      DemandFrameAt cfg env cx source.world source.typingAfter source.rootsEnv source.context.outputFuture
        map.values map.runs ⟨finalPoint, finalFrame, after⟩ := by
  obtain ⟨snapshotPoint, snapshotFrame, sampledState, alias, child, view, childAt, viewAt,
    rest, count, tail, demanded, next, instruction, longer⟩ :=
    accepted_generated_slice_assignment_snapshot_stage source slice selected owned occurrence rows coverage admitted bounded realized input extended (by omega) steps
  exact longer enough

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
              (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2)).1 (.val (.int intType number)), sampledState⟩ ∧
      ∃ id op, instAt cx.fn (snapshotPoint.1, snapshotPoint.2 + 1) = some (.def id op) := by
  obtain ⟨snapshotPoint, snapshotFrame, sampledState, alias, aliases, child, upper, childAt, upperAt,
    suffix, count, suffixSteps, upperDemand, instruction, sliceStopped, next⟩ :=
    accepted_generated_slice_assignment_literal_stage source slice selected owned occurrence rows coverage admitted bounded realized input extended enough steps
  exact ⟨snapshotPoint, snapshotFrame, sampledState, alias, aliases, child, upper, childAt, upperAt,
    suffix, count, suffixSteps, upperDemand, instruction⟩
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
    suffix, count, suffixSteps, upperDemand, instruction, sliceStopped, next⟩ :=
    accepted_generated_slice_assignment_literal_stage source slice selected owned occurrence rows coverage admitted bounded realized input extended (by omega) steps
  rcases suffixSteps.uncons with ⟨empty, _⟩ | ⟨restCount, sliceEnd, countSlice, sliceStep, remainingSteps⟩
  · omega
  · cases sliceEnd with
    | mk slicePoint sliceFrame sliceState =>
      obtain ⟨destinationFrame, runAliases, value, evaluated, site, boundary, storeStopped, complete⟩ :=
        next slicePoint sliceFrame sliceState sliceStep
      exact ⟨destinationFrame, slicePoint, sliceFrame, sliceState, alias, runAliases, value, child, childAt,
        restCount, by omega, remainingSteps, evaluated, site, boundary⟩

#print axioms accepted_generated_slice_assignment_store_split
theorem accepted_generated_slice_assignment_completed_prefix {cfg : Cfg} {env : Env} {state : St}
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

    (cursor : DemandRuntimePoint → Prop)
    {taken : Nat} {reached : DemandRuntimePoint} (enough : 7 ≤ taken)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    GeneratedStatementPrefixDecomposition source selected occurrence rows map initial start cursor taken reached := by
  obtain ⟨snapshotPoint, snapshotFrame, sampledState, alias, aliases, child, upper, childAt, upperAt,
    suffix, count, suffixSteps, upperDemand, instruction, sliceStopped, next⟩ :=
    accepted_generated_slice_assignment_literal_stage source slice selected owned occurrence rows coverage admitted bounded realized input extended (by omega) steps
  rcases suffixSteps.uncons with ⟨empty, _⟩ | ⟨restCount, sliceEnd, countSlice, sliceStep, remainingSteps⟩
  · omega
  · cases sliceEnd with
    | mk slicePoint sliceFrame sliceState =>
      obtain ⟨destinationFrame, runAliases, value, evaluated, site, boundary, storeStopped, complete⟩ :=
        next slicePoint sliceFrame sliceState sliceStep
      rcases remainingSteps.uncons with ⟨empty, _⟩ | ⟨finalCount, final, countFinal, store, residual⟩
      · omega
      · cases final with
        | mk finalPoint finalFrame after =>
          obtain ⟨executed, done, post, result, finalBounded, finalDemand⟩ := complete finalPoint finalFrame after store
          have prepared : (execStmt 4 cfg env (.assign (.deref reference)
              (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) >>= prepareLoopFlow env loop) state =
                .ok (.normal .unit) after := by
            simp only [bind_apply, done]
            cases loop <;> rfl
          exact ⟨owned, coverage, .complete (by omega) executed residual prepared
            (.normal post result finalBounded finalDemand.operands)⟩

#print axioms accepted_generated_slice_assignment_completed_prefix
end Goose.Lower
