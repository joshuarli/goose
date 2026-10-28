import Goose.Lower.DemandSliceAssignmentLiteralPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_slice_assignment_snapshot_result_split {cfg : Cfg} {env : Env} {state : St}
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

    {taken : Nat} {reached : DemandRuntimePoint} (enough : 4 ≤ taken)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    ∃ (snapshotPoint : Pt) (snapshotFrame : GIR.Frame) (sampledState : St)
      (alias : RetainedAlias)
      (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state)
      (view : ViewSource cfg env (.of (.global global)) state),
      source.AssignmentValueAt child ∧ child.ViewChildAt view 0 rfl ∧
      ∃ remaining, taken = 4 + remaining ∧ DemandRuntimePrefix cx remaining ⟨snapshotPoint, snapshotFrame, sampledState⟩ reached ∧
      DemandFrameAt cfg env cx view.world view.typingEnv view.rootsEnv view.context.outputFuture
        (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).values
        (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).runs
        ⟨snapshotPoint, snapshotFrame, sampledState⟩ ∧
      ∀ fuel, DemandInstructionStep cx fuel ⟨snapshotPoint, snapshotFrame, sampledState⟩
        ⟨(snapshotPoint.1, snapshotPoint.2 + 1),
          snapshotFrame.set (lowerExpr (.lit intType number) (lowerEnv cfg.mod env.vars results)
            (sliceUpperBefore (.of (.global global)) .omitted (lowerEnv cfg.mod env.vars results)
              (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2)).1 (.val (.int intType number)), sampledState⟩ := by
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
      exact ⟨snapshotPoint, snapshotFrame, sampledState, alias, child, view, childAt, canonical,
        rest, by omega, tail, viewDemand, literalStep⟩

#print axioms accepted_generated_slice_assignment_snapshot_result_split
end Goose.Lower
