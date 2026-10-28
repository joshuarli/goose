import Goose.Lower.DemandSliceAssignmentStore

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_slice_assignment_path {cfg : Cfg} {env : Env} {state : St}
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
    ∃ (destinationPoint : Pt) (destinationFrame : GIR.Frame),
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
      ∀ (finalPoint : Pt) (finalFrame : GIR.Frame) (after : St),
      RuntimeStep cx.cfg cx.fn slicePoint sliceFrame sliceState finalPoint finalFrame after →
      DemandRuntimePrefix cx 7 ⟨start, initial, state⟩ ⟨finalPoint, finalFrame, after⟩ ∧
      execStmt 4 cfg env (.assign (.deref reference)
        (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) state = .ok (.normal .unit) after ∧
      StmtResult source (.normal .unit) after ∧
      DemandFrameAt cfg env cx source.world source.typingAfter source.rootsEnv source.context.outputFuture
        map.values map.runs ⟨finalPoint, finalFrame, after⟩ := by
  obtain ⟨location, destinationPoint, destinationFrame, alias, destination, canonical, placed, destinationSteps,
    traversal, destinationPost, query, child, childTyping, childRoots, childAt, childOwner, valueOccurrence, valueRows, valueCoverage,
    valueBounded, valueAdmitted, valueRealized, valueInput⟩ :=
    accepted_generated_slice_assignment_entry source slice selected owned occurrence rows coverage admitted bounded realized input extended
  refine ⟨destinationPoint, destinationFrame, destinationSteps, ?_⟩
  intro snapshotPoint snapshotFrame sampledState snapshot slicePoint sliceFrame sliceState sliceStep finalPoint finalFrame after store
  obtain ⟨rhsSteps, done, post, result, demanded⟩ := accepted_generated_slice_assignment_store source child childAt occurrence rows admitted bounded realized
    placed destinationPost query childTyping childRoots valueRows valueCoverage valueAdmitted valueBounded valueRealized extended snapshot sliceStep store
  exact ⟨destinationSteps.append rhsSteps, done, result, demanded⟩

#print axioms accepted_generated_slice_assignment_path
end Goose.Lower
