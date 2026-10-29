import Goose.Lower.DemandSliceGlobalAddressDemand

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_slice_assignment_value_entry_split {cfg : Cfg} {env : Env} {state : St}
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

    {taken : Nat} {reached : DemandRuntimePoint} (enough : 2 ≤ taken)
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    ∃ (destinationPoint : Pt) (destinationFrame : GIR.Frame) (alias : RetainedAlias)
      (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state),
      source.AssignmentValueAt child ∧
      ∃ remaining, taken = 2 + remaining ∧
      DemandRuntimePrefix cx remaining ⟨destinationPoint, destinationFrame, state⟩ reached ∧
      DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.inputFuture
        (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).values
        (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).runs
        ⟨destinationPoint, destinationFrame, state⟩ ∧
      (∀ fuel, DemandInstructionStep cx fuel ⟨destinationPoint, destinationFrame, state⟩
        ⟨(destinationPoint.1, destinationPoint.2 + 1),
          destinationFrame.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1
              (.val (.ref ⟨.global global, []⟩)), state⟩) ∧
      ∃ id op, instAt cx.fn destinationPoint = some (.def id op) := by
  obtain ⟨location, destinationPoint, destinationFrame, alias, destination, canonical, placed, destinationSteps,
    traversal, destinationPost, query, child, childTyping, childRoots, childAt, childOwner, valueOccurrence, valueRows, valueCoverage,
    valueBounded, valueAdmitted, valueRealized, valueInput⟩ :=
    accepted_generated_slice_assignment_entry source slice selected owned occurrence rows coverage admitted bounded realized input extended
  obtain ⟨view, viewAt, viewOccurrence, viewRows, globalPlace, globalPost, step⟩ :=
    accepted_generated_slice_global_address child valueOccurrence valueRows destinationPost.pp destinationPost.rel
      (generated_assignment_value_extended extended)
  let le := lowerEnv cfg.mod env.vars results
  let valueBefore := (lowerPlace (.deref reference) le before).2
  have globalExtended : ExtT (lowerPlace (.global global) le valueBefore).2 cx.fn.blocks :=
    generated_view_place_extended (generated_slice_view_extended (generated_assignment_value_extended extended))
  have emitted : emitDef (.globalAddr global) le valueBefore =
      ((lowerPlace (.global global) le valueBefore).1, (lowerPlace (.global global) le valueBefore).2) := rfl
  obtain ⟨_, instruction⟩ := Post.def_leaf (Post.init destinationPost.rel destinationPost.pp) emitted globalExtended
    (.val (.ref ⟨.global global, []⟩))
  obtain ⟨remaining, count, residual⟩ := destinationSteps.split_at enough steps
  exact ⟨destinationPoint, destinationFrame, alias, child, childAt, remaining, count, residual,
    ⟨⟨_, valueInput.atPoint, valueInput.related⟩, child.frame, valueRealized⟩, step, ⟨_, _, instruction⟩⟩

#print axioms accepted_generated_slice_assignment_value_entry_split
end Goose.Lower
