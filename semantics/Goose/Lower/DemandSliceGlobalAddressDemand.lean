import Goose.Lower.DemandSliceGlobalSnapshot
import Goose.Lower.DemandSliceAssignmentEntry

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

theorem accepted_generated_slice_global_address_demand {cfg : Cfg} {env : Env} {state : St}
    {mutability : Mutability} {global : GlobalId} {lower upper : Bound} {origin : OriginId}
    (source : ExprSource cfg env (.slice mutability (.of (.global global)) lower upper origin) state)
    {cx : FnCtx} {results : List Ty} {root : DemandNode} {before : LS}
    (occurrence : GeneratedDemandOccurrence cfg.mod cx.fn (lowerEnv cfg.mod env.vars results)
      root source.path (.expression (.slice mutability (.of (.global global)) lower upper origin)) before)
    {required : RetainedSsaMap} (rows : GeneratedDemandRows cfg.mod source.rootsEnv.access occurrence required)
    {map : RetainedSsaMap} (bounded : map.Bounded before.vals.size)
    {initial : GIR.Frame} {point : Pt} (realized : map.Realizes cfg.mod source.world env ⟨point, initial, state⟩) (atPoint : before.pp = some point) (related : Rel cfg env cx initial before)
    (extended : ExtT (lowerExpr (.slice mutability (.of (.global global)) lower upper origin)
      (lowerEnv cfg.mod env.vars results) before).2 cx.fn.blocks) :
    ∃ (view : ViewSource cfg env (.of (.global global)) state), source.ViewChildAt view 0 rfl ∧
      DemandFrameAt cfg env cx view.world view.typingEnv view.rootsEnv view.context.inputFuture map.values map.runs
        ⟨(point.1, point.2 + 1), initial.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1
          (.val (.ref ⟨.global global, []⟩)), state⟩ ∧
      ∀ fuel, DemandInstructionStep cx fuel ⟨point, initial, state⟩
        ⟨(point.1, point.2 + 1), initial.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1
          (.val (.ref ⟨.global global, []⟩)), state⟩ := by
  obtain ⟨view, canonical, occurrence, rows, placed, post, step⟩ :=
    accepted_generated_slice_global_address source occurrence rows atPoint related extended
  have retained := realized.retained post.same bounded.1 bounded.2 RetainsAliases.refl
  have carried : map.Realizes cfg.mod view.world env
      ⟨(point.1, point.2 + 1), initial.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results) before).1
        (.val (.ref ⟨.global global, []⟩)), state⟩ := by
    simpa only [RetainedSsaMap.Realizes, canonical.world] using retained
  exact ⟨view, canonical, ⟨⟨_, post.pp, post.rel⟩, view.frame, carried⟩, step⟩

#print axioms accepted_generated_slice_global_address_demand
theorem accepted_generated_slice_assignment_snapshot_cursor {cfg : Cfg} {env : Env} {state : St}
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
      (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state)
      (view : ViewSource cfg env (.of (.global global)) state),
      source.AssignmentValueAt child ∧ child.ViewChildAt view 0 rfl ∧
      DemandRuntimePrefix cx 3 ⟨start, initial, state⟩
        ⟨(destinationPoint.1, destinationPoint.2 + 1),
          destinationFrame.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1
              (.val (.ref ⟨.global global, []⟩)), state⟩ ∧
      DemandFrameAt cfg env cx view.world view.typingEnv view.rootsEnv view.context.inputFuture
        (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).values
        (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).runs
        ⟨(destinationPoint.1, destinationPoint.2 + 1),
          destinationFrame.set (lowerPlace (.global global) (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1
              (.val (.ref ⟨.global global, []⟩)), state⟩ := by
  obtain ⟨location, destinationPoint, destinationFrame, alias, destination, canonical, placed, destinationSteps,
    traversal, destinationPost, query, child, childTyping, childRoots, childAt, childOwner, valueOccurrence, valueRows, valueCoverage,
    valueBounded, valueAdmitted, valueRealized, valueInput⟩ :=
    accepted_generated_slice_assignment_entry source slice selected owned occurrence rows coverage admitted bounded realized input extended
  obtain ⟨view, viewAt, demanded, step⟩ :=
    accepted_generated_slice_global_address_demand child valueOccurrence valueRows valueBounded valueRealized
      destinationPost.pp destinationPost.rel (generated_assignment_value_extended extended)
  exact ⟨destinationPoint, destinationFrame, alias, child, view, childAt, viewAt,
    destinationSteps.append (.next ((step 0).runtime) (.zero _)), demanded⟩

#print axioms accepted_generated_slice_assignment_snapshot_cursor
end Goose.Lower
