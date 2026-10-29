import Goose.Lower.DemandSliceAssignmentDestination
import Goose.Lower.DemandSliceAssignmentValuePrefix
import Goose.Lower.DemandSliceAssignmentLiteralPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound Goose.Evidence

inductive SliceAssignmentInterior {cfg : Cfg} {env : Env} {state : St}
    {reference : Expr} {mutability : Mutability} {global : GlobalId} {sliceOrigin origin : OriginId}
    {intType : IntTy} {number : Int}
    (source : StmtSource cfg env (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) state)
    (cx : FnCtx) (results : List Ty) (before : LS) (map : RetainedSsaMap) : DemandRuntimePoint → Prop
  | destination {runtime : DemandRuntimePoint}
      (child : PlaceSource cfg env (.deref reference) state) (canonical : source.PlaceChildAt child rfl)
      (demanded : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.inputFuture
        map.values map.runs runtime) (progress : ∃ next, ∀ fuel, DemandInstructionStep cx fuel runtime next)
      (instruction : ∃ id op, instAt cx.fn runtime.point = some (.def id op)) :
      SliceAssignmentInterior source cx results before map runtime
  | value {runtime : DemandRuntimePoint} (alias : RetainedAlias)
      (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state)
      (canonical : source.AssignmentValueAt child)
      (demanded : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.inputFuture
        (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).values
        (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).runs runtime)
      (progress : ∃ next, ∀ fuel, DemandInstructionStep cx fuel runtime next) :
      SliceAssignmentInterior source cx results before map runtime
  | view {runtime : DemandRuntimePoint} (alias : RetainedAlias)
      (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state)
      (canonical : source.AssignmentValueAt child) (view : ViewSource cfg env (.of (.global global)) state)
      (viewAt : child.ViewChildAt view 0 rfl)
      (demanded : DemandFrameAt cfg env cx view.world view.typingEnv view.rootsEnv view.context.inputFuture
        (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).values
        (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).runs runtime)
      (instruction : ∃ id op, instAt cx.fn runtime.point = some (.def id op)) :
      SliceAssignmentInterior source cx results before map runtime
  | viewDone {runtime : DemandRuntimePoint} (alias : RetainedAlias)
      (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state)
      (canonical : source.AssignmentValueAt child) (view : ViewSource cfg env (.of (.global global)) state)
      (viewAt : child.ViewChildAt view 0 rfl)
      (demanded : DemandFrameAt cfg env cx view.world view.typingEnv view.rootsEnv view.context.outputFuture
        (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).values
        (map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).runs runtime)
      (progress : ∃ next, ∀ fuel, DemandInstructionStep cx fuel runtime next) :
      SliceAssignmentInterior source cx results before map runtime
  | bound {runtime : DemandRuntimePoint} {sampledState : St} (alias : RetainedAlias) (aliases : List RetainedAlias)
      (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state)
      (canonical : source.AssignmentValueAt child) (upper : BoundSource cfg env (.expr (.lit intType number)) sampledState)
      (upperAt : child.BoundChildAt upper 2 rfl)
      (demanded : DemandFrameAt cfg env cx upper.world upper.typingEnv upper.rootsEnv upper.context.outputFuture
        ((map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).addRuns
          (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 aliases).values
        ((map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).addRuns
          (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 aliases).runs runtime)
      (instruction : ∃ id op, instAt cx.fn runtime.point = some (.def id op)) :
      SliceAssignmentInterior source cx results before map runtime
  | store {runtime : DemandRuntimePoint} (alias : RetainedAlias) (aliases : List RetainedAlias)
      (child : ExprSource cfg env (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) state)
      (canonical : source.AssignmentValueAt child)
      (demanded : DemandFrameAt cfg env cx child.world child.typingEnv child.rootsEnv child.context.outputFuture
        ((map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).addRuns
          (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 aliases).values
        ((map.addValues (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).1 [alias]).addRuns
          (lowerView (.of (.global global)) (lowerEnv cfg.mod env.vars results)
            (lowerPlace (.deref reference) (lowerEnv cfg.mod env.vars results) before).2).1 aliases).runs runtime)
      (instruction : ∃ effect, instAt cx.fn runtime.point = some (.eff effect)) :
      SliceAssignmentInterior source cx results before map runtime

theorem SliceAssignmentInterior.realizes {cfg : Cfg} {env : Env} {state : St}
    {reference : Expr} {mutability : Mutability} {global : GlobalId} {sliceOrigin origin : OriginId}
    {intType : IntTy} {number : Int}
    {source : StmtSource cfg env (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) state}
    {cx : FnCtx} {results : List Ty} {before : LS} {map : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : SliceAssignmentInterior source cx results before map runtime) : map.Realizes cfg.mod source.world env runtime := by
  have valueCoverage (id : ValueId) (aliases : List RetainedAlias) : (map.addValues id aliases).Covers map := by
    constructor
    · intro cell member
      exact List.mem_append_right _ member
    · intro cell member
      exact member
  have runCoverage (id run : ValueId) (aliases runs : List RetainedAlias) :
      ((map.addValues id aliases).addRuns run runs).Covers map := by
    constructor
    · intro cell member
      exact List.mem_append_right _ member
    · intro cell member
      exact List.mem_append_right _ member
  cases cursor with
  | destination child canonical demanded progress instruction => simpa only [RetainedSsaMap.Realizes, canonical.world] using demanded.operands
  | value alias child canonical demanded progress =>
    simpa only [canonical.world] using (valueCoverage _ _).realizes demanded.operands
  | view alias child canonical view viewAt demanded instruction =>
    simpa only [canonical.world, viewAt.world] using (valueCoverage _ _).realizes demanded.operands
  | viewDone alias child canonical view viewAt demanded progress =>
    simpa only [canonical.world, viewAt.world] using (valueCoverage _ _).realizes demanded.operands
  | bound alias aliases child canonical upper upperAt demanded instruction =>
    simpa only [canonical.world, upperAt.world] using (runCoverage _ _ _ _).realizes demanded.operands
  | store alias aliases child canonical demanded instruction =>
    simpa only [canonical.world] using (runCoverage _ _ _ _).realizes demanded.operands

#print axioms SliceAssignmentInterior.realizes

theorem SliceAssignmentInterior.instruction {cfg : Cfg} {env : Env} {state : St}
    {reference : Expr} {mutability : Mutability} {global : GlobalId} {sliceOrigin origin : OriginId}
    {intType : IntTy} {number : Int}
    {source : StmtSource cfg env (.assign (.deref reference)
      (.slice mutability (.of (.global global)) .omitted (.expr (.lit intType number)) sliceOrigin) origin) state}
    {cx : FnCtx} {results : List Ty} {before : LS} {map : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : SliceAssignmentInterior source cx results before map runtime) :
    ∃ instruction, instAt cx.fn runtime.point = some instruction := by
  cases cursor with
  | destination child canonical demanded progress instruction =>
    obtain ⟨id, op, found⟩ := instruction
    exact ⟨_, found⟩
  | value alias child canonical demanded progress =>
    obtain ⟨next, step⟩ := progress
    cases step 0 with
    | definition instruction execution => exact ⟨_, instruction⟩
    | effect instruction execution => exact ⟨_, instruction⟩
    | control instruction execution => exact ⟨_, instruction⟩
  | view alias child canonical view viewAt demanded instruction =>
    obtain ⟨id, op, instruction⟩ := instruction
    exact ⟨_, instruction⟩
  | viewDone alias child canonical view viewAt demanded progress =>
    obtain ⟨next, step⟩ := progress
    cases step 0 with
    | definition instruction execution => exact ⟨_, instruction⟩
    | effect instruction execution => exact ⟨_, instruction⟩
    | control instruction execution => exact ⟨_, instruction⟩
  | bound alias aliases child canonical upper upperAt demanded instruction =>
    obtain ⟨id, op, instruction⟩ := instruction
    exact ⟨_, instruction⟩
  | store alias aliases child canonical demanded instruction =>
    obtain ⟨effect, instruction⟩ := instruction
    exact ⟨_, instruction⟩

#print axioms SliceAssignmentInterior.instruction

theorem accepted_generated_slice_assignment_prefix {cfg : Cfg} {env : Env} {state : St}
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

    {taken : Nat} {reached : DemandRuntimePoint}
    (steps : DemandRuntimePrefix cx taken ⟨start, initial, state⟩ reached) :
    GeneratedStatementPrefixDecomposition source selected occurrence rows map initial start
      (SliceAssignmentInterior source cx results before map) taken reached := by
  by_cases short : taken < 2
  · obtain ⟨destination, canonical, demanded, progress⟩ :=
      accepted_generated_slice_assignment_destination_prefix source slice selected owned occurrence rows coverage admitted bounded realized input extended short steps
    have instruction := accepted_generated_slice_assignment_destination_instruction source slice selected owned occurrence rows coverage admitted bounded
      realized input extended short steps
    exact ⟨owned, coverage, .interior (.destination destination canonical demanded progress instruction)⟩
  · by_cases atTwo : taken = 2
    · obtain ⟨point, frame, alias, child, canonical, remaining, count, residual, demanded, progress⟩ :=
        accepted_generated_slice_assignment_value_entry_split source slice selected owned occurrence rows coverage admitted bounded realized input extended (by omega) steps
      have zero : remaining = 0 := by omega
      subst remaining
      cases residual
      exact ⟨owned, coverage, .interior (.value alias child canonical demanded ⟨_, progress⟩)⟩
    · by_cases atThree : taken = 3
      · obtain ⟨point, frame, alias, child, view, canonical, viewAt, executed, ⟨remaining, count, residual⟩, demanded, instruction⟩ :=
          accepted_generated_slice_assignment_snapshot_split source slice selected owned occurrence rows coverage admitted bounded realized input extended (by omega) steps
        have zero : remaining = 0 := by omega
        subst remaining
        cases residual
        exact ⟨owned, coverage, .interior (.view alias child canonical view viewAt demanded instruction)⟩
      · by_cases atFour : taken = 4
        · obtain ⟨point, frame, after, alias, child, view, canonical, viewAt, remaining, count, residual, demanded, progress⟩ :=
            accepted_generated_slice_assignment_snapshot_result_split source slice selected owned occurrence rows coverage admitted bounded realized input extended (by omega) steps
          have zero : remaining = 0 := by omega
          subst remaining
          cases residual
          exact ⟨owned, coverage, .interior (.viewDone alias child canonical view viewAt demanded ⟨_, progress⟩)⟩
        · by_cases atFive : taken = 5
          · obtain ⟨point, frame, after, alias, aliases, child, upper, canonical, upperAt, remaining, count, residual, demanded, instruction⟩ :=
              accepted_generated_slice_assignment_literal_split source slice selected owned occurrence rows coverage admitted bounded realized input extended (by omega) steps
            have zero : remaining = 0 := by omega
            subst remaining
            cases residual
            exact ⟨owned, coverage, .interior (.bound alias aliases child canonical upper upperAt demanded instruction)⟩
          · by_cases atSix : taken = 6
            · obtain ⟨destinationFrame, point, frame, after, alias, aliases, value, child, canonical, remaining, count, residual, evaluated, site, boundary⟩ :=
                accepted_generated_slice_assignment_store_split source slice selected owned occurrence rows coverage admitted bounded realized input extended (by omega) steps
              have zero : remaining = 0 := by omega
              subst remaining
              cases residual
              exact ⟨owned, coverage, .interior (.store alias aliases child canonical boundary.demanded ⟨_, site.instruction⟩)⟩
            · exact accepted_generated_slice_assignment_completed_prefix source slice selected owned occurrence rows coverage admitted bounded realized input extended
                (SliceAssignmentInterior source cx results before map) (by omega) steps

#print axioms accepted_generated_slice_assignment_prefix
end Goose.Lower
