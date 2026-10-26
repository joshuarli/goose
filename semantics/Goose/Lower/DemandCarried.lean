import Goose.Lower.DemandAssignment

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

structure RetainedSsaMap where
  values : List (ValueId × RetainedAlias)
  runs : List (ValueId × RetainedAlias)

def RetainedSsaMap.Admitted (map : RetainedSsaMap) (profile : ArtifactProfile) (retained : List RetainedAlias) : Prop :=
  profile = .shrink → ∀ alias ∈ map.values.map Prod.snd ++ map.runs.map Prod.snd, alias ∈ retained

def RetainedSsaMap.Bounded (map : RetainedSsaMap) (frontier : ValueId) : Prop :=
  (∀ cell ∈ map.values, cell.1 < frontier) ∧ (∀ cell ∈ map.runs, cell.1 < frontier)

def RetainedSsaMap.Realizes (map : RetainedSsaMap) (m : Core.Module) (world : World) (env : Env)
    (point : DemandRuntimePoint) : Prop :=
  RetainedOperandsAt m world env point.state.store point.frame map.values map.runs

theorem RetainedSsaMap.Bounded.mono {map : RetainedSsaMap} {before after : ValueId}
    (bounded : map.Bounded before) (larger : before ≤ after) : map.Bounded after :=
  ⟨fun cell member => Nat.lt_of_lt_of_le (bounded.1 cell member) larger,
    fun cell member => Nat.lt_of_lt_of_le (bounded.2 cell member) larger⟩

theorem retainedAliases_of_storeLe {m : Core.Module} {world : World} {env : Env}
    {before after : Store} (growth : Goose.Proofs.Memory.StoreLe before after)
    (aliases : List RetainedAlias) : RetainsAliases m world env before after aliases := by
  intro alias member
  constructor
  · intro value realized
    exact ⟨HasTy.mono growth realized.1, realized.2⟩
  · intro mutability element capacity location start length typeEq realized typed
    exact SliceTy.mono growth typed

theorem accepted_literal_assignment_carried_traversal {cfg : Cfg} {env : Env} {state : St}
    {varId : VarId} {type : IntTy} {number : Int} {origin : OriginId}
    (source : StmtSource cfg env (.assign (.var varId) (.lit type number) origin) state)
    {cx : FnCtx} {ls ls' : LS} {pt : Pt} {frame : GIR.Frame} {loop : Option LoopCtx}
    {results : List Ty} (map : RetainedSsaMap)
    (admitted : map.Admitted cfg.mod.profile source.context.retained) (bounded : map.Bounded ls.vals.size)
    (realized : map.Realizes cfg.mod source.world env ⟨pt, frame, state⟩)
    (lowered : lowerStmt loop (.assign (.var varId) (.lit type number) origin)
      (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (point : ls.pp = some pt) (extended : ExtT ls' cx.fn.blocks)
    (related : Rel cfg env cx frame ls) :
    ∃ (after : St) (address value : ValueId) (alias : RetainedAlias)
        (finalPoint : Pt) (finalFrame : GIR.Frame),
      execStmt 2 cfg env (.assign (.var varId) (.lit type number) origin) state =
        .ok (.normal .unit) after ∧
      DemandUniformTraversal cx
        (fun point => LiteralAssignmentDemand source cx address alias pt point ∧
          map.Realizes cfg.mod source.world env point) 3
        ⟨pt, frame, state⟩ ⟨finalPoint, finalFrame, after⟩ ∧
      finalFrame.vals[value]? = some (.val (.int type number)) ∧
      ls'.pp = some finalPoint ∧ Rel cfg env cx finalFrame ls' := by
  obtain ⟨after, address, value, alias, finalPoint, finalFrame, done, _, _, traversal,
    valueAt, finalPointAt, finalRelated⟩ :=
    accepted_literal_assignment_execution_traversal source lowered point extended related
  have result := source.result 2 (.normal .unit) done
  refine ⟨after, address, value, alias, finalPoint, finalFrame, done, ?_, valueAt, finalPointAt, finalRelated⟩
  apply traversal.mono
  intro runtime valid
  refine ⟨valid.1, ?_⟩
  rcases valid.2.2 with before | afterEq
  · change RetainedOperandsAt cfg.mod source.world env runtime.state.store runtime.frame map.values map.runs
    rw [before]
    exact realized.retained valid.2.1 bounded.1 bounded.2 RetainsAliases.refl
  · change RetainedOperandsAt cfg.mod source.world env runtime.state.store runtime.frame map.values map.runs
    rw [afterEq]
    have retention : RetainsAliases cfg.mod source.world env state.store after.store
        (map.values.map Prod.snd ++ map.runs.map Prod.snd) := by
      cases profileEq : cfg.mod.profile with
      | pilot => exact retainedAliases_of_storeLe (result.pilotStore profileEq) _
      | shrink => exact result.aliases.subset (admitted profileEq)
    exact realized.retained valid.2.1 bounded.1 bounded.2 retention

end Goose.Lower
