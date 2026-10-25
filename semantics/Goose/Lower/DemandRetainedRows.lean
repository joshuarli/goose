import Goose.Lower.DemandCarried

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

def RetainedSsaMap.Covers (map required : RetainedSsaMap) : Prop :=
  (∀ cell ∈ required.values, cell ∈ map.values) ∧ (∀ cell ∈ required.runs, cell ∈ map.runs)

def RetainedSsaMap.withValue (map : RetainedSsaMap) (id : ValueId) (alias : RetainedAlias) : RetainedSsaMap :=
  ⟨(id, alias) :: map.values, map.runs⟩

def RetainedSsaMap.withRun (map : RetainedSsaMap) (id : ValueId) (alias : RetainedAlias) : RetainedSsaMap :=
  ⟨map.values, (id, alias) :: map.runs⟩

theorem RetainedSsaMap.Covers.realizes {map required : RetainedSsaMap}
    {m : Core.Module} {world : World} {env : Env} {runtime : DemandRuntimePoint}
    (coverage : map.Covers required) (realized : map.Realizes m world env runtime) :
    required.Realizes m world env runtime :=
  ⟨fun cell member => realized.1 cell (coverage.1 cell member),
    fun cell member => realized.2 cell (coverage.2 cell member)⟩

theorem RetainedSsaMap.Covers.bounded {map required : RetainedSsaMap} {frontier : ValueId}
    (coverage : map.Covers required) (bounded : map.Bounded frontier) : required.Bounded frontier :=
  ⟨fun cell member => bounded.1 cell (coverage.1 cell member),
    fun cell member => bounded.2 cell (coverage.2 cell member)⟩

theorem RetainedSsaMap.Covers.admitted {map required : RetainedSsaMap} {profile : ArtifactProfile}
    {retained : List RetainedAlias} (coverage : map.Covers required) (admitted : map.Admitted profile retained) :
    required.Admitted profile retained := by
  intro shrink alias member
  rcases List.mem_append.mp member with values | runs
  · obtain ⟨cell, member, same⟩ := List.mem_map.mp values
    exact admitted shrink alias (List.mem_append_left _
      (List.mem_map.mpr ⟨cell, coverage.1 cell member, same⟩))
  · obtain ⟨cell, member, same⟩ := List.mem_map.mp runs
    exact admitted shrink alias (List.mem_append_right _
      (List.mem_map.mpr ⟨cell, coverage.2 cell member, same⟩))

theorem RetainedSsaMap.Covers.withValue {map required : RetainedSsaMap}
    (coverage : map.Covers required) (id : ValueId) (alias : RetainedAlias) :
    (map.withValue id alias).Covers (required.withValue id alias) := by
  constructor
  · intro cell member
    rcases List.mem_cons.mp member with same | old
    · exact List.mem_cons.mpr (Or.inl same)
    · exact List.mem_cons.mpr (Or.inr (coverage.1 cell old))
  · exact coverage.2

theorem RetainedSsaMap.Covers.withRun {map required : RetainedSsaMap}
    (coverage : map.Covers required) (id : ValueId) (alias : RetainedAlias) :
    (map.withRun id alias).Covers (required.withRun id alias) := by
  constructor
  · exact coverage.1
  · intro cell member
    rcases List.mem_cons.mp member with same | old
    · exact List.mem_cons.mpr (Or.inl same)
    · exact List.mem_cons.mpr (Or.inr (coverage.2 cell old))

theorem RetainedSsaMap.withValue_realizes {map : RetainedSsaMap}
    {m : Core.Module} {world : World} {env : Env} {runtime : DemandRuntimePoint}
    (realized : map.Realizes m world env runtime) {id : ValueId} {alias : RetainedAlias}
    (produced : ValueAliasAt m world env runtime.state.store runtime.frame id alias) :
    (map.withValue id alias).Realizes m world env runtime := by
  constructor
  · intro cell member
    rcases List.mem_cons.mp member with rfl | old
    · exact produced
    · exact realized.1 cell old
  · exact realized.2

theorem RetainedSsaMap.withRun_realizes {map : RetainedSsaMap}
    {m : Core.Module} {world : World} {env : Env} {runtime : DemandRuntimePoint}
    (realized : map.Realizes m world env runtime) {id : ValueId} {alias : RetainedAlias}
    (produced : RunAliasAt m world env runtime.state.store runtime.frame id alias) :
    (map.withRun id alias).Realizes m world env runtime := by
  constructor
  · exact realized.1
  · intro cell member
    rcases List.mem_cons.mp member with rfl | old
    · exact produced
    · exact realized.2 cell old

theorem RetainedSsaMap.withValue_admitted {map : RetainedSsaMap} {profile : ArtifactProfile}
    {retained : List RetainedAlias} (admitted : map.Admitted profile retained) {id : ValueId} {alias : RetainedAlias}
    (produced : profile = .shrink → alias ∈ retained) : (map.withValue id alias).Admitted profile retained := by
  intro shrink next member
  change next ∈ ((id, alias) :: map.values).map Prod.snd ++ map.runs.map Prod.snd at member
  simp only [List.map_cons, List.mem_append, List.mem_cons] at member
  rcases member with (rfl | old) | old
  · exact produced shrink
  · exact admitted shrink next (List.mem_append_left _ old)
  · exact admitted shrink next (List.mem_append_right _ old)

theorem RetainedSsaMap.withRun_admitted {map : RetainedSsaMap} {profile : ArtifactProfile}
    {retained : List RetainedAlias} (admitted : map.Admitted profile retained) {id : ValueId} {alias : RetainedAlias}
    (produced : profile = .shrink → alias ∈ retained) : (map.withRun id alias).Admitted profile retained := by
  intro shrink next member
  change next ∈ map.values.map Prod.snd ++ ((id, alias) :: map.runs).map Prod.snd at member
  simp only [List.map_cons, List.mem_append, List.mem_cons] at member
  rcases member with old | rfl | old
  · exact admitted shrink next (List.mem_append_left _ old)
  · exact produced shrink
  · exact admitted shrink next (List.mem_append_right _ old)

theorem RetainedSsaMap.withValue_bounded {map : RetainedSsaMap} {frontier id : ValueId} {alias : RetainedAlias}
    (bounded : map.Bounded frontier) (fresh : id < frontier) : (map.withValue id alias).Bounded frontier := by
  constructor
  · intro cell member
    rcases List.mem_cons.mp member with rfl | old
    · exact fresh
    · exact bounded.1 cell old
  · exact bounded.2

theorem RetainedSsaMap.withRun_bounded {map : RetainedSsaMap} {frontier id : ValueId} {alias : RetainedAlias}
    (bounded : map.Bounded frontier) (fresh : id < frontier) : (map.withRun id alias).Bounded frontier := by
  constructor
  · exact bounded.1
  · intro cell member
    rcases List.mem_cons.mp member with rfl | old
    · exact fresh
    · exact bounded.2 cell old

end Goose.Lower
