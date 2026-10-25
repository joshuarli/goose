import Goose.Lower.Validation.SnapshotContentsSourceControlBranches

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem snapshot_control_selected {le : LEnv} {loop : Option LoopCtx}
    {branch : B (BlockId × BlockId × α)} {body : B ValueId}
    (prefixSource : SnapshotSourceAction le loop branch) (prefixFree : SnapshotFreeRun branch)
    (bodySource : SnapshotSourceAction le loop body)
    (prefixRows : ∀ before result after, GeneratedBuilderState before →
      branch le before = (result, after) →
      result.1 < after.blocks.size ∧ result.2.1 < after.blocks.size ∧
        ∃ block, after.blocks[result.2.1]? = some block ∧
          ∀ param ∈ block.params, param.1 < after.vals.size)
    (arguments : ValueId → List ValueId) :
    SnapshotTraceRun le loop (do
      let (target, join, payload) ← branch
      Goose.Lower.setCur (some target)
      let value ← body
      Goose.Lower.emitTerm (.br join (arguments value))
      Goose.Lower.setCur (some join)
      pure payload) := by
  intro before result after generated frames run
  simp only [bind_eq] at run
  obtain ⟨⟨target, join, payload⟩, forked, forkRun, u1, selected, selectRun,
    value, evaluated, bodyRun, u2, closed, closeRun, u3, resumed, resumeRun, done⟩ := run
  obtain ⟨_, rfl⟩ := pure_eq.mp done
  obtain ⟨targetBound, joinBound, joinBlock, joinRow, params⟩ := prefixRows before _ _ generated forkRun
  have prefixAdvance := prefixSource.advance le before _ _ forkRun
  have forkGenerated := generated.of_runs prefixSource.dense prefixSource.targets frames.toTargets forkRun
  have selectedGenerated := forkGenerated.setCur (some target)
    (fun block equal => (Option.some.inj equal) ▸ targetBound) selectRun
  have selectExt : forked.Ext selected := by
    rw [setCur_run] at selectRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj selectRun
    exact .refl _
  have selectValues : selected.vals.size = forked.vals.size := by
    rw [setCur_run] at selectRun
    exact congrArg (fun pair => pair.2.vals.size) selectRun.symm
  have selectedFrames := frames.mono (prefixAdvance.ext.trans selectExt)
  have bodyTrace := bodySource.snapshots selected value evaluated selectedGenerated selectedFrames bodyRun
  have bodyGenerated := selectedGenerated.of_runs bodySource.dense bodySource.targets selectedFrames.toTargets bodyRun
  have bodyAdvance := bodySource.advance le selected _ _ bodyRun
  have forkBody := selectExt.trans bodyAdvance.ext
  obtain ⟨destination, destinationRow, destinationParams, _⟩ := forkBody.2 join joinBlock joinRow
  have closedTrace := bodyTrace.emitTerm_before_full bodyGenerated closeRun (by
    intro edge member actual row param belongs
    have same : edge = (join, arguments value) := by simpa [Term.permissionEdges] using member
    subst edge
    have located : actual = ⟨destination.params, destination.insts.toList⟩ := by
      simpa only [permissionFunc, Array.getElem?_map, destinationRow, Option.map_some, Option.some.injEq] using row.symm
    rw [located] at belongs
    rw [selectValues]
    exact params param (by simpa only [destinationParams] using belongs))
  have closedGenerated := bodyGenerated.emitTerm (.br join (arguments value)) (by
    intro block member
    have equal : block = join := by simpa [Term.successors] using member
    subst block
    exact Nat.lt_of_lt_of_le joinBound forkBody.1) closeRun
  have closeExt := (advB_emitTerm (.br join (arguments value)) le evaluated _ _ closeRun).ext
  have resumedTrace := closedTrace.setCur_full resumeRun
  have resumedGenerated := closedGenerated.setCur (some join) (fun block equal => by
    have equal := Option.some.inj equal
    subst block
    exact Nat.lt_of_lt_of_le joinBound (forkBody.trans closeExt).1) resumeRun
  have resumeExt : closed.Ext resumed := by
    rw [setCur_run] at resumeRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj resumeRun
    exact .refl _
  have noPrefix : NoNewSnapshots before selected := by
    have one : NoNewSnapshots before forked := by simpa only [forkRun] using prefixFree le before
    have two : NoNewSnapshots forked selected := by
      simpa only [selectRun] using SnapshotFreeRun.setCur (some target) le forked
    exact one.trans two
  have oldTrace : SnapshotSourceTrace le before.vals.size selected resumed := by
    intro snapshot mode owner member bound
    exact (Nat.not_lt_of_ge bound (snapshot_definition_lt generated.dense (noPrefix _ _ _ member))).elim
  exact oldTrace.seq resumedTrace (by rw [selectValues]; exact prefixAdvance.vals)
    selectedGenerated.dense resumedGenerated.dense (bodyAdvance.ext.trans (closeExt.trans resumeExt))

theorem SnapshotTraceRun.shortCircuit {le : LEnv} {loop : Option LoopCtx}
    (isAnd : Bool) (condition : ValueId) {body : B ValueId}
    (bodySource : SnapshotSourceAction le loop body) :
    SnapshotTraceRun le loop (Goose.Lower.shortCircuit isAnd condition body) := by
  intro before result after generated frames run
  cases live : before.cur with
  | none =>
    rw [Goose.Lower.shortCircuit, whenLive_none _ _ _ live] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact .empty le before generated.dense
  | some current =>
    rw [Goose.Lower.shortCircuit, whenLive_some _ _ _ live] at run
    apply snapshot_control_selected (SnapshotSourceAction.scFork le loop isAnd condition)
      (SnapshotFreeRun.scFork isAnd condition) bodySource ?_ (fun value => [value]) before result after generated frames run
    intro state output finish checked action
    have ids := scFork_ids action
    refine ⟨?_, ?_, ?_⟩
    · have id := congrArg Prod.fst ids.1
      have size := ids.2
      nat_omega
    · have id := congrArg (fun tuple : BlockId × BlockId × ValueId => tuple.2.1) ids.1
      have size := ids.2
      nat_omega
    · cases active : state.cur with
      | none =>
        cases isAnd <;> simp only [Goose.Lower.scFork, bind_eq, Bool.false_eq_true, reduceIte] at action
        all_goals
          obtain ⟨a, one, oneRun, b, two, twoRun, u, closed, closedRun, done⟩ := action
          rw [newBlock0_run] at oneRun
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj oneRun
          rw [newBlock1_run] at twoRun
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj twoRun
          rw [emitTerm_none _ le (show ({ state with blocks := (state.blocks.push ⟨[], #[]⟩).push ⟨[(state.vals.size, .data .bool)], #[]⟩, vals := state.vals.push (some (.data .bool)) } : LS).cur = none from active)] at closedRun
          obtain ⟨_, rfl⟩ := Prod.mk.inj closedRun
          obtain ⟨rfl, rfl⟩ := pure_eq.mp done
          refine ⟨⟨[(state.vals.size, .data .bool)], #[]⟩, by simp only [Array.getElem?_push, Array.size_push, ite_true], ?_⟩
          intro param member
          have equal := List.mem_singleton.mp member
          subst param
          simp
      | some block =>
        rw [scFork_run isAnd condition le active] at action
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj action
        refine ⟨⟨[(state.vals.size, .data .bool)], #[]⟩, ?_, ?_⟩
        · have different : block ≠ state.blocks.size + 1 := Nat.ne_of_lt (Nat.lt_succ_of_lt (checked.live block active))
          simp only [Array.getElem?_modify, different, ite_false, Array.getElem?_push, Array.size_push, ite_true]
        · intro param member
          have equal := List.mem_singleton.mp member
          subst param
          simp

end Goose.Lower.Validation
