import Goose.Lower.Validation.SnapshotContentsFinal
import Goose.Lower.Validation.SnapshotContentsConstructors
import Goose.Lower.Validation.SnapshotContentsLoops

namespace Goose.Lower.Validation.SnapshotContentsChecks

open Goose.Core Goose.GIR

private def module : Core.Module :=
  { files := #[], types := #[], globals := #[], impls := #[], contexts := #[], entry := 0, origins := #[] }

private def env : TEnv :=
  { mod := module, impl := none, vars := #[⟨"array", .arr (.int .i64) 1, .immutable, 0, 0⟩],
    visible := [0], loops := 0, inExpr := false, scopes := [0], globalLimit := 0, initializing := none }

private def place : Place := .deref (.ref .readOnly (.var 0))

private def initial : LS :=
  ⟨#[⟨[], #[]⟩, ⟨[(0, .data (.int .i64))], #[]⟩], #[some (.data (.int .i64))], some 0, [0]⟩

private def ownerState : LS := (lowerPlace place (lowerEnv module env.vars []) initial).2

private def finalState : LS := (lowerView (.of place) (lowerEnv module env.vars []) initial).2

private theorem generated : GeneratedBuilderState initial := by
  refine ⟨List.Perm.refl _, ?_, ?_⟩
  · intro block current
    have same : block = 0 := Option.some.inj current.symm
    subst block
    decide
  · intro index body row target member
    have bound := (Array.getElem?_eq_some_iff.mp row).1
    have either : index = 0 ∨ index = 1 := by change index < 2 at bound; nat_omega
    rcases either with rfl | rfl
    all_goals
      simp [initial] at row
      subst body
      simp [cfgBlock, GIR.Block.terms] at member

example : Core.tyPlace env place 1 = .ok (⟨.arr (.int .i64) 1, false, false⟩, 1) := rfl

#guard finalState.vals[2]? == some (some (.view .mutable (.int .i64)))

private theorem sourceTrace : SnapshotSourceTrace (lowerEnv module env.vars []) 0 finalState finalState := by
  apply SnapshotSourceTrace.lowerView_of (env := env) (results := [])
    (place := place) (info := ⟨.arr (.int .i64) 1, false, false⟩) (start := 1) (finish := 1)
    (before := initial) (ownerState := ownerState) (owner := 1) (snapshot := 2)
    rfl generated rfl ?_ (Nat.zero_le _) rfl
  intro snapshot mode owner member _
  change Inst.def snapshot (.snapshot mode owner) ∈ [Inst.def 1 (.slotAddr 0)] at member
  simp at member

example : MutableSnapshotGraphs (lower module)
    (permissionFunc (lowerEnv module env.vars []) finalState) finalState :=
  sourceTrace.mutableSnapshotGraphs rfl rfl (by cbv) rfl

example : ∃ authorized,
    SnapshotContentsWitness (lowerEnv module env.vars []) 1 2 1 authorized finalState ∧
    ¬ authorized 0 ∧ ¬ authorized 2 := by
  let site : SnapshotSourceSite (lowerEnv module env.vars []) 2 .borrowed 1 :=
    { typingEnv := env, results := [], place := place,
      info := ⟨.arr (.int .i64) 1, false, false⟩, start := 1, finish := 1,
      beforePlace := initial, ownerState := ownerState, emittedState := finalState,
      aligned := rfl, typed := rfl, generated := generated, lowered := rfl,
      live := rfl, emitted := rfl }
  have evidence := site.freshContents (.refl _) (show finalState.vals[2]? =
    some (some (.view .mutable (.int .i64))) from by cbv)
  obtain ⟨authorized, witness⟩ := snapshotContentsWitness_emit evidence
    site.ownerGenerated (current := 0) rfl site.emitted
  refine ⟨authorized, witness, ?_, ?_⟩
  · intro old
    have fresh : 1 ≤ 0 := witness.fresh 0 old
    omega
  · exact fun joined => Nat.lt_irrefl _ (witness.beforeSnapshot 2 joined)

private def allocated := newBlock [.data (.int .i64)] (lowerEnv module env.vars []) finalState

private def selected : LS := { allocated.2 with cur := some allocated.1.1 }

private def rangeState : LS :=
  (Goose.Lower.lowerRange .i64 (allocated.1.2.headD 0) 0 allocated.1.1
    (fun _ _ => pure 0) (lowerEnv module env.vars []) selected).2

private theorem rangeTrace : SnapshotSourceTrace (lowerEnv module env.vars []) 0 rangeState rangeState := by
  have finalGenerated : GeneratedBuilderState finalState := generated.lowerView (.of place)
    (show lowerView (.of place) (lowerEnv module env.vars []) initial = (2, finalState) from rfl)
  have allocatedTrace := sourceTrace.newBlock [.data (.int .i64)] finalGenerated
    (show newBlock [.data (.int .i64)] (lowerEnv module env.vars []) finalState = allocated from rfl)
  have allocatedGenerated : GeneratedBuilderState allocated.2 := finalGenerated.newBlock (env := lowerEnv module env.vars []) _ rfl
  have selectedTrace : SnapshotSourceTrace (lowerEnv module env.vars []) 0 selected selected :=
    allocatedTrace.setCur_full (current := some allocated.1.1) rfl
  have headerRow : selected.blocks[allocated.1.1]? =
      some ⟨[(allocated.1.2.headD 0, .data (.int .i64))], #[]⟩ := by
    simp [selected, allocated, newBlock1_run]
  have selectedGenerated : GeneratedBuilderState selected := allocatedGenerated.setCur
    (env := lowerEnv module env.vars []) (some allocated.1.1)
    (by
      intro block same
      cases Option.some.inj same
      simp [allocated, newBlock1_run]) rfl
  exact (snapshot_lowerRange selectedTrace selectedGenerated (Nat.zero_le _) .i64
    (allocated.1.2.headD 0) 0 allocated.1.1 ⟨_, headerRow, rfl⟩ (fun _ _ => pure 0)
    (fun depth exit => SnapshotSourceAction.pure _ (some ⟨depth, exit,
      .next allocated.1.1 .i64 (allocated.1.2.headD 0)⟩) 0)).1

example : MutableSnapshotGraphs (lower module)
    (permissionFunc (lowerEnv module env.vars []) rangeState) rangeState :=
  rangeTrace.mutableSnapshotGraphs rfl rfl (by cbv) rfl

#guard rangeState.vals[2]? == some (some (.view .mutable (.int .i64)))

end Goose.Lower.Validation.SnapshotContentsChecks
