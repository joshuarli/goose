import Goose.Lower.Validation.CfgOpenCount
import Goose.Lower.Validation.CfgOpenActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def LiveCount (state : LS) : Nat := if state.cur.isSome then 1 else 0

def CompletionRun (action : B α) : Prop :=
  ∀ env before result after, action env before = (result, after) →
    CurrentOpen before → ShapedBlocks before →
      ShapedBlocks after ∧ OpenCount after + LiveCount before = OpenCount before + LiveCount after

structure CompletionAction (action : B α) : Prop where
  openAction : OpenAction action
  complete : CompletionRun action

theorem CompletionAction.pure (value : α) : CompletionAction (pure value) := by
  refine ⟨OpenAction.pure value, ?_⟩
  intro env before result after run _ shaped
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact ⟨shaped, rfl⟩

theorem CompletionAction.bind {first : B α} {next : α → B β}
    (one : CompletionAction first) (two : ∀ result, CompletionAction (next result)) :
    CompletionAction (first >>= next) := by
  refine ⟨one.openAction.bind (fun value => (two value).openAction), ?_⟩
  intro env before result after run openBefore shapedBefore
  obtain ⟨value, middle, firstRun, secondRun⟩ := bind_eq.mp run
  obtain ⟨shapedMiddle, countOne⟩ := one.complete env before value middle firstRun openBefore shapedBefore
  have openMiddle := one.openAction.paths env before value middle firstRun openBefore openBefore.bound
  obtain ⟨shapedAfter, countTwo⟩ := (two value).complete env middle result after secondRun openMiddle shapedMiddle
  exact ⟨shapedAfter, by omega⟩

theorem CompletionAction.of_state {action : B α} (openAction : OpenAction action)
    (blocks : ∀ env state, (action env state).2.blocks = state.blocks)
    (current : ∀ env state, (action env state).2.cur = state.cur) : CompletionAction action := by
  refine ⟨openAction, ?_⟩
  intro env before result after run _ shaped
  have blockEq : after.blocks = before.blocks := by simpa [run] using blocks env before
  have curEq : after.cur = before.cur := by simpa [run] using current env before
  refine ⟨shaped.of_blocks blockEq, ?_⟩
  simp [OpenCount, LiveCount, blockEq, curEq]

theorem complete_emitDef (op : Op) : CompletionAction (emitDef op) := by
  refine ⟨open_emitDef op, ?_⟩
  intro env before result after run openBefore shaped
  have shapedAfter := shaped.emitDef openBefore op env
  rw [run] at shapedAfter
  refine ⟨shapedAfter, ?_⟩
  cases current : before.cur with
  | none =>
    have same : after = before := by
      simp only [emitDef, bind_run, get_apply, current, pure_run] at run
      exact (Prod.mk.inj run).2.symm
    simp [same]
  | some block =>
    obtain ⟨body, row, _⟩ := openBefore block current
    rw [emitDef_run op env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    have count := openCount_push_def row before.vals.size op
    change OpenCount _ + LiveCount before = OpenCount before + LiveCount _
    simpa only [OpenCount, LiveCount] using congrArg (· + LiveCount before) count

theorem complete_emitEffect (effect : Effect) : CompletionAction (emitEffect effect) := by
  refine ⟨open_emitEffect effect, ?_⟩
  intro env before result after run openBefore shaped
  have shapedAfter := shaped.emitEffect openBefore effect env
  rw [run] at shapedAfter
  refine ⟨shapedAfter, ?_⟩
  cases current : before.cur with
  | none =>
    have same : after = before := by
      rw [emitEffect_none effect env current] at run
      exact (Prod.mk.inj run).2.symm
    simp [same]
  | some block =>
    obtain ⟨body, row, _⟩ := openBefore block current
    rw [emitEffect_run effect env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact congrArg (· + LiveCount before) (openCount_push_effect row effect)

theorem complete_emitTerm (term : Term) : CompletionAction (emitTerm term) := by
  refine ⟨open_emitTerm term, ?_⟩
  intro env before result after run openBefore shaped
  have shapedAfter := shaped.emitTerm openBefore term env
  rw [run] at shapedAfter
  refine ⟨shapedAfter, ?_⟩
  cases current : before.cur with
  | none =>
    have same : after = before := by
      rw [emitTerm_none term env current] at run
      exact (Prod.mk.inj run).2.symm
    simp [same]
  | some block =>
    obtain ⟨body, row, openBody⟩ := openBefore block current
    rw [emitTerm_run term env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    have count := openCount_push_term row openBody term
    simpa only [OpenCount, LiveCount, current, Option.isSome_some, ite_true,
      Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] using count

theorem CompletionAction.closed {action : B α} (preserves : CompletionAction action)
    {env : LEnv} {before after : LS} {result : α} (run : action env before = (result, after))
    (openBefore : CurrentOpen before) (shapedBefore : ShapedBlocks before)
    (initial : OpenCount before = LiveCount before) (stopped : after.cur = none) : AllClosed after := by
  obtain ⟨shapedAfter, balance⟩ := preserves.complete env before result after run openBefore shapedBefore
  have zeroLive : LiveCount after = 0 := by simp [LiveCount, stopped]
  apply allClosed_of_shaped_count shapedAfter
  omega

end Goose.Lower.Validation
