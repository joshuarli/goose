import Goose.Lower.Validation.CfgSourceDominanceLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def LiveSSARun (loop : Option LoopCtx) (inputs : List ValueId) (outputs : α → List ValueId)
    (action : B α) : Prop :=
  ∀ env before result after, action env before = (result, after) →
    ∀ imports, ImportedState before imports → LoopImportsReady loop before imports →
      AvailableValues before imports inputs → before.cur.isSome = true →
        ∃ nextImports, SSAResult before after imports nextImports (outputs result)

theorem SSARun.live {loop : Option LoopCtx} {inputs : List ValueId} {outputs : α → List ValueId}
    {action : B α} (source : SSARun loop inputs outputs action) : LiveSSARun loop inputs outputs action :=
  fun env before result after run imports checked ready arguments _ =>
    source env before result after run imports checked ready arguments

theorem SSARun.discard {loop : Option LoopCtx} {inputs : List ValueId} {outputs : α → List ValueId}
    {action : B α} (source : SSARun loop inputs outputs action) : SSARun loop inputs (fun _ => []) action :=
  source.congr_outputs (fun _ => List.nil_subset _)

theorem LiveSSARun.bind {loop : Option LoopCtx} {inputs : List ValueId}
    {intermediate : α → List ValueId} {outputs : β → List ValueId}
    {first : B α} {next : α → B β} (one : LiveSSARun loop inputs intermediate first)
    (two : ∀ value, SSARun loop (intermediate value) outputs (next value)) :
    LiveSSARun loop inputs outputs (first >>= next) := by
  intro env before result after run imports checked ready arguments live
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  obtain ⟨middleImports, firstState⟩ := one env before value middle firstRun imports checked ready arguments live
  obtain ⟨nextImports, nextState⟩ := two value env middle result after nextRun middleImports
    firstState.checked (firstState.loop ready) firstState.available
  exact ⟨nextImports, firstState.trans nextState⟩

theorem LiveSSARun.bind_current {loop : Option LoopCtx} {inputs : List ValueId}
    {intermediate : α → List ValueId} {outputs : β → List ValueId}
    {first : B α} {next : α → B β} (one : SSARun loop inputs intermediate first)
    (current : ∀ env state, (first env state).2.cur = state.cur)
    (two : ∀ value, LiveSSARun loop (intermediate value) outputs (next value)) :
    LiveSSARun loop inputs outputs (first >>= next) := by
  intro env before result after run imports checked ready arguments live
  obtain ⟨value, middle, firstRun, nextRun⟩ := bind_eq.mp run
  obtain ⟨middleImports, firstState⟩ := one env before value middle firstRun imports checked ready arguments
  have same := current env before
  rw [firstRun] at same
  change middle.cur = before.cur at same
  obtain ⟨nextImports, nextState⟩ := two value env middle result after nextRun middleImports
    firstState.checked (firstState.loop ready) firstState.available (by simpa only [same] using live)
  exact ⟨nextImports, firstState.trans nextState⟩

theorem ssa_whenLive_live (loop : Option LoopCtx) (default : α) (inputs : List ValueId)
    (outputs : α → List ValueId) {action : B α} (source : LiveSSARun loop inputs outputs action) :
    SSARun loop inputs outputs (whenLive default fun _ => action) := by
  intro env before result after run imports checked ready arguments
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact ⟨imports, SSAResult.of_current checked (.refl before) (Or.inr rfl)
      (by simp [AvailableValues, current])⟩
  | some block =>
    rw [whenLive_some _ _ env current] at run
    exact source env before result after run imports checked ready arguments (by simp [current])

end Goose.Lower.Validation
