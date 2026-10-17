import Goose.Lower.Validation.ValueBounds

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def FreshValueRun (action : B ValueId) : Prop :=
  ∀ env before value after, action env before = (value, after) →
    after.cur.isSome = true → before.vals.size ≤ value

theorem FreshValueRun.prepend {first : B α} {next : α → B ValueId}
    (advance : AdvB first) (fresh : ∀ value, FreshValueRun (next value)) :
    FreshValueRun (first >>= next) := by
  intro env before value after run live
  obtain ⟨input, middle, firstRun, nextRun⟩ := bind_eq.mp run
  exact Nat.le_trans (advance env before input middle firstRun).vals
    (fresh input env middle value after nextRun live)

theorem FreshValueRun.prepend_sameValues {first : B α} {next : α → B ValueId}
    (same : ∀ env state, (first env state).2.vals = state.vals)
    (fresh : ∀ value, FreshValueRun (next value)) : FreshValueRun (first >>= next) := by
  intro env before value after run live
  obtain ⟨input, middle, firstRun, nextRun⟩ := bind_eq.mp run
  have values := same env before
  rw [firstRun] at values
  change middle.vals = before.vals at values
  have result := fresh input env middle value after nextRun live
  simpa only [values] using result

theorem freshValue_emitDef (op : Op) : FreshValueRun (emitDef op) := by
  intro env before value after run live
  cases current : before.cur with
  | none =>
    rw [emitDef_none op env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    simp [current] at live
  | some block =>
    rw [emitDef_run op env current] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    exact Nat.le_refl _

theorem FreshValueRun.post {first : B ValueId} {next : ValueId → B α}
    (fresh : FreshValueRun first) (dead : ∀ value, DeadRun (next value)) :
    FreshValueRun (do let value ← first; let _ ← next value; pure value) := by
  intro env before value after run live
  obtain ⟨input, middle, firstRun, _, last, nextRun, pureRun⟩ :=
    (by simpa only [bind_eq] using run)
  obtain ⟨rfl, rfl⟩ := pure_eq.mp pureRun
  exact fresh env before input middle firstRun (live_before (dead input) nextRun live)

theorem freshValue_whenLive (action : BlockId → B ValueId)
    (fresh : ∀ block, FreshValueRun (action block)) : FreshValueRun (whenLive 0 action) := by
  intro env before value after run live
  cases current : before.cur with
  | none =>
    rw [whenLive_none _ _ env current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    simp [current] at live
  | some block =>
    rw [whenLive_some _ _ env current] at run
    exact fresh block env before value after run live

theorem freshValue_freezeTo {action : B ValueId} (fresh : FreshValueRun action)
    (advance : AdvB action) (mu : Mutability) :
    FreshValueRun (do let value ← action; freezeTo mu value) := by
  intro env before value after run live
  obtain ⟨input, middle, firstRun, nextRun⟩ := bind_eq.mp run
  rcases freezeTo_cases nextRun with ⟨rfl, rfl⟩ | emitted
  · exact fresh env before value after firstRun live
  · exact Nat.le_trans (advance env before input middle firstRun).vals
      (freshValue_emitDef _ env middle value after emitted live)

theorem freshValue_borrowTo {action : B ValueId} (fresh : FreshValueRun action)
    (advance : AdvB action) (mu : Mutability) :
    FreshValueRun (do let value ← action; borrowTo mu value) := by
  intro env before value after run live
  obtain ⟨input, middle, firstRun, nextRun⟩ := bind_eq.mp run
  rcases borrowTo_cases nextRun with frozen | emitted
  · exact freshValue_freezeTo fresh advance mu env before value after
      (bind_eq.mpr ⟨input, middle, firstRun, frozen⟩) live
  · exact Nat.le_trans (advance env before input middle firstRun).vals
      (freshValue_emitDef _ env middle value after emitted live)

theorem freshValue_joinValue (yes no : Option BlockId) (yesValue noValue : ValueId) :
    FreshValueRun (joinValue yes yesValue no noValue) := by
  intro env before value after run live
  unfold joinValue at run
  cases yes <;> cases no
  · simp only [bind_eq] at run
    obtain ⟨_, middle, changed, pureRun⟩ := run
    rw [setCur_run] at changed
    obtain ⟨_, rfl⟩ := Prod.mk.inj changed
    obtain ⟨_, rfl⟩ := pure_eq.mp pureRun
    simp at live
  all_goals
    simp only [bind_eq] at run
    obtain ⟨type, middle, typeRun, ⟨block, params⟩, allocated, allocation,
      _, patched, patch, _, resumed, resume, pureRun⟩ := run
    have same : middle = before := by
      simpa only [valTy_run] using (congrArg Prod.snd typeRun).symm
    subst middle
    rw [newBlock1_run] at allocation
    obtain ⟨pair, rfl⟩ := Prod.mk.inj allocation
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair
    obtain ⟨rfl, _⟩ := pure_eq.mp pureRun
    exact Nat.le_refl _

theorem freshValue_shortCircuit (isAnd : Bool) (input : ValueId) (rhs : B ValueId) :
    FreshValueRun (shortCircuit isAnd input rhs) := by
  unfold shortCircuit
  apply freshValue_whenLive
  intro block env before value after run live
  simp only [bind_eq] at run
  obtain ⟨⟨right, join, param⟩, forked, forkRun, _, selected, select,
    result, evaluated, evaluate, _, closed, close, _, resumed, resume, pureRun⟩ := run
  have ids := (scFork_ids forkRun).1
  have same : param = before.vals.size := (Prod.mk.inj (Prod.mk.inj ids).2).2
  obtain ⟨rfl, _⟩ := pure_eq.mp pureRun
  exact Nat.le_of_eq same.symm

theorem FreshValueRun.inScope (scope : ScopeId) {action : B ValueId}
    (fresh : FreshValueRun action) : FreshValueRun (inScope scope action) := by
  intro env before value after run live
  obtain ⟨middle, actionRun, rfl⟩ := inScope_eq run
  exact fresh env { before with stack := scope :: before.stack } value middle actionRun live

#print axioms freshValue_joinValue
#print axioms freshValue_shortCircuit

end Goose.Lower.Validation
