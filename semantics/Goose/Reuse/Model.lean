/-!
A model of artifact reuse: a stage, its cache, and what a cache can and cannot
break.

A **stage** turns an input into a result (`run`) and names the part of the
input the result depends on (`key`). A **cache** is a finite map from keys to
results. `cachedRun` looks the input's key up and, when it is absent, runs the
stage and records the result.

What is proved. Provided the key determines the result, and the cache is
consistent (every entry is the result of some input with that key), a cached
run returns exactly what an uncached run returns and leaves the cache
consistent; so any sequence of cached runs from the empty cache agrees with
recomputation, whatever order the inputs arrive in and whatever the cache
already holds. The same holds for two stages in a row where the second is keyed
on the first's result.

What is **not** proved. The hypothesis `KeyDetermines` — `key i = key j` implies
`run i = run j` — is the completeness of dependency tracking: that the key
mentions everything the result depends on. It is assumed here, not established,
and nothing in this file can establish it for a real stage. It is also
necessary: a stage whose key omits an input the result depends on has a
consistent-looking cache and an input for which `cachedRun` answers wrongly
(`wrong_answer_without_key_determination`, `key_omission_example`). A
reuse boundary is only as sound as the argument that its key is complete.

The model is independent of the Core semantics. A cache here is an association
list; entries are only ever added for absent keys, so it behaves as a finite
map.
-/

namespace Goose.Reuse

/-- A stage: `key` is the part of an input the result is claimed to depend on. -/
structure Stage (I K A : Type) where
  key : I → K
  run : I → A

/-- A finite map from keys to results. -/
abbrev Cache (K A : Type) := List (K × A)

variable {I K A B : Type} [DecidableEq K]

/-- The result recorded for `k`, if any. -/
def Cache.lookup (c : Cache K A) (k : K) : Option A :=
  (c.find? fun e => decide (e.1 = k)).map (·.2)

/-- Run the stage on `i`, reusing a recorded result for the same key. -/
def cachedRun (s : Stage I K A) (c : Cache K A) (i : I) : A × Cache K A :=
  match c.lookup (s.key i) with
  | some a => (a, c)
  | none =>
    let a := s.run i
    (a, (s.key i, a) :: c)

/-- Every entry is what the stage computes for some input with that key. -/
def Consistent (s : Stage I K A) (c : Cache K A) : Prop :=
  ∀ k a, (k, a) ∈ c → ∃ i, s.key i = k ∧ s.run i = a

/-- The key determines the result: the completeness of dependency tracking.
Assumed by the theorems below; never proved. -/
def KeyDetermines (s : Stage I K A) : Prop :=
  ∀ i j, s.key i = s.key j → s.run i = s.run j

theorem Cache.lookup_mem {c : Cache K A} {k : K} {a : A} (h : c.lookup k = some a) :
    (k, a) ∈ c := by
  unfold Cache.lookup at h
  cases hf : c.find? fun e => decide (e.1 = k) with
  | none => simp [hf] at h
  | some e =>
    simp only [hf, Option.map_some, Option.some.injEq] at h
    have hmem := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    simp only [decide_eq_true_eq] at hk
    obtain ⟨k', a'⟩ := e
    simp only at hk h
    subst hk; subst h
    exact hmem

/-- **A cached run returns the uncached result.** -/
theorem cachedRun_result {s : Stage I K A} (hs : KeyDetermines s) {c : Cache K A}
    (hc : Consistent s c) (i : I) : (cachedRun s c i).1 = s.run i := by
  unfold cachedRun
  cases h : c.lookup (s.key i) with
  | none => rfl
  | some a =>
    obtain ⟨j, hj, hr⟩ := hc _ _ (Cache.lookup_mem h)
    simp only
    rw [← hr]
    exact (hs i j hj.symm).symm

/-- **A cached run leaves the cache consistent.** Needs no hypothesis on the key:
a new entry is the stage's own result for its own input. -/
theorem cachedRun_consistent {s : Stage I K A} {c : Cache K A}
    (hc : Consistent s c) (i : I) : Consistent s (cachedRun s c i).2 := by
  unfold cachedRun
  cases h : c.lookup (s.key i) with
  | some a => exact hc
  | none =>
    intro k a hmem
    simp only [List.mem_cons, Prod.mk.injEq] at hmem
    rcases hmem with ⟨hk, ha⟩ | hmem
    · exact ⟨i, hk.symm, ha.symm⟩
    · exact hc k a hmem

omit [DecidableEq K] in
theorem consistent_nil (s : Stage I K A) : Consistent s [] := by
  intro k a h; simp at h

/-- Run a list of inputs in order, threading the state through `step`. -/
def runAll {S : Type} (step : S → I → B × S) : S → List I → List B × S
  | st, [] => ([], st)
  | st, i :: is =>
    let (b, st') := step st i
    let (bs, st'') := runAll step st' is
    (b :: bs, st'')

/-- A sequence of steps agrees with direct computation, and keeps its invariant,
when each step does. -/
theorem runAll_agrees {S : Type} (step : S → I → B × S) (inv : S → Prop) (f : I → B)
    (hstep : ∀ st i, inv st → (step st i).1 = f i ∧ inv (step st i).2) :
    ∀ (st : S) (is : List I), inv st → (runAll step st is).1 = is.map f ∧ inv (runAll step st is).2
  | st, [], h => ⟨rfl, h⟩
  | st, i :: is, h => by
    obtain ⟨h1, h2⟩ := hstep st i h
    obtain ⟨h3, h4⟩ := runAll_agrees step inv f hstep (step st i).2 is h2
    simp only [runAll, List.map_cons]
    exact ⟨by rw [h1, h3], h4⟩

/-- **Any sequence of cached runs from the empty cache returns the results of
uncached runs**, and leaves a consistent cache. -/
theorem cachedRuns_agree {s : Stage I K A} (hs : KeyDetermines s) (inputs : List I) :
    (runAll (cachedRun s) [] inputs).1 = inputs.map s.run ∧
      Consistent s (runAll (cachedRun s) [] inputs).2 :=
  runAll_agrees (cachedRun s) (Consistent s) s.run
    (fun _ i hc => ⟨cachedRun_result hs hc i, cachedRun_consistent hc i⟩) [] inputs
    (consistent_nil s)

/-- The same from any consistent cache, not only the empty one. -/
theorem cachedRuns_agree_from {s : Stage I K A} (hs : KeyDetermines s) {c : Cache K A}
    (hc : Consistent s c) (inputs : List I) :
    (runAll (cachedRun s) c inputs).1 = inputs.map s.run ∧
      Consistent s (runAll (cachedRun s) c inputs).2 :=
  runAll_agrees (cachedRun s) (Consistent s) s.run
    (fun _ i hc => ⟨cachedRun_result hs hc i, cachedRun_consistent hc i⟩) c inputs hc

/-! ### Two stages in a row -/

section Composition

variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂]

/-- Two caches, one per stage. -/
abbrev Caches (K₁ K₂ A B : Type) := Cache K₁ A × Cache K₂ B

/-- Run the first stage on the input, then the second on the first's result,
each through its own cache; the second is keyed on the first's result. -/
def cachedRun₂ (s₁ : Stage I K₁ A) (s₂ : Stage A K₂ B) (cs : Caches K₁ K₂ A B) (i : I) :
    B × Caches K₁ K₂ A B :=
  let (a, c₁) := cachedRun s₁ cs.1 i
  let (b, c₂) := cachedRun s₂ cs.2 a
  (b, (c₁, c₂))

def Consistent₂ (s₁ : Stage I K₁ A) (s₂ : Stage A K₂ B) (cs : Caches K₁ K₂ A B) : Prop :=
  Consistent s₁ cs.1 ∧ Consistent s₂ cs.2

/-- **Two cached stages in a row** return what the uncached composition returns
and keep both caches consistent. -/
theorem cachedRun₂_result {s₁ : Stage I K₁ A} {s₂ : Stage A K₂ B}
    (h₁ : KeyDetermines s₁) (h₂ : KeyDetermines s₂) {cs : Caches K₁ K₂ A B}
    (hc : Consistent₂ s₁ s₂ cs) (i : I) :
    (cachedRun₂ s₁ s₂ cs i).1 = s₂.run (s₁.run i) ∧
      Consistent₂ s₁ s₂ (cachedRun₂ s₁ s₂ cs i).2 := by
  have e1 := cachedRun_result h₁ hc.1 i
  have k1 := cachedRun_consistent hc.1 i
  have e2 := cachedRun_result h₂ hc.2 (cachedRun s₁ cs.1 i).1
  have k2 := cachedRun_consistent hc.2 (cachedRun s₁ cs.1 i).1
  unfold cachedRun₂
  exact ⟨e2.trans (congrArg s₂.run e1), k1, k2⟩

/-- A sequence of inputs through two cached stages, from empty caches, returns
the uncached results. -/
theorem cachedRuns₂_agree {s₁ : Stage I K₁ A} {s₂ : Stage A K₂ B}
    (h₁ : KeyDetermines s₁) (h₂ : KeyDetermines s₂) (inputs : List I) :
    (runAll (cachedRun₂ s₁ s₂) ([], []) inputs).1 = inputs.map (fun i => s₂.run (s₁.run i)) ∧
      Consistent₂ s₁ s₂ (runAll (cachedRun₂ s₁ s₂) ([], []) inputs).2 :=
  runAll_agrees (cachedRun₂ s₁ s₂) (Consistent₂ s₁ s₂) (fun i => s₂.run (s₁.run i))
    (fun _ i hc => cachedRun₂_result h₁ h₂ hc i) _ inputs ⟨consistent_nil s₁, consistent_nil s₂⟩

end Composition

/-! ### The key-determines-result hypothesis cannot be dropped -/

/-- If the key does not determine the result, some consistent cache makes a
cached run return a wrong answer. -/
theorem wrong_answer_without_key_determination {s : Stage I K A} (h : ¬ KeyDetermines s) :
    ∃ (c : Cache K A) (i : I), Consistent s c ∧ (cachedRun s c i).1 ≠ s.run i := by
  have : ∃ i j, s.key i = s.key j ∧ s.run i ≠ s.run j := by
    refine Classical.byContradiction fun hne => h fun i j hk => ?_
    exact Classical.byContradiction fun hr => hne ⟨i, j, hk, hr⟩
  obtain ⟨i, j, hk, hr⟩ := this
  refine ⟨[(s.key i, s.run i)], j, ?_, ?_⟩
  · intro k a hmem
    simp only [List.mem_singleton, Prod.mk.injEq] at hmem
    exact ⟨i, hmem.1.symm, hmem.2.symm⟩
  · unfold cachedRun Cache.lookup
    simp [← hk, hr]

/-- A concrete stage whose key omits the second component of its input. -/
def omittedInput : Stage (Nat × Nat) Nat Nat where
  key := Prod.fst
  run := fun p => p.1 + p.2

/-- The inputs `(0, 0)` and `(0, 1)` share a key but not a result. After the
first runs, the cache is consistent, and the second input is answered with the
first's result. -/
theorem key_omission_example :
    Consistent omittedInput (cachedRun omittedInput [] (0, 0)).2 ∧
      (cachedRun omittedInput (cachedRun omittedInput [] (0, 0)).2 (0, 1)).1 = 0 ∧
      omittedInput.run (0, 1) = 1 := by
  refine ⟨cachedRun_consistent (consistent_nil _) _, ?_, rfl⟩
  decide

end Goose.Reuse
