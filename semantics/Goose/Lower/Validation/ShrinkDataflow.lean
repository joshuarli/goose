import Goose.GIR.Validate
import Init.Data.Range.Lemmas
import Init.Internal.Order.While

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem list_forIn'_invariant {property : σ → Prop} (items : List α) (start : σ)
    (body : (item : α) → item ∈ items → σ → Id (ForInStep σ))
    (initial : property start)
    (preserved : ∀ item member state, property state → property (body item member state).value) :
    property (forIn' items start body) := by
  induction items generalizing start with
  | nil => exact initial
  | cons first rest ih =>
    rw [List.forIn'_cons]
    have next := preserved first (by simp) start initial
    cases step : body first (by simp) start with
    | done final =>
      change property final
      simpa [step] using next
    | yield mid =>
      change property (forIn' (m := Id) rest mid (fun item member => body item (by simp [member])))
      apply ih mid (fun item member => body item (by simp [member]))
      · simpa [step] using next
      · intro item member state checked
        exact preserved item (by simp [member]) state checked

theorem list_forIn_state_invariant {property : σ → Prop} (items : List α) (start : σ)
    (body : α → σ → Id (ForInStep σ))
    (initial : property start)
    (preserved : ∀ item state, property state → property (body item state).value) :
    property (forIn items start body) := by
  induction items generalizing start with
  | nil => exact initial
  | cons first rest ih =>
    rw [List.forIn_cons]
    have next := preserved first start initial
    cases step : body first start with
    | done final =>
      change property final
      simpa [step] using next
    | yield mid =>
      change property (forIn rest mid body)
      exact ih mid (by simpa [step] using next)

def TrueFlagsPreserved (before after : Array Bool) : Prop :=
  after.size = before.size ∧ ∀ index : Nat, before[index]? = some true → after[index]? = some true

theorem TrueFlagsPreserved.refl (flags : Array Bool) : TrueFlagsPreserved flags flags :=
  ⟨rfl, fun _ present => present⟩

theorem TrueFlagsPreserved.trans {before mid after : Array Bool}
    (first : TrueFlagsPreserved before mid) (second : TrueFlagsPreserved mid after) :
    TrueFlagsPreserved before after :=
  ⟨second.1.trans first.1, fun index present => second.2 index (first.2 index present)⟩

theorem trueFlags_set (flags : Array Bool) (index : Nat) :
    TrueFlagsPreserved flags (flags.set! index true) := by
  refine ⟨Array.size_set! _ _ _, ?_⟩
  intro other present
  change (flags.setIfInBounds index true)[other]? = some true
  rw [Array.getElem?_setIfInBounds]
  split
  · rename_i same
    subst other
    have bound := (Array.getElem?_eq_some_iff.mp present).1
    simp [bound]
  · exact present

theorem freshRunRound_preserves_true (func : Func) (flags : Array Bool) :
    TrueFlagsPreserved flags (freshRunRound func flags).1 := by
  unfold freshRunRound
  change TrueFlagsPreserved flags ((forIn' (m := Id) [:func.blocks.size] (flags, false) _).1)
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply list_forIn'_invariant (property := fun state : Array Bool × Bool => TrueFlagsPreserved flags state.1)
  · exact .refl flags
  · intro target member state checked
    apply list_forIn_state_invariant (property := fun state : Array Bool × Bool => TrueFlagsPreserved flags state.1)
    · exact checked
    · intro param state checked
      obtain ⟨⟨value, ty⟩, index⟩ := param
      dsimp only
      split
      · exact checked.trans (trueFlags_set _ _)
      · exact checked

def KnownStatesPreserved (before after : Array (Option (List ValueId))) : Prop :=
  after.size = before.size ∧ ∀ (index : Nat) roots,
    before[index]? = some (some roots) → ∃ next, after[index]? = some (some next)

theorem KnownStatesPreserved.refl (states : Array (Option (List ValueId))) :
    KnownStatesPreserved states states := ⟨rfl, fun _ roots known => ⟨roots, known⟩⟩

theorem KnownStatesPreserved.trans {before mid after : Array (Option (List ValueId))}
    (first : KnownStatesPreserved before mid) (second : KnownStatesPreserved mid after) :
    KnownStatesPreserved before after := by
  refine ⟨second.1.trans first.1, ?_⟩
  intro index roots known
  obtain ⟨next, present⟩ := first.2 index roots known
  exact second.2 index next present

theorem knownStates_set (states : Array (Option (List ValueId))) (index : Nat) (roots : List ValueId) :
    KnownStatesPreserved states (states.set! index (some roots)) := by
  refine ⟨Array.size_set! _ _ _, ?_⟩
  intro other before present
  change ∃ next, (states.setIfInBounds index (some roots))[other]? = some (some next)
  rw [Array.getElem?_setIfInBounds]
  split
  · rename_i same
    subst other
    have bound := (Array.getElem?_eq_some_iff.mp present).1
    exact ⟨roots, by simp [bound]⟩
  · exact ⟨before, present⟩

theorem emptyFactRound_preserves_known (module : GIR.Module) (func : Func)
    (types : Array (Option VTy)) (provenance : ReplacementQueries) (states : Array (Option (List ValueId))) :
    KnownStatesPreserved states (emptyFactRound module func types provenance states).1 := by
  unfold emptyFactRound
  change KnownStatesPreserved states ((forIn' (m := Id) [:func.blocks.size] (states, false) _).1)
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply list_forIn'_invariant (property := fun state : Array (Option (List ValueId)) × Bool =>
    KnownStatesPreserved states state.1)
  · exact .refl states
  · intro block member state checked
    dsimp only
    split
    · split
      · apply list_forIn_state_invariant (property := fun state : Array (Option (List ValueId)) × Bool =>
          KnownStatesPreserved states state.1)
        · exact checked
        · intro edge state checked
          obtain ⟨target, args⟩ := edge
          dsimp only
          split
          · split
            · exact checked.trans (knownStates_set _ _ _)
            · split
              · exact checked.trans (knownStates_set _ _ _)
              · exact checked
            · exact checked
          · exact checked
      · exact checked
    · exact checked

def dataflowRounds (round : σ → σ × Bool) (state : σ) (changed : Bool) (fuel : Nat) : σ :=
  ((forIn (m := Id) Lean.Loop.mk (state, changed, fuel) fun _ state =>
    if state.2.1 && decide (state.2.2 > 0) then
      let next := round state.1
      pure (.yield (next.1, next.2, state.2.2 - 1))
    else pure (.done state)) : Id (σ × Bool × Nat)).1

theorem dataflowRounds_invariant {property : σ → Prop} (round : σ → σ × Bool)
    (preserved : ∀ state, property state → property (round state).1)
    (state : σ) (changed : Bool) (fuel : Nat) (initial : property state) :
    property (dataflowRounds round state changed fuel) := by
  induction fuel generalizing state changed with
  | zero =>
    unfold dataflowRounds
    change property (Lean.Loop.forIn (m := Id) (β := σ × Bool × Nat) _ _ _).1
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [Nat.not_lt_zero, decide_false, Bool.and_false, Bool.false_eq_true, ite_false]
    change property state
    exact initial
  | succ fuel ih =>
    unfold dataflowRounds
    change property (Lean.Loop.forIn (m := Id) (β := σ × Bool × Nat) _ _ _).1
    rw [Lean.Loop.forIn_eq_of_monadTail]
    cases changed
    · change property state
      exact initial
    · change property (dataflowRounds round (round state).1 (round state).2 fuel)
      exact ih _ _ (preserved state initial)

theorem emptyFactsAtBlocks_entry_known (module : GIR.Module) (func : Func)
    (types : Array (Option VTy)) (provenance : ReplacementQueries) (nonempty : 0 < func.blocks.size) :
    ∃ facts, (emptyFactsAtBlocks module func types provenance)[0]? = some (some facts) := by
  let seed : Array (Option (List ValueId)) := (Array.replicate func.blocks.size none).set! 0 (some [])
  have entry : seed[0]? = some (some []) := by
    change ((Array.replicate func.blocks.size none).setIfInBounds 0 (some []))[0]? = some (some [])
    rw [Array.getElem?_setIfInBounds]
    simp [nonempty]
  have preserved : KnownStatesPreserved seed
      (dataflowRounds (emptyFactRound module func types provenance) seed true
        ((func.blocks.size + 1) * (func.numValues + 1) + 1)) := by
    apply dataflowRounds_invariant
    · intro state checked
      exact checked.trans (emptyFactRound_preserves_known module func types provenance state)
    · exact .refl seed
  have algorithm : emptyFactsAtBlocks module func types provenance =
      dataflowRounds (emptyFactRound module func types provenance) seed true
        ((func.blocks.size + 1) * (func.numValues + 1) + 1) := by
    have present : func.blocks.isEmpty = false := by
      simp [Array.isEmpty, Nat.ne_of_gt nonempty]
    unfold emptyFactsAtBlocks
    simp only [present, Bool.not_false, ite_true]
    rfl
  rw [algorithm]
  exact preserved.2 0 [] entry

theorem dataflowRounds_false (round : σ → σ × Bool) (state : σ) (fuel : Nat) :
    dataflowRounds round state false fuel = state := by
  unfold dataflowRounds
  change (Lean.Loop.forIn (m := Id) (β := σ × Bool × Nat) _ _ _).1 = state
  rw [Lean.Loop.forIn_eq_of_monadTail]
  rfl

theorem dataflowRounds_step (round : σ → σ × Bool) (state : σ) (fuel : Nat) :
    dataflowRounds round state true (fuel + 1) =
      dataflowRounds round (round state).1 (round state).2 fuel := by
  unfold dataflowRounds
  change (Lean.Loop.forIn (m := Id) (β := σ × Bool × Nat) _ _ _).1 = _
  rw [Lean.Loop.forIn_eq_of_monadTail]
  rfl

theorem dataflowRounds_stable {property : σ → Prop} (round : σ → σ × Bool) (measure : σ → Nat)
    (progress : ∀ state, property state → property (round state).1 ∧
      ((round state).2 = true → measure (round state).1 < measure state))
    (unchanged : ∀ state, property state → (round state).2 = false → (round state).1 = state)
    (state : σ) (fuel : Nat) (checked : property state) (enough : measure state < fuel) :
    (round (dataflowRounds round state true fuel)).1 = dataflowRounds round state true fuel := by
  induction fuel generalizing state with
  | zero => omega
  | succ fuel ih =>
    rw [dataflowRounds_step]
    have next := progress state checked
    cases changed : (round state).2
    · rw [dataflowRounds_false]
      have same := unchanged state checked changed
      rw [same]
      exact same
    · apply ih _ next.1
      have decreases := next.2 changed
      omega

end Goose.Lower.Validation
