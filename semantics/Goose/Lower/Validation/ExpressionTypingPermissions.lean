import Goose.GIR.Typing

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def CapabilityBelow (lower upper : Bool × Bool) : Prop :=
  (lower.1 = true → upper.1 = true) ∧ (lower.2 = true → upper.2 = true)

def capabilityWeight (capability : Bool × Bool) : Nat :=
  (if capability.1 then 1 else 0) + (if capability.2 then 1 else 0)

inductive CapabilitiesBelow : List (Bool × Bool) → List (Bool × Bool) → Prop where
  | nil : CapabilitiesBelow [] []
  | cons {lower upper : Bool × Bool} {lowers uppers : List (Bool × Bool)}
      (head : CapabilityBelow lower upper) (tail : CapabilitiesBelow lowers uppers) :
      CapabilitiesBelow (lower :: lowers) (upper :: uppers)

def capabilitiesWeight : List (Bool × Bool) → Nat
  | [] => 0
  | head :: tail => capabilityWeight head + capabilitiesWeight tail

theorem CapabilityBelow.weight_le {lower upper : Bool × Bool} (below : CapabilityBelow lower upper) :
    capabilityWeight lower ≤ capabilityWeight upper := by
  obtain ⟨a, b⟩ := lower
  obtain ⟨c, d⟩ := upper
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [CapabilityBelow, capabilityWeight]

theorem CapabilityBelow.eq_of_weight {lower upper : Bool × Bool} (below : CapabilityBelow lower upper)
    (same : capabilityWeight lower = capabilityWeight upper) : lower = upper := by
  obtain ⟨a, b⟩ := lower
  obtain ⟨c, d⟩ := upper
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [CapabilityBelow, capabilityWeight]

theorem CapabilitiesBelow.weight_le {lower upper : List (Bool × Bool)} (below : CapabilitiesBelow lower upper) :
    capabilitiesWeight lower ≤ capabilitiesWeight upper := by
  induction below with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    have first := head.weight_le
    simp only [capabilitiesWeight]
    omega

theorem CapabilitiesBelow.eq_of_weight {lower upper : List (Bool × Bool)} (below : CapabilitiesBelow lower upper)
    (same : capabilitiesWeight lower = capabilitiesWeight upper) : lower = upper := by
  induction below with
  | nil => rfl
  | @cons a b lowers uppers head tail ih =>
    have first := head.weight_le
    have rest := tail.weight_le
    simp only [capabilitiesWeight] at same
    have headEqual := head.eq_of_weight (by omega)
    have tailEqual := ih (by omega)
    exact congrArg (fun tail => a :: tail) tailEqual |>.trans (by rw [headEqual])

theorem CapabilitiesBelow.weight_lt_of_ne {lower upper : List (Bool × Bool)}
    (below : CapabilitiesBelow lower upper) (different : lower ≠ upper) :
    capabilitiesWeight lower < capabilitiesWeight upper := by
  have bounded := below.weight_le
  have unequal : capabilitiesWeight lower ≠ capabilitiesWeight upper := by
    intro same
    exact different (below.eq_of_weight same)
  omega

theorem CapabilityBelow.refl (value : Bool × Bool) : CapabilityBelow value value :=
  ⟨fun h => h, fun h => h⟩

theorem CapabilityBelow.trans {a b c : Bool × Bool} (first : CapabilityBelow a b)
    (second : CapabilityBelow b c) : CapabilityBelow a c :=
  ⟨fun h => second.1 (first.1 h), fun h => second.2 (first.2 h)⟩

theorem CapabilitiesBelow.refl (values : List (Bool × Bool)) : CapabilitiesBelow values values := by
  induction values with
  | nil => exact .nil
  | cons head tail ih => exact .cons (.refl head) ih

theorem CapabilitiesBelow.trans {a b c : List (Bool × Bool)} (first : CapabilitiesBelow a b)
    (second : CapabilitiesBelow b c) : CapabilitiesBelow a c := by
  induction first generalizing c with
  | nil => cases second; exact .nil
  | cons head tail ih =>
    cases second with
    | cons next rest => exact .cons (head.trans next) (ih rest)

def capabilityMeet (a b : Bool × Bool) : Bool × Bool := (a.1 && b.1, a.2 && b.2)

theorem capabilityMeet_below (left right : Bool × Bool) : CapabilityBelow (capabilityMeet left right) left := by
  obtain ⟨a, b⟩ := left
  obtain ⟨c, d⟩ := right
  cases a <;> cases b <;> cases c <;> cases d <;> simp [capabilityMeet, CapabilityBelow]

theorem CapabilitiesBelow.set {values : List (Bool × Bool)} {index : Nat} {value : Bool × Bool}
    (below : ∀ old, values[index]? = some old → CapabilityBelow value old) :
    CapabilitiesBelow (values.set index value) values := by
  induction values generalizing index with
  | nil => exact .nil
  | cons head tail ih =>
    cases index with
    | zero => exact .cons (below head rfl) (.refl tail)
    | succ index => exact .cons (.refl head) (ih (fun old row => below old row))

theorem array_set_meet_below (values : Array (Bool × Bool)) (index : Nat) (value : Bool × Bool) :
    CapabilitiesBelow
      (values.set! index (capabilityMeet (values[index]?.getD (false, false)) value)).toList values.toList := by
  rw [Array.toList_set!]
  apply CapabilitiesBelow.set
  intro old row
  have found : values[index]? = some old := by simpa using row
  rw [found]
  exact capabilityMeet_below old value

theorem capabilitiesWeight_le (values : List (Bool × Bool)) :
    capabilitiesWeight values ≤ 2 * values.length := by
  induction values with
  | nil => simp [capabilitiesWeight]
  | cons head tail ih =>
    have headBound : capabilityWeight head ≤ 2 := by
      obtain ⟨a, b⟩ := head
      cases a <;> cases b <;> simp [capabilityWeight]
    simp only [capabilitiesWeight, List.length_cons]
    omega

theorem list_forIn_invariant {α β : Type} {items : List α} {initial : β}
    {body : α → β → Id (ForInStep β)} {invariant : β → Prop}
    (preserved : ∀ item ∈ items, ∀ current, invariant current → invariant (body item current).value)
    (valid : invariant initial) : invariant (forIn items initial body : Id β) := by
  induction items generalizing initial with
  | nil => exact valid
  | cons item rest ih =>
    have one := preserved item (by simp) initial valid
    have remaining : ∀ next ∈ rest, ∀ current, invariant current → invariant (body next current).value :=
      fun next member current currentValid => preserved next (by simp [member]) current currentValid
    rw [List.forIn_cons]
    cases outcome : body item initial with
    | done next =>
      rw [outcome] at one
      exact one
    | yield next =>
      rw [outcome] at one
      exact ih remaining one

theorem array_forIn_invariant {α β : Type} {items : Array α} {initial : β}
    {body : α → β → Id (ForInStep β)} {invariant : β → Prop}
    (preserved : ∀ item ∈ items.toList, ∀ current, invariant current → invariant (body item current).value)
    (valid : invariant initial) : invariant (forIn items initial body : Id β) := by
  rw [← Array.forIn_toList]
  exact list_forIn_invariant preserved valid

def capabilityFix (step : Array (Bool × Bool) → Array (Bool × Bool)) (bottom : Array (Bool × Bool)) :
    Nat → Array (Bool × Bool) → Array (Bool × Bool)
  | 0, _ => bottom
  | fuel + 1, current =>
    let next := step current
    if next == current then current else capabilityFix step bottom fuel next

theorem capabilityFix_invariant {step : Array (Bool × Bool) → Array (Bool × Bool)}
    {bottom : Array (Bool × Bool)} {invariant : Array (Bool × Bool) → Prop}
    (descending : ∀ current, CapabilitiesBelow (step current).toList current.toList)
    (preserved : ∀ current, invariant current → invariant (step current))
    {fuel : Nat} {current : Array (Bool × Bool)}
    (enough : capabilitiesWeight current.toList < fuel) (valid : invariant current) :
    invariant (capabilityFix step bottom fuel current) := by
  induction fuel generalizing current with
  | zero => omega
  | succ fuel ih =>
    simp only [capabilityFix]
    by_cases stable : (step current == current) = true
    · simp only [stable, ite_true]
      exact valid
    · simp only [stable, Bool.false_eq_true, ite_false]
      have different : (step current).toList ≠ current.toList := by
        intro same
        have sameArray : step current = current := Array.toList_inj.mp same
        simp [sameArray] at stable
      have smaller := (descending current).weight_lt_of_ne different
      exact ih (by omega) (preserved current valid)

theorem capabilityFix_stable {step : Array (Bool × Bool) → Array (Bool × Bool)}
    {bottom : Array (Bool × Bool)}
    (descending : ∀ current, CapabilitiesBelow (step current).toList current.toList)
    {fuel : Nat} {current : Array (Bool × Bool)}
    (enough : capabilitiesWeight current.toList < fuel) :
    step (capabilityFix step bottom fuel current) = capabilityFix step bottom fuel current := by
  induction fuel generalizing current with
  | zero => omega
  | succ fuel ih =>
    simp only [capabilityFix]
    by_cases stable : (step current == current) = true
    · simp only [stable, ite_true]
      exact eq_of_beq stable
    · simp only [stable, Bool.false_eq_true, ite_false]
      have different : (step current).toList ≠ current.toList := by
        intro same
        have sameArray : step current = current := Array.toList_inj.mp same
        simp [sameArray] at stable
      have smaller := (descending current).weight_lt_of_ne different
      exact ih (by omega)

theorem permissionRound_descending (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) (caps : Array (Bool × Bool)) :
    CapabilitiesBelow (func.permissionRound globalKinds structs types caps).toList caps.toList := by
  unfold Func.permissionRound
  cases entry : func.blocks[0]? with
  | none =>
    simp only [Id.run, pure, bind]
    apply array_forIn_invariant (invariant := fun (values : Array (Bool × Bool)) => CapabilitiesBelow values.toList caps.toList)
    · intro block member current prior
      simp only [ForInStep.value]
      apply list_forIn_invariant (invariant := fun (values : Array (Bool × Bool)) => CapabilitiesBelow values.toList caps.toList)
      · intro inst member next checked
        cases inst with
        | «def» value op =>
          exact (array_set_meet_below next value _).trans checked
        | eff effect => exact checked
        | term term =>
          simp only [ForInStep.value]
          apply list_forIn_invariant (invariant := fun (values : Array (Bool × Bool)) => CapabilitiesBelow values.toList caps.toList)
          · intro edge member next checked
            obtain ⟨target, args⟩ := edge
            cases destination : func.blocks[target]? with
            | none => simpa only [ForInStep.value] using checked
            | some block =>
              simp only [ForInStep.value]
              apply list_forIn_invariant (invariant := fun (values : Array (Bool × Bool)) => CapabilitiesBelow values.toList caps.toList)
              · intro entry member next checked
                obtain ⟨⟨value, ty⟩, arg⟩ := entry
                exact (array_set_meet_below next value _).trans checked
              · exact checked
          · exact checked
      · exact prior
    · exact .refl _
  | some block =>
    simp only [Id.run, pure, bind]
    apply array_forIn_invariant (invariant := fun (values : Array (Bool × Bool)) => CapabilitiesBelow values.toList caps.toList)
    · intro block member current prior
      simp only [ForInStep.value]
      apply list_forIn_invariant (invariant := fun (values : Array (Bool × Bool)) => CapabilitiesBelow values.toList caps.toList)
      · intro inst member next checked
        cases inst with
        | «def» value op =>
          exact (array_set_meet_below next value _).trans checked
        | eff effect => exact checked
        | term term =>
          simp only [ForInStep.value]
          apply list_forIn_invariant (invariant := fun (values : Array (Bool × Bool)) => CapabilitiesBelow values.toList caps.toList)
          · intro edge member next checked
            obtain ⟨target, args⟩ := edge
            cases destination : func.blocks[target]? with
            | none => simpa only [ForInStep.value] using checked
            | some block =>
              simp only [ForInStep.value]
              apply list_forIn_invariant (invariant := fun (values : Array (Bool × Bool)) => CapabilitiesBelow values.toList caps.toList)
              · intro entry member next checked
                obtain ⟨⟨value, ty⟩, arg⟩ := entry
                exact (array_set_meet_below next value _).trans checked
              · exact checked
          · exact checked
      · exact prior
    · apply list_forIn_invariant (invariant := fun (values : Array (Bool × Bool)) => CapabilitiesBelow values.toList caps.toList)
      · intro entry member next checked
        obtain ⟨value, ty⟩ := entry
        exact (array_set_meet_below next value _).trans checked
      · exact .refl _

theorem permissionFix_eq (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) (fuel : Nat) (caps : Array (Bool × Bool)) :
    func.permissionFix globalKinds structs types fuel caps =
      capabilityFix (func.permissionRound globalKinds structs types)
        (Array.replicate func.numValues (false, false)) fuel caps := by
  induction fuel generalizing caps with
  | zero => rfl
  | succ fuel ih =>
    simp only [Func.permissionFix, capabilityFix]
    split
    · rfl
    · exact ih _

theorem permissionsFromTables_stable (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) :
    func.permissionRound globalKinds structs types (func.permissionsFromTables globalKinds structs types) =
      func.permissionsFromTables globalKinds structs types := by
  rw [Func.permissionsFromTables, permissionFix_eq]
  apply capabilityFix_stable (permissionRound_descending globalKinds structs func types)
  have weight := capabilitiesWeight_le (Array.replicate func.numValues (true, true)).toList
  simp only [Array.length_toList, Array.size_replicate] at weight
  omega

theorem permissionsFromTables_invariant {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {types : Array (Option VTy)} {invariant : Array (Bool × Bool) → Prop}
    (preserved : ∀ current, invariant current → invariant (func.permissionRound globalKinds structs types current))
    (initial : invariant (Array.replicate func.numValues (true, true))) :
    invariant (func.permissionsFromTables globalKinds structs types) := by
  rw [Func.permissionsFromTables, permissionFix_eq]
  apply capabilityFix_invariant (permissionRound_descending globalKinds structs func types) preserved ?_ initial
  have weight := capabilitiesWeight_le (Array.replicate func.numValues (true, true)).toList
  simp only [Array.length_toList, Array.size_replicate] at weight
  omega

end Goose.Lower.Validation
