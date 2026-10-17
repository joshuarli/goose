import Goose.Lower.Validation.FreshRunLiterals
import Goose.Lower.Validation.CfgReturnBits

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem forIn_member_invariant {property : σ → Prop} (items : List α) (start : σ)
    (body : α → σ → Id (ForInStep σ)) (initial : property start)
    (preserved : ∀ item ∈ items, ∀ state, property state → property (body item state).value) :
    property (forIn items start body) := by
  induction items generalizing start with
  | nil => exact initial
  | cons first rest ih =>
    rw [List.forIn_cons]
    have next := preserved first (by simp) start initial
    cases step : body first start with
    | done final =>
      change property final
      simpa [step] using next
    | yield mid =>
      apply ih mid
      · simpa [step] using next
      · intro item member state checked
        exact preserved item (by simp [member]) state checked

def FreshRoundState (initial : Array Bool) (state : Array Bool × Bool) : Prop :=
  ReturnBitsLE initial state.1 ∧
    (state.2 = false → state.1 = initial) ∧
    (state.2 = true → initial.count true < state.1.count true)

private theorem freshRoundState_set {initial flags : Array Bool} {changed : Bool}
    (checked : FreshRoundState initial (flags, changed)) {value : ValueId}
    (bounded : value < flags.size) (absent : flags[value]! = false) :
    FreshRoundState initial (flags.set! value true, true) := by
  have order : ReturnBitsLE flags (flags.set! value true) :=
    ⟨(trueFlags_set flags value).1.symm, (trueFlags_set flags value).2⟩
  have old : flags[value]? = some false := by
    rw [Array.getElem?_eq_getElem bounded]
    have exactValue : flags[value] = false := by simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem bounded] using absent
    simp [exactValue]
  have fresh : (flags.set! value true)[value]? = some true := by
    simp [Array.getElem?_setIfInBounds, bounded]
  have different : flags ≠ flags.set! value true := by
    intro equal
    rw [equal] at old
    rw [fresh] at old
    contradiction
  refine ⟨checked.1.trans order, by simp, ?_⟩
  intro _
  exact Nat.lt_of_le_of_lt checked.1.count.1 (order.strict different)

theorem freshRunRound_progress (func : Func) (flags : Array Bool)
    (parameters : ∀ block ∈ func.blocks.toList, ∀ param ∈ block.params, param.1 < flags.size) :
    FreshRoundState flags (freshRunRound func flags) := by
  unfold freshRunRound
  change FreshRoundState flags (forIn' (m := Id) [:func.blocks.size] (flags, false) _)
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply list_forIn'_invariant (property := FreshRoundState flags)
  · exact ⟨.refl flags, fun _ => rfl, by simp⟩
  · intro target member state checked
    have targetBound : target < func.blocks.size := by
      have bounds := List.mem_range'.mp member
      simp [Std.Legacy.Range.size] at bounds
      omega
    apply forIn_member_invariant (property := FreshRoundState flags)
    · exact checked
    · intro item itemMember state checked
      obtain ⟨⟨value, ty⟩, index⟩ := item
      have paramMember : (value, ty) ∈ func.blocks[target].params :=
        List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp itemMember)
      have bounded := parameters func.blocks[target]
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem (h := targetBound) rfl)) _ paramMember
      have currentBound : value < state.1.size := by rw [← checked.1.1]; exact bounded
      dsimp only
      split
      · rename_i guard
        apply freshRoundState_set checked currentBound
        cases valueAt : state.1[value]! <;> simp_all
      · exact checked

theorem literalRunSeeds_size (func : Func) (types : Array (Option VTy)) :
    (literalRunSeeds func types).size = func.numValues := by
  unfold literalRunSeeds
  change ((forIn (m := Id) func.blocks (Array.replicate func.numValues false) _)).size = func.numValues
  rw [← Array.forIn_toList]
  apply list_forIn_invariant (property := fun flags : Array Bool => flags.size = func.numValues)
  · simp
  · intro block flags sized
    apply list_forIn_invariant (property := fun flags : Array Bool => flags.size = func.numValues)
    · exact sized
    · intro inst flags sized
      cases inst with
      | «def» value op =>
        cases op <;> try exact sized
        dsimp only
        split
        · change (flags.set! value true).size = func.numValues
          simpa only [Array.size_set!] using sized
        · exact sized
      | _ => exact sized

theorem freshRuns_rounds (func : Func) (types : Array (Option VTy)) :
    freshRuns func types = dataflowRounds (freshRunRound func) (literalRunSeeds func types)
      true (func.numValues + 1) := rfl

theorem freshRuns_size (func : Func) (types : Array (Option VTy)) :
    (freshRuns func types).size = func.numValues := by
  rw [freshRuns_rounds]
  apply dataflowRounds_invariant (property := fun flags : Array Bool => flags.size = func.numValues)
  · intro flags sized
    exact (freshRunRound_preserves_true func flags).1.trans sized
  · exact literalRunSeeds_size func types

theorem freshRuns_fixed (func : Func) (types : Array (Option VTy))
    (parameters : ∀ block ∈ func.blocks.toList, ∀ param ∈ block.params, param.1 < func.numValues) :
    (freshRunRound func (freshRuns func types)).1 = freshRuns func types := by
  change (freshRunRound func (dataflowRounds (freshRunRound func) (literalRunSeeds func types)
    true (func.numValues + 1))).1 = _
  apply dataflowRounds_stable (property := fun flags : Array Bool => flags.size = func.numValues)
    (measure := fun flags => flags.size - flags.count true)
  · intro flags sized
    have checked := freshRunRound_progress func flags (by simpa only [sized] using parameters)
    refine ⟨checked.1.1.symm.trans sized, ?_⟩
    intro changed
    have strict := checked.2.2 changed
    have countBound := Array.count_le_size (a := true) (xs := (freshRunRound func flags).1)
    have size := checked.1.1
    omega
  · intro flags sized unchanged
    exact (freshRunRound_progress func flags (by simpa only [sized] using parameters)).2.1 unchanged
  · exact literalRunSeeds_size func types
  · have sized := literalRunSeeds_size func types
    omega

theorem freshRunRound_parameter (func : Func) (flags : Array Bool)
    {target : BlockId} (targetBound : target < func.blocks.size)
    {value : ValueId} {ty : VTy} {index : Nat}
    (parameter : func.blocks[target].params[index]? = some (value, ty))
    (bounded : value < flags.size)
    (nonempty : incomingValues func target index ≠ [])
    (incoming : ∀ source ∈ incomingValues func target index, flags[source]? = some true) :
    (freshRunRound func flags).1[value]? = some true := by
  unfold freshRunRound
  change ((forIn' (m := Id) [:func.blocks.size] (flags, false) _).1)[value]? = some true
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  refine list_forIn'_establishes
    (property := fun state : Array Bool × Bool => TrueFlagsPreserved flags state.1)
    (known := fun state => state.1[value]? = some true)
    _ _ _ target ?_ (.refl flags) ?_ ?_ ?_ ?_
  · simp only [List.mem_range']
    simp [Std.Legacy.Range.size, targetBound]
  · intro block member state checked
    apply list_forIn_invariant (property := fun state : Array Bool × Bool => TrueFlagsPreserved flags state.1)
    · exact checked
    · intro param state checked
      obtain ⟨⟨result, ty⟩, index⟩ := param
      dsimp only
      split
      · exact checked.trans (trueFlags_set _ _)
      · exact checked
  · intro block member state known
    apply list_forIn_invariant (property := fun state : Array Bool × Bool => state.1[value]? = some true)
    · exact known
    · intro param state known
      obtain ⟨⟨result, ty⟩, index⟩ := param
      dsimp only
      split
      · exact (trueFlags_set _ _).2 value known
      · exact known
  · intro block member state
    exact ⟨_, rfl⟩
  · intro state checked
    apply list_forIn_establishes
      (property := fun state : Array Bool × Bool => TrueFlagsPreserved flags state.1)
      (known := fun state => state.1[value]? = some true)
      (target := ((value, ty), index))
      (member := List.mk_mem_zipIdx_iff_getElem?.mpr parameter)
    · exact checked
    · intro param state checked
      obtain ⟨⟨result, ty⟩, index⟩ := param
      dsimp only
      split
      · exact checked.trans (trueFlags_set _ _)
      · exact checked
    · intro param state known
      obtain ⟨⟨result, ty⟩, index⟩ := param
      dsimp only
      split
      · exact (trueFlags_set _ _).2 value known
      · exact known
    · intro param state
      obtain ⟨⟨result, ty⟩, index⟩ := param
      dsimp only
      split <;> exact ⟨_, rfl⟩
    · intro state checked
      have currentBound : value < state.1.size := by rw [checked.1]; exact bounded
      have allIncoming : (incomingValues func target index).all
          (fun source => state.1[source]?.getD false) = true := by
        apply List.all_eq_true.mpr
        intro source member
        simp [checked.2 source (incoming source member)]
      have presentIncoming : (incomingValues func target index).isEmpty = false :=
        List.isEmpty_eq_false_iff.mpr nonempty
      dsimp only
      by_cases already : state.1[value]! = true
      · simp only [already, Bool.not_true, Bool.false_and, ite_false]
        have row : state.1[value]? = some true := by
          rw [Array.getElem?_eq_getElem currentBound]
          simpa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_getElem currentBound] using already
        exact row
      · have absent : state.1[value]! = false := Bool.eq_false_iff.mpr already
        simp only [absent, Bool.not_false, presentIncoming, allIncoming,
          Bool.and_self, ite_true]
        change (state.1.set! value true)[value]? = some true
        simp [Array.getElem?_setIfInBounds, currentBound]

theorem freshRuns_parameter (func : Func) (types : Array (Option VTy))
    (parameters : ∀ block ∈ func.blocks.toList, ∀ param ∈ block.params, param.1 < func.numValues)
    {target : BlockId} (targetBound : target < func.blocks.size)
    {value : ValueId} {ty : VTy} {index : Nat}
    (parameter : func.blocks[target].params[index]? = some (value, ty))
    (nonempty : incomingValues func target index ≠ [])
    (incoming : ∀ source ∈ incomingValues func target index,
      (freshRuns func types)[source]? = some true) :
    (freshRuns func types)[value]? = some true := by
  have bounded : value < (freshRuns func types).size := by
    rw [freshRuns_size]
    exact parameters func.blocks[target]
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem (h := targetBound) rfl)) _
      (List.mem_of_getElem? parameter)
  have discovered := freshRunRound_parameter func (freshRuns func types) targetBound
    parameter bounded nonempty incoming
  rw [freshRuns_fixed func types parameters] at discovered
  exact discovered

inductive FreshLiteralValue (func : Func) (types : Array (Option VTy)) : ValueId → Prop
  | literal {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
      {value : ValueId} {ty : Ty} {values : List ValueId}
      (definition : Inst.def value (.arrLit ty values) ∈ block.insts)
      (runType : isLiteralRunType ty = true) (typed : types[value]? = some (some (.data ty)))
      (bounded : value < func.numValues) : FreshLiteralValue func types value
  | parameter {target : BlockId} (targetBound : target < func.blocks.size)
      {value : ValueId} {ty : VTy} {index : Nat}
      (row : func.blocks[target].params[index]? = some (value, ty))
      (nonempty : incomingValues func target index ≠ [])
      (incoming : ∀ source ∈ incomingValues func target index, FreshLiteralValue func types source) :
      FreshLiteralValue func types value

theorem FreshLiteralValue.checked {func : Func} {types : Array (Option VTy)} {value : ValueId}
    (source : FreshLiteralValue func types value)
    (parameters : ∀ block ∈ func.blocks.toList, ∀ param ∈ block.params, param.1 < func.numValues) :
    (freshRuns func types)[value]? = some true := by
  induction source with
  | literal blockMember definition runType typed bounded =>
    exact freshRuns_literal func types blockMember definition runType typed bounded
  | parameter targetBound row nonempty incoming ih =>
    exact freshRuns_parameter func types parameters targetBound row nonempty ih

end Goose.Lower.Validation
