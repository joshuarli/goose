import Goose.Evidence.SimulationFixtures
import Goose.Evidence.Provenance

namespace Goose.Proofs.Bounds.SimulationChecks

open Goose.Core Goose.GIR Goose.Evidence

private theorem instruction_bounds {variant : Variant} {placement : Placement} {point : Pt} {instruction : Inst}
    (atInstruction : instAt (mainFunction variant placement) point = some instruction) :
    point.1 < 4 ∧ point.2 < 10 := by
  unfold instAt at atInstruction
  cases blockAt : (mainFunction variant placement).blocks[point.1]? with
  | none => simp [blockAt] at atInstruction
  | some block =>
    simp only [blockAt, Option.bind_some] at atInstruction
    have blockBound := (Array.getElem?_eq_some_iff.mp blockAt).1
    have instBound := (List.getElem?_eq_some_iff.mp atInstruction).1
    have member := Array.mem_of_getElem? blockAt
    have size : block.insts.length ≤ 10 :=
      of_decide_eq_true (List.all_eq_true.mp (block_lengths variant placement) block (Array.mem_toList_iff.mpr member))
    have tableSize : (mainFunction variant placement).blocks.size ≤ 4 := by cases placement <;> simp [mainFunction]
    exact ⟨Nat.lt_of_lt_of_le blockBound tableSize, Nat.lt_of_lt_of_le instBound size⟩

private theorem constant_location {variant : Variant} {placement : Placement} {point : Pt} {operation : Op}
    (instruction : instAt (mainFunction variant placement) point = some (.def 0 operation)) : point = (0, 0) := by
  obtain ⟨blocks, offsets⟩ := instruction_bounds instruction
  have position := constant_position variant placement ⟨point.1, blocks⟩ ⟨point.2, offsets⟩
    (by simp [instruction, defines])
  exact Prod.ext position.1 position.2

private theorem comparison_location {variant : Variant} {placement : Placement} {point : Pt} {operation : Op}
    (instruction : instAt (mainFunction variant placement) point = some (.def 5 operation)) : point = (0, 7) := by
  obtain ⟨blocks, offsets⟩ := instruction_bounds instruction
  have position := comparison_position variant placement ⟨point.1, blocks⟩ ⟨point.2, offsets⟩
    (by simp [instruction, defines])
  exact Prod.ext position.1 position.2

private theorem array_length_location {variant : Variant} {placement : Placement} {point : Pt} {operation : Op}
    (instruction : instAt (mainFunction variant placement) point = some (.def 4 operation)) : point = (0, 6) := by
  obtain ⟨blocks, offsets⟩ := instruction_bounds instruction
  have position := array_length_position variant placement ⟨point.1, blocks⟩ ⟨point.2, offsets⟩
    (by simp [instruction, defines])
  exact Prod.ext position.1 position.2

private theorem no_parameters (variant : Variant) (placement : Placement) (id : ValueId) :
    ∀ block ∈ (mainFunction variant placement).blocks, id ∉ block.params.map Prod.fst := by
  intro block member
  have empty := List.all_eq_true.mp (block_parameters variant placement) block (Array.mem_toList_iff.mpr member)
  have noParams : block.params = [] := by simpa using empty
  simp [noParams]

private theorem index_constant {variant : Variant} {placement : Placement} {profile : NumProfile} {point : Pt} {fr : Frame}
    {state : St} {value : RVal}
    (reachable : RuntimePoint ⟨profile, fixture variant placement⟩ (mainFunction variant placement) point fr state)
    (cell : fr.vals[0]? = some value) : value = .val (.int .i64 0) := by
  obtain ⟨sourcePoint, sourceFrame, sourceState, operation, fuel, writtenState,
    sourceReachable, instruction, evaluated, history⟩ := reachable.def_cell_sample cell (no_parameters variant placement 0)
  have location := constant_location instruction
  subst sourcePoint
  have operationEq : operation = .constInt .i64 0 := by
    cases placement <;> simpa [instAt, mainFunction, entryBlock] using instruction.symm
  subst operation
  simp only [execOp, execPure, pure_apply, Res.ok.injEq] at evaluated
  exact evaluated.1.symm

private theorem control_rank {variant : Variant} {placement : Placement} {before after : Pt}
    (step : ControlStep (mainFunction variant placement) before after) : rank before < rank after := by
  cases step with
  | definition | effect => simp [rank]
  | branch instruction successor =>
    obtain ⟨blocks, offsets⟩ := instruction_bounds instruction
    have allRanks := branch_ranks variant placement ⟨before.1, blocks⟩ ⟨before.2, offsets⟩
    simp only [instruction] at allRanks
    exact of_decide_eq_true (List.all_eq_true.mp allRanks _ successor)

private theorem operands_unwritten {variant : Variant} {placement : Placement} {before after : Pt}
    (step : ControlStep (mainFunction variant placement) before after) (afterComparison : 8 ≤ rank before) :
    ∀ id ∈ [0, 4], id ∉ stepWrites (mainFunction variant placement) before after := by
  intro id member
  cases step with
  | definition instruction =>
    simp only [stepWrites, instruction, List.mem_singleton]
    intro same
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · subst_vars
      have atStart := constant_location instruction
      rw [atStart] at afterComparison
      simp [rank] at afterComparison
    · subst_vars
      have atLength := array_length_location instruction
      rw [atLength] at afterComparison
      simp [rank] at afterComparison
  | effect instruction => simp [stepWrites, instruction]
  | branch instruction successor =>
    rename_i term target
    simp only [stepWrites, instruction]
    cases blockAt : (mainFunction variant placement).blocks[target]? with
    | none => simp
    | some block =>
      simp only [Option.map_some, Option.getD_some]
      exact no_parameters variant placement id block (Array.mem_of_getElem? blockAt)

private theorem protect_operands {variant : Variant} {placement : Placement} {profile : NumProfile}
    {ids : List ValueId} {before after : Pt} {fr next : Frame} {state final : St}
    (history : RuntimeStepsAvoid ⟨profile, fixture variant placement⟩ (mainFunction variant placement)
      ids before fr state after next final) (afterComparison : 8 ≤ rank before) :
    RuntimeStepsAvoid ⟨profile, fixture variant placement⟩ (mainFunction variant placement)
      [0, 4] before fr state after next final := by
  induction history with
  | refl => exact .refl
  | next transition _ rest ih =>
    have increases := control_rank transition.control
    exact .next transition (operands_unwritten transition.control afterComparison) (ih (by omega))

private theorem comparison_metadata {variant : Variant} {placement : Placement}
    {condition left right : ValueId}
    (definition : (mainFunction variant placement).defOp? condition = some (.cmp .lt .i64 left right)) :
    condition = 5 ∧ left = 0 ∧ right = 4 := by
  obtain ⟨block, member, instruction⟩ := defOp_member definition
  have inBody : .def condition (.cmp .lt .i64 left right) ∈
      (mainFunction variant placement).blocks.toList.flatMap (·.insts) :=
    List.mem_flatMap.mpr ⟨block, Array.mem_toList_iff.mpr member, instruction⟩
  cases variant <;> cases placement <;>
    simpa [mainFunction, entryBlock, indexBlock, falseBlock, dispatchBlock] using inBody

private theorem helper_has_no_comparison {variant : Variant} {condition left right : ValueId}
    (definition : (helperFunction variant).defOp? condition = some (.cmp .lt .i64 left right)) : False := by
  obtain ⟨block, member, instruction⟩ := defOp_member definition
  have inBody : .def condition (.cmp .lt .i64 left right) ∈
      (helperFunction variant).blocks.toList.flatMap (·.insts) :=
    List.mem_flatMap.mpr ⟨block, Array.mem_toList_iff.mpr member, instruction⟩
  cases variant <;> simp [helperFunction] at inBody

theorem fixture_comparisons (variant : Variant) (placement : Placement) (profile : NumProfile) :
    TrueComparisonFacts ⟨profile, fixture variant placement⟩ := by
  intro fn point fr state condition yes yesArgs no noArgs left right reachable branch definition cell
  have member := reachable.function_mem
  have functionCases : fn = mainFunction variant placement ∨ fn = helperFunction variant := by
    simpa [Module.allFuncs, fixture] using member
  rcases functionCases with rfl | rfl
  · obtain ⟨rfl, rfl, rfl⟩ := comparison_metadata definition
    obtain ⟨sourcePoint, sourceFrame, sourceState, operation, fuel, writtenState,
      sourceReachable, instruction, evaluated, history⟩ :=
      reachable.def_cell_sample cell (no_parameters variant placement 5)
    have location := comparison_location instruction
    subst sourcePoint
    have operationEq : operation = .cmp .lt .i64 0 4 := by
      cases placement <;> simpa [instAt, mainFunction, entryBlock] using instruction.symm
    subst operation
    have preserved := protect_operands history (by decide : 8 ≤ rank (0, 8))
    obtain ⟨leftValue, rightValue, compared, leftCell, rightCell, compatible, less⟩ := cmp_true_cells evaluated
    have leftEq : leftValue = .int .i64 0 := RVal.val.inj (index_constant sourceReachable leftCell)
    subst leftValue
    cases rightValue with
    | int rightType rightNumber =>
      have fact : FactHolds sourceFrame sourceState (.lt 0 4) :=
        cmp_true_facts ⟨.i64, leftCell⟩ ⟨rightType, rightCell⟩ (by simpa only [execOp] using evaluated)
      apply FactHolds.sameCells (hold := fact)
      intro id mentioned
      simp only [Fact.mentions, Bool.or_eq_true, beq_iff_eq] at mentioned
      rcases mentioned with zero | four
      · subst id
        simpa [Frame.set, Std.HashMap.getElem?_insert] using preserved.preserves_cell (by simp : 0 ∈ [0, 4])
      · subst id
        simpa [Frame.set, Std.HashMap.getElem?_insert] using preserved.preserves_cell (by simp : 4 ∈ [0, 4])
    | _ => simp [expectComparable, fault, M.stop] at compatible
  · exact False.elim (helper_has_no_comparison definition)

theorem fixture_run_replacement (variant : Variant) (placement : Placement) (profile : NumProfile) (fuel : Nat) :
    run fuel profile (checkedModule (fixture variant placement)) = run fuel profile (fixture variant placement) :=
  checked_run (fixture_accepted variant placement) profile (fixture_comparisons variant placement profile) fuel

theorem fixture_reachable_facts (variant : Variant) (placement : Placement) (profile : NumProfile)
    {fn : Func} {point : Pt} {fr : Frame} {state : St}
    (reachable : RuntimePoint ⟨profile, fixture variant placement⟩ fn point fr state)
    (certificate : FactCertificate) (present : fn.certificate = some certificate) :
    PointFactsHold ⟨⟨profile, fixture variant placement⟩, fn⟩ certificate point fr state :=
  reachable_facts (fixture_accepted variant placement) (fixture_comparisons variant placement profile)
    reachable certificate present

def expectedResult (variant : Variant) : Result → Bool
  | .done .returned trace =>
    match variant with
    | .returned => trace == "1\n"
    | .called => trace == "1\n7\n"
    | _ => false
  | .done (.aborted .userAbort 0) trace => variant == .aborted && trace == "1\n"
  | .timeout trace => variant == .looping && trace == "1\n"
  | _ => false

#guard [Variant.returned, .aborted, .called, .looping].all fun variant =>
  [Placement.immediate, .delayed, .predecessor].all fun placement =>
    [NumProfile.release, .debug].all fun profile =>
      expectedResult variant (run 100 profile (fixture variant placement)) &&
        expectedResult variant (run 100 profile (checkedModule (fixture variant placement)))

#guard [0, 1, 2].all fun fuel =>
  match run fuel .release (fixture .returned .predecessor),
      run fuel .release (checkedModule (fixture .returned .predecessor)) with
  | .timeout original, .timeout checked => original == "" && checked == ""
  | _, _ => false

end Goose.Proofs.Bounds.SimulationChecks
