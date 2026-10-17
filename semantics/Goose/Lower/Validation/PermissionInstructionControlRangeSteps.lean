import Goose.Lower.Validation.PermissionInstructionControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def CountingPermissionFree : Op → Prop
  | .cmp .. | .next .. | .arrayLen .. | .viewLen .. | .constInt .. | .refElem .. => True
  | _ => False

theorem FreshPermissionInstruction.counting {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {state : LS} {value : ValueId} {op : Op} (free : CountingPermissionFree op) :
    FreshPermissionInstruction module func le first state (.def value op) := by
  cases op <;> simp only [CountingPermissionFree] at free
  all_goals try contradiction
  all_goals
    constructor
    · constructor
      · intro a b c impossible; cases impossible
      · intro a b c d e impossible; cases impossible
      · intro a impossible; cases impossible
      · intro a b impossible; cases impossible
      · intro a b c impossible; cases impossible
      · intro a b c d impossible; cases impossible
      · intro a b c d e impossible; cases impossible
      · intro a b c d impossible; cases impossible
      · intro a b impossible; cases impossible
    · constructor
      · intro a b c impossible; cases impossible
      · intro a b c impossible; cases impossible

theorem NewPermissionInstructions.counting {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {value : ValueId} {op : Op}
    (run : Goose.Lower.emitDef op le before = (value,after)) (free : CountingPermissionFree op) :
    NewPermissionInstructions module func le first before after :=
  .emitDef run (fun _ => .counting free)

theorem generatedTargetFrame_rangeBackNext (depth exit header : Nat) (hint : IntTy) (counter : ValueId) :
    GeneratedTargetFrameRun (some ⟨depth,exit,.next header hint counter⟩) (rangeBack hint counter header) := by
  unfold rangeBack
  refine GeneratedTargetFrameRun.bind (generatedTargetFrame_isLive _) fun live => ?_
  cases live with
  | false => exact generatedTargetFrame_pure _ _
  | true =>
    refine GeneratedTargetFrameRun.bind (generatedTargetFrame_emitDef _ _) fun value => ?_
    apply generatedTargetFrame_emitTerm
    intro base target member bound
    simp only [Term.successors,List.mem_singleton] at member
    subst target
    exact Or.inr rfl

theorem FreshPermissionInstruction.rangeBack {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {instruction : Inst} {result : Unit}
    {depth exit header : Nat} {hint : IntTy} {counter : ValueId}
    (permitted : FreshPermissionInstruction module func le first before instruction)
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (frames : LoopBuilderFrames (some ⟨depth,exit,.next header hint counter⟩) before)
    (run : Goose.Lower.rangeBack hint counter header le before = (result,after)) :
    FreshPermissionInstruction module func le first after instruction := by
  have afterDense := dense_rangeBack hint counter header le before result after run checked bounded
  have advanced := advB_rangeBack hint counter header le before result after run
  have framed := generatedTargetFrame_rangeBackNext depth exit header hint counter
    before le before result after (.refl _) frames (.refl _ _) run
  exact permitted.retained checked afterDense.1 advanced.ext advanced.vals
    (types_rangeBack hint counter header le before result after run) frames framed.1

theorem rangeBack_newPermissionInstructions {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {result : Unit} {header counter : Nat} {hint : IntTy}
    (run : rangeBack hint counter header le before = (result,after)) :
    NewPermissionInstructions module func le first before after := by
  unfold rangeBack at run
  obtain ⟨live,middle,test,tail⟩ := bind_eq.mp run
  have same : middle = before := by
    have stable : (isLive le before).2 = before := rfl
    rw [test] at stable
    exact stable
  subst middle
  cases live with
  | false =>
    simp only [Bool.false_eq_true,ite_false,pure_run] at tail
    obtain ⟨_,rfl⟩ := Prod.mk.inj tail
    exact .of_blocks_eq rfl
  | true =>
    simp only [ite_true,bind_eq] at tail
    obtain ⟨value,middle,emitted,branched⟩ := tail
    intro instruction member
    rcases NewPermissionInstructions.branch branched instruction member with old | issued
    · cases current : before.cur with
      | none =>
        rw [emitDef_none _ le current] at emitted
        obtain ⟨_,rfl⟩ := Prod.mk.inj emitted
        exact Or.inl old
      | some block =>
        rw [emitDef_run _ le current] at emitted
        obtain ⟨_,rfl⟩ := Prod.mk.inj emitted
        rcases permission_appendInst_membership old with original | rfl
        · exact Or.inl original
        · exact Or.inr (.counting trivial)
    · exact Or.inr issued

#print axioms FreshPermissionInstruction.rangeBack
#print axioms rangeBack_newPermissionInstructions

end Goose.Lower.Validation
