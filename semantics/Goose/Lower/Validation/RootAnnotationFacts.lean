import Goose.Core.Sound.Check
import Goose.GIR.Validate

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

private theorem forIn_yields_member {α ε : Type} {items : List α}
    {body : α → Except ε (ForInStep PUnit.{1})}
    (yielded : ∀ item step, body item = .ok step → step = .yield PUnit.unit)
    (checked : forIn items PUnit.unit (fun item _ => body item) = .ok PUnit.unit) :
    ∀ item ∈ items, body item = .ok (.yield PUnit.unit) := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    rw [List.forIn_cons] at checked
    obtain ⟨step, first, remaining⟩ := (ex_bind_ok _ _ _).mp checked
    have equal := yielded item step first
    subst step
    intro next member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact ih remaining next member

private theorem bind_yields {α ε : Type} {action : Except ε α} {step : ForInStep PUnit.{1}}
    (checked : (do let _ ← action; pure (ForInStep.yield PUnit.unit)) = .ok step) :
    step = .yield PUnit.unit := by
  cases action with
  | error error => simp [bind, Except.bind] at checked
  | ok value => simpa [bind, Except.bind, pure, Except.pure] using checked.symm

private theorem after_optional_check {α β ε : Type} {condition : Prop} [Decidable condition]
    {first : Except ε α} {after : Except ε β} {value : β}
    (checked : (if condition then first >>= fun _ => after else after) = .ok value) :
    after = .ok value := by
  by_cases selected : condition
  · simp only [selected, ite_true] at checked
    cases first with
    | error rejection => simp [bind, Except.bind] at checked
    | ok result => simpa [bind, Except.bind] using checked
  · simpa only [selected, ite_false] using checked

theorem checkRootAnnotationsOf_load_contents
    {module : GIR.Module} {types : Array (Array (Option VTy))}
    {results : Array (List RootRef)} {nRoots index : Nat} {func : Func}
    (checked : checkRootAnnotationsOf module types results nRoots index = .ok ())
    (functionAt : module.funcs[index]? = some func)
    {block : GIR.Block} (blockMember : block ∈ func.blocks.toList)
    {value address : ValueId} (instruction : .def value (.load address) ∈ block.insts)
    {mutability : Mutability} {element : Ty}
    (typed : (types[index]?.getD #[])[value]? = some (some (.data (.slice mutability element))))
    {parameter : Nat}
    (parameterRoot : .param parameter ∈
      rootsAt (func.provenance results (types[index]?.getD #[]) nRoots).vals address)
    (reference : (func.params[parameter]?).any Ty.isRefSlice = true) :
    (func.roots.contents.find? (·.1 == parameter)).isSome = true := by
  unfold checkRootAnnotationsOf at checked
  simp only [functionAt] at checked
  have remaining := after_optional_check checked
  obtain ⟨_, blocks, _⟩ := (ex_bind_ok _ _ _).mp remaining
  rw [← Array.forIn_toList] at blocks
  have blockChecked := forIn_yields_member (checked := blocks)
    (by intro item step one; exact bind_yields one) block blockMember
  obtain ⟨_, instructions, _⟩ := (ex_bind_ok _ _ _).mp blockChecked
  have instructionChecked := forIn_yields_member (checked := instructions)
    (by
      intro item step one
      cases item with
      | eff effect => simpa [pure, Except.pure] using one.symm
      | term term => simpa [pure, Except.pure] using one.symm
      | «def» result op =>
        cases op <;>
          repeat' first
          | exact bind_yields one
          | (simpa [pure, Except.pure] using one.symm)
          | (split at one)) (.def value (.load address)) instruction
  simp only [typed] at instructionChecked
  obtain ⟨_, roots, _⟩ := (ex_bind_ok _ _ _).mp instructionChecked
  have parameterChecked := forIn_yields_member (checked := roots)
    (by
      intro root step one
      cases root <;>
        repeat' first
        | exact bind_yields one
        | (simpa [pure, Except.pure] using one.symm)
        | (split at one)) (.param parameter) parameterRoot
  cases contentAt : func.roots.contents.find? (·.1 == parameter) with
  | some row => simp
  | none => simp [reference, contentAt, violation, bind, Except.bind] at parameterChecked

#print axioms checkRootAnnotationsOf_load_contents

end Goose.Lower.Validation
