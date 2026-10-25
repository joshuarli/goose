import Goose.Construct.Validate
import Goose.Proofs.ExitExecutionFixedPrefixReads
import Lean

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

private theorem except_bind_ok {α β ε : Type} (action : Except ε α)
    (next : α → Except ε β) (result : β) :
    (action >>= next) = .ok result ↔ ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action <;> simp [bind, Except.bind]

private theorem forIn'_members {α β ε : Type} (items : List α)
    (body : (item : α) → item ∈ items → β → Except ε (ForInStep β))
    (initial final : β) (checked : forIn' items initial body = .ok final)
    (yields : ∀ item member accumulator step, body item member accumulator = .ok step →
      ∃ next, step = .yield next) :
    ∀ item member, ∃ accumulator next, body item member accumulator = .ok (.yield next) := by
  cases items with
  | nil => intro item member; cases member
  | cons head tail =>
      rw [List.forIn'_cons] at checked
      obtain ⟨step, first, rest⟩ := (except_bind_ok _ _ _).mp checked
      obtain ⟨next, rfl⟩ := yields head (by simp) initial step first
      intro item member
      rcases List.mem_cons.mp member with same | remaining
      · subst item; exact ⟨initial, next, first⟩
      · exact forIn'_members tail _ next final rest
          (fun item member accumulator step success => yields item (List.mem_cons_of_mem _ member) accumulator step success)
          item remaining
termination_by items.length

open Lean Elab Tactic in
elab "unfold_exit_struct_tables" : tactic => do
  let information ← getConstInfo ``Goose.Construct.validate
  let some value := information.value? | throwError "expected validation definition"
  let some operation := value.find? (fun expression =>
    match expression with
    | .const name _ => name.toString.endsWith ".checkStructTables"
    | _ => false) | throwError "expected struct table validation"
  evalTactic (← `(tactic| unfold $(mkIdent operation.constName!) at *))

theorem validated_fixedLayoutFieldBounds (module : Module) (accepted : validate module = .ok ()) :
    FixedLayoutFieldBounds (.ofModule module) := by
  unfold validate at accepted
  obtain ⟨_, _, accepted⟩ := (except_bind_ok _ _ _).mp accepted
  obtain ⟨value, checked, _⟩ := (except_bind_ok _ _ _).mp accepted
  cases value
  unfold_exit_struct_tables
  obtain ⟨token, checked, _⟩ := (except_bind_ok _ _ _).mp checked
  cases token
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size] at checked
  have each := forIn'_members _ _ _ _ checked (by
    intro index member accumulator step success
    repeat
      first
      | (split at success)
      | (obtain ⟨_, _, success⟩ := (except_bind_ok _ _ _).mp success)
      | (simp only [Core.reject, bind, Except.bind] at success; cases success)
      | exact ⟨_, (Except.ok.inj success).symm⟩)
  intro id descriptor present field member
  have indexBound := (Array.getElem?_eq_some_iff.mp present).1
  have selected := each id (by
    apply List.mem_range'.mpr
    exact ⟨id, by simpa only [LayoutEnv.ofModule, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] using indexBound, by simp⟩)
  obtain ⟨accumulator, next, row⟩ := selected
  change module.structs[id]? = some descriptor at present
  have descriptorEq := (Array.getElem?_eq_some_iff.mp present).2
  simp only [descriptorEq, Core.reject, bind, Except.bind] at row
  split at row
  · cases row
  · split at row
    · obtain ⟨endOffset, fieldChecks, _⟩ := (except_bind_ok _ _ _).mp row
      rw [← Array.forIn_toList] at fieldChecks
      have fieldEach := forIn'_members descriptor.fields.toList
        (fun field _ accumulator => _) 0 endOffset (by exact fieldChecks) (by
          intro selected selectedMember accumulator step success
          obtain ⟨_, _, success⟩ := (except_bind_ok _ _ _).mp success
          repeat
            first
            | (solve | cases success)
            | split at success
            | (simp only [Core.reject, bind, Except.bind] at success; cases success)
            | exact ⟨_, (Except.ok.inj success).symm⟩)
      obtain ⟨offset, next, fieldChecked⟩ := fieldEach field member
      obtain ⟨_, _, fieldChecked⟩ := (except_bind_ok _ _ _).mp fieldChecked
      split at fieldChecked
      · cases sized : fixedByteSize? (LayoutEnv.ofModule module) field.ty with
        | none => simp only [sized] at fieldChecked; cases fieldChecked
        | some width =>
          simp only [sized] at fieldChecked
          split at fieldChecked
          · split at fieldChecked
            · rename_i bound
              exact ⟨width, rfl, bound⟩
            · cases fieldChecked
          · cases fieldChecked
      · cases fieldChecked
    · cases row

#print axioms validated_fixedLayoutFieldBounds

end Goose.Proofs.ExitExecution
