import Goose.Lower.Validation.SummaryPreservationTransfer

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

theorem rootsAt_push_old {table : Array (List RootRef)} {roots : List RootRef} {index : Nat}
    (bound : index < table.size) : rootsAt (table.push roots) index = rootsAt table index := by
  simp [rootsAt, Array.getElem?_push, Nat.ne_of_lt bound]

theorem rootsAt_push_new (table : Array (List RootRef)) (roots : List RootRef) :
    rootsAt (table.push roots) table.size = roots := by
  simp [rootsAt]

theorem rootsOfDef_congr_values {res : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {before after : Prov} {result : ValueId} (op : Op)
    (values : ∀ value ∈ op.uses, rootsAt before.vals value = rootsAt after.vals value)
    (slots : before.slots = after.slots) :
    rootsOfDef res vt func before result op = rootsOfDef res vt func after result op := by
  cases op with
  | load address =>
    have same := values address (by simp [Op.uses])
    simp only [rootsOfDef, same, slots]
  | call callee args origin =>
    simp only [rootsOfDef]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro root member
    cases root with
    | param index =>
      cases argument : args[index]? with
      | none => simp [argument]
      | some value =>
        simp only [argument]
        exact values value (List.mem_of_getElem? argument)
    | _ => rfl
  | _ =>
    all_goals first | rfl | exact values _ (by simp [Op.uses])

theorem rootsOfDef_push_fresh {res : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {before : Prov} {result : ValueId} {newRoots : List RootRef} {op : Op}
    (bounds : ∀ value ∈ op.uses, value < before.vals.size) :
    rootsOfDef res vt func { before with vals := before.vals.push newRoots } result op =
      rootsOfDef res vt func before result op := by
  apply rootsOfDef_congr_values op
  · intro value member
    exact rootsAt_push_old (bounds value member)
  · rfl

theorem def_roots_closed_after_push {res : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {before : Prov} {op : Op}
    (bounds : ∀ value ∈ op.uses, value < before.vals.size) :
    let after := { before with vals := before.vals.push (rootsOfDef res vt func before before.vals.size op) }
    InstructionRootsClosed res vt func after (.def before.vals.size op) := by
  dsimp only
  change ∀ root ∈ rootsOfDef res vt func _ before.vals.size op,
    root ∈ rootsAt (before.vals.push _) before.vals.size
  rw [rootsOfDef_push_fresh bounds, rootsAt_push_new]
  exact fun _ member => member

theorem old_def_roots_closed_after_push {res : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {before : Prov} {result : ValueId} {newRoots : List RootRef} {op : Op}
    (closed : InstructionRootsClosed res vt func before (.def result op))
    (resultBound : result < before.vals.size)
    (bounds : ∀ value ∈ op.uses, value < before.vals.size) :
    InstructionRootsClosed res vt func { before with vals := before.vals.push newRoots }
      (.def result op) := by
  change ∀ root ∈ rootsOfDef res vt func _ result op,
    root ∈ rootsAt (before.vals.push newRoots) result
  rw [rootsOfDef_push_fresh bounds, rootsAt_push_old resultBound]
  exact closed

end Goose.Lower.Validation.SummaryPreservation
