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


theorem edge_roots_closed_after_push {func : Func} {before : Prov}
    {newRoots : List RootRef} {target : BlockId} {args : List ValueId}
    (closed : EdgeRootsClosed func before target args)
    (arguments : ∀ value ∈ args, value < before.vals.size)
    (parameters : ∀ block, func.blocks[target]? = some block →
      ∀ pair ∈ block.params, pair.1 < before.vals.size) :
    EdgeRootsClosed func { before with vals := before.vals.push newRoots } target args := by
  intro block lookup pair member root rootMember
  have parameterMember := List.of_mem_zip member
  have argumentMember := List.of_mem_zip member
  rw [rootsAt_push_old (arguments pair.2 argumentMember.2)] at rootMember
  rw [rootsAt_push_old (parameters block lookup pair.1 parameterMember.1)]
  exact closed block lookup pair member root rootMember

theorem instruction_roots_closed_after_push {res : Array (List RootRef)}
    {vt : Array (Option VTy)} {func : Func} {before : Prov} {newRoots : List RootRef}
    {inst : Inst}
    (closed : InstructionRootsClosed res vt func before inst)
    (uses : ∀ value ∈ inst.uses, value < before.vals.size)
    (definitions : ∀ result op, inst = .def result op → result < before.vals.size)
    (parameters : ∀ block ∈ func.blocks.toList,
      ∀ pair ∈ block.params, pair.1 < before.vals.size) :
    InstructionRootsClosed res vt func { before with vals := before.vals.push newRoots } inst := by
  have edge : ∀ target args, (∀ value ∈ args, value < before.vals.size) →
      EdgeRootsClosed func before target args →
      EdgeRootsClosed func { before with vals := before.vals.push newRoots } target args := by
    intro target args arguments prior
    apply edge_roots_closed_after_push prior arguments
    intro block lookup
    exact parameters block (by simpa using Array.mem_of_getElem? lookup)
  cases inst with
  | «def» result op =>
    exact old_def_roots_closed_after_push closed (definitions result op rfl) uses
  | eff effect =>
    cases effect with
    | slotInit slot value origin =>
      change ∀ root ∈ rootsAt (before.vals.push newRoots) value, _
      rw [rootsAt_push_old (uses value (by simp [Inst.uses, Effect.uses]))]
      exact closed
    | store address value origin =>
      change ∀ slot, RootRef.local slot ∈ rootsAt (before.vals.push newRoots) address →
        ∀ root ∈ rootsAt (before.vals.push newRoots) value, _
      rw [rootsAt_push_old (uses address (by simp [Inst.uses, Effect.uses])),
        rootsAt_push_old (uses value (by simp [Inst.uses, Effect.uses]))]
      exact closed
    | _ => trivial
  | term term =>
    cases term with
    | br target args => exact edge target args uses closed
    | condbr condition left leftArgs right rightArgs =>
      exact ⟨edge left leftArgs (fun value member => uses value (by
        simp [Inst.uses, Term.uses, member])) closed.1,
        edge right rightArgs (fun value member => uses value (by
          simp [Inst.uses, Term.uses, member])) closed.2⟩
    | _ => trivial

end Goose.Lower.Validation.SummaryPreservation
