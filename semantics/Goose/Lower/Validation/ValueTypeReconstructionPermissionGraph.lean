import Goose.Lower.Validation.ExpressionTypingAuthority

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem list_forIn_fold {α β : Type} (items : List α) (initial : β)
    (step : β → α → β) :
    (forIn (m := Id) items initial (fun item acc => ForInStep.yield (step acc item)) : Id β) =
      items.foldl step initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    simpa only [List.forIn_cons, bind, pure, List.foldl_cons] using ih (step initial item)

private theorem array_forIn_fold {α β : Type} (items : Array α) (initial : β)
    (step : β → α → β) :
    (forIn (m := Id) items initial (fun item acc => ForInStep.yield (step acc item)) : Id β) =
      items.toList.foldl step initial := by
  rw [← Array.forIn_toList]
  exact list_forIn_fold _ _ _

def permissionConstraintStep (caps : Array (Bool × Bool))
    (constraint : ValueId × (Bool × Bool)) : Array (Bool × Bool) :=
  caps.set! constraint.1 (meetPermissions (permissionsAt caps constraint.1) constraint.2)

def instructionPermissionConstraints (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) (caps : Array (Bool × Bool)) :
    Inst → List (ValueId × (Bool × Bool))
  | .def value op => [(value, func.permissionOfOp globalKinds structs types caps value op)]
  | .eff _ => []
  | .term term => term.permissionEdges.flatMap fun edge =>
      match func.blocks[edge.1]? with
      | none => []
      | some destination => destination.params.zip edge.2 |>.map fun (entry : (ValueId × VTy) × ValueId) =>
          (entry.1.1, permissionsAt caps entry.2)

def permissionConstraints (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) (caps : Array (Bool × Bool)) :
    List (ValueId × (Bool × Bool)) :=
  ((func.blocks[0]?).toList.flatMap fun entry =>
    entry.params.map fun param => (param.1, typedPermissions types param.1)) ++
  func.blocks.toList.flatMap fun block =>
    block.insts.flatMap (instructionPermissionConstraints globalKinds structs func types caps)

private def permissionInstructionRun (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) (caps : Array (Bool × Bool))
    (inst : Inst) (next : Array (Bool × Bool)) : Id (ForInStep (Array (Bool × Bool))) :=
  match inst with
  | .def value op => .yield (next.set! value
      (meetPermissions (permissionsAt next value)
        (func.permissionOfOp globalKinds structs types caps value op)))
  | .term term => .yield (forIn (m := Id) term.permissionEdges next fun edge next =>
      match func.blocks[edge.1]? with
      | some destination => .yield (forIn (m := Id) (destination.params.zip edge.2) next fun entry next =>
          .yield (next.set! entry.1.1
            (meetPermissions (permissionsAt next entry.1.1) (permissionsAt caps entry.2))))
      | _ => .yield next)
  | _ => .yield next

private theorem permissionInstructionRun_eq_fold (globalKinds : Array VarKind)
    (structs : Array StructDef) (func : Func) (types : Array (Option VTy))
    (caps : Array (Bool × Bool)) (inst : Inst) (next : Array (Bool × Bool)) :
    permissionInstructionRun globalKinds structs func types caps inst next =
      .yield ((instructionPermissionConstraints globalKinds structs func types caps inst).foldl
        permissionConstraintStep next) := by
  cases inst with
  | «def» value op => rfl
  | eff effect => rfl
  | term term =>
    simp only [permissionInstructionRun, instructionPermissionConstraints,
      List.foldl_flatMap]
    have body : (fun (edge : BlockId × List ValueId) (current : Array (Bool × Bool)) =>
        match func.blocks[edge.1]? with
        | some destination => ForInStep.yield (forIn (m := Id) (destination.params.zip edge.2) current
            fun entry current => ForInStep.yield (current.set! entry.1.1
              (meetPermissions (permissionsAt current entry.1.1) (permissionsAt caps entry.2))))
        | _ => ForInStep.yield current) =
        (fun edge current => ForInStep.yield
          ((match func.blocks[edge.1]? with
          | none => []
          | some destination => (destination.params.zip edge.2).map fun (entry : (ValueId × VTy) × ValueId) =>
              (entry.1.1, permissionsAt caps entry.2)).foldl permissionConstraintStep current)) := by
      funext edge current
      cases row : func.blocks[edge.1]? with
      | none => rfl
      | some destination =>
        simp only [list_forIn_fold, List.foldl_map]
        rfl
    dsimp only [Id] at body ⊢
    rw [body, list_forIn_fold]

theorem permissionRound_eq_constraints (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) (caps : Array (Bool × Bool)) :
    func.permissionRound globalKinds structs types caps =
      (permissionConstraints globalKinds structs func types caps).foldl permissionConstraintStep caps := by
  unfold Func.permissionRound permissionConstraints
  simp only [List.foldl_append, List.foldl_flatMap, List.foldl_map]
  simp only [Id.run, bind, pure]
  dsimp only [Id]
  cases row : func.blocks[0]?
  all_goals simp only [Option.toList, List.foldl_nil, List.foldl_cons,
    array_forIn_fold, list_forIn_fold]
  all_goals congr 1
  all_goals funext current block
  all_goals have body := permissionInstructionRun_eq_fold globalKinds structs func types caps
  all_goals dsimp only [permissionInstructionRun, Id] at body
  all_goals simp only [list_forIn_fold] at body
  all_goals unfold permissionInstructionRun.match_4 permissionInstructionRun.match_1 at body
  all_goals unfold Func.permissionRound.match_7 Func.permissionRound.match_3
  all_goals simp only [body, list_forIn_fold]

private theorem constraintStep_size (caps : Array (Bool × Bool))
    (constraint : ValueId × (Bool × Bool)) :
    (permissionConstraintStep caps constraint).size = caps.size := by
  simp [permissionConstraintStep]

private theorem constraintFold_size (constraints : List (ValueId × (Bool × Bool)))
    (caps : Array (Bool × Bool)) :
    (constraints.foldl permissionConstraintStep caps).size = caps.size := by
  induction constraints generalizing caps with
  | nil => rfl
  | cons constraint rest ih => rw [List.foldl_cons, ih, constraintStep_size]

private theorem constraintStep_contents (caps : Array (Bool × Bool))
    (constraint : ValueId × (Bool × Bool)) (value : ValueId)
    (present : (permissionsAt (permissionConstraintStep caps constraint) value).2 = true) :
    (permissionsAt caps value).2 = true ∧ (constraint.1 = value → constraint.2.2 = true) := by
  by_cases same : constraint.1 = value
  · subst value
    by_cases bound : constraint.1 < caps.size
    · simp only [permissionConstraintStep, permissionsAt, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_self_of_lt bound, Option.getD_some, meetPermissions] at present
      exact ⟨(Bool.and_eq_true_iff.mp present).1, fun _ => (Bool.and_eq_true_iff.mp present).2⟩
    · simp [permissionConstraintStep, permissionsAt, Array.set!_eq_setIfInBounds, bound] at present
  · simp only [permissionConstraintStep, permissionsAt, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne same] at present
    exact ⟨present, fun equality => (same equality).elim⟩

private theorem constraintFold_contents (constraints : List (ValueId × (Bool × Bool)))
    (caps : Array (Bool × Bool)) (value : ValueId)
    (present : (permissionsAt (constraints.foldl permissionConstraintStep caps) value).2 = true) :
    (permissionsAt caps value).2 = true ∧
      ∀ constraint ∈ constraints, constraint.1 = value → constraint.2.2 = true := by
  induction constraints generalizing caps with
  | nil => exact ⟨present, by simp⟩
  | cons constraint rest ih =>
    obtain ⟨next, remaining⟩ := ih _ present
    obtain ⟨previous, allowed⟩ := constraintStep_contents caps constraint value next
    refine ⟨previous, ?_⟩
    intro entry member same
    rcases List.mem_cons.mp member with equal | tail
    · subst entry
      exact allowed same
    · exact remaining entry tail same

theorem permissionRound_size (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) (caps : Array (Bool × Bool)) :
    (func.permissionRound globalKinds structs types caps).size = caps.size := by
  rw [permissionRound_eq_constraints]
  exact constraintFold_size _ _

theorem permissionsFromTables_size (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) :
    (func.permissionsFromTables globalKinds structs types).size = func.numValues := by
  apply permissionsFromTables_invariant (invariant := fun caps => caps.size = func.numValues)
  · intro caps size
    exact (permissionRound_size _ _ _ _ _).trans size
  · simp

theorem permissionsFromTables_constraints (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) :
    let caps := func.permissionsFromTables globalKinds structs types
    ∀ constraint ∈ permissionConstraints globalKinds structs func types caps,
      (permissionsAt caps constraint.1).2 = true → constraint.2.2 = true := by
  dsimp only
  intro constraint member present
  have stable := permissionsFromTables_stable globalKinds structs func types
  rw [permissionRound_eq_constraints] at stable
  have finalPresent := present
  rw [← stable] at finalPresent
  exact (constraintFold_contents _ _ _ finalPresent).2 constraint member rfl

theorem ContentsOperation.of_permission
    {globalKinds : Array VarKind} {structs : Array StructDef}
    {func : Func} {types : Array (Option VTy)} {caps : Array (Bool × Bool)}
    {value : ValueId} {op : Op}
    (allowed : (func.permissionOfOp globalKinds structs types caps value op).2 = true) :
    ContentsOperation globalKinds structs func types
      (fun owner => (permissionsAt caps owner).2 = true) value op := by
  cases op with
  | slotAddr slot =>
    cases row : func.slots[slot]? with
    | none => simp [Func.permissionOfOp, row] at allowed
    | some descriptor => exact ⟨descriptor, row⟩
  | globalAddr global =>
    cases row : globalKinds[global]? with
    | none => simp [Func.permissionOfOp, row] at allowed
    | some kind => exact ⟨kind, row⟩
  | refFreeze owner => simp [Func.permissionOfOp] at allowed
  | fieldAddr owner index =>
    simp only [Func.permissionOfOp] at allowed
    split at allowed
    · next mu id fields typed =>
      cases descriptorRow : structs[id]? with
      | none => simp [descriptorRow] at allowed
      | some descriptor =>
        cases fieldRow : descriptor.fields[index]? with
        | none => simp [descriptorRow, fieldRow] at allowed
        | some field =>
          simp only [descriptorRow, Option.bind_some, fieldRow] at allowed
          have facts := Bool.and_eq_true_iff.mp allowed
          exact ⟨facts.1, mu, id, fields, descriptor, field, typed, descriptorRow,
            fieldRow, beq_iff_eq.mp facts.2⟩
    · contradiction
  | snapshot _ owner | refElem owner _ | indexChecked owner _ _ | indexProven owner _ => exact allowed
  | _ => exact allowed

theorem contentsClosed_permissions (globalKinds : Array VarKind) (structs : Array StructDef)
    (func : Func) (types : Array (Option VTy)) :
    let caps := func.permissionsFromTables globalKinds structs types
    ContentsClosed globalKinds structs func types
      (fun value => (permissionsAt caps value).2 = true) := by
  dsimp only
  let caps := func.permissionsFromTables globalKinds structs types
  have constraints := permissionsFromTables_constraints globalKinds structs func types
  change ∀ constraint ∈ permissionConstraints globalKinds structs func types caps,
    (permissionsAt caps constraint.1).2 = true → constraint.2.2 = true at constraints
  constructor
  · intro value member
    have bounded := ContentsPresent.bound (caps := caps)
      (authorized := fun value => (permissionsAt caps value).2 = true)
      (fun _ member => member) member
    rw [permissionsFromTables_size] at bounded
    exact bounded
  · intro block row param member authorized
    apply constraints (param.1, typedPermissions types param.1) ?_ authorized
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨block, by simp [row],
      List.mem_map.mpr ⟨param, member, rfl⟩⟩
  · intro block member value op definition authorized
    apply ContentsOperation.of_permission
    apply constraints (value, func.permissionOfOp globalKinds structs types caps value op) ?_ authorized
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨block, member,
      List.mem_flatMap.mpr ⟨.def value op, definition, by simp [instructionPermissionConstraints]⟩⟩
  · intro block member term definition edge edgeMember destination destinationRow entry entryMember authorized
    apply constraints (entry.1.1, permissionsAt caps entry.2) ?_ authorized
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨block, member,
      List.mem_flatMap.mpr ⟨.term term, definition,
        List.mem_flatMap.mpr ⟨edge, edgeMember, by
          simp only [destinationRow]
          exact List.mem_map.mpr ⟨entry, entryMember, rfl⟩⟩⟩⟩

end Goose.Lower.Validation
