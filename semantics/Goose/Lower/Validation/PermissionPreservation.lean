import Goose.Lower.Validation.ExpressionTypingWritable
import Goose.GIR.Validate

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def PermissionTransfer (profile : ArtifactProfile) (writable contents : ValueId → Prop) (value : ValueId) : Ty → Prop
  | .ref .mutable (.grow _) | .ref .mutable (.growshrink _) =>
    if profile = .shrink then writable value ∧ contents value else contents value
  | .ref .mutable (.structT ..) | .ref .mutable (.arr ..) | .ref .mutable (.limited ..) =>
    writable value ∧ contents value
  | .ref .mutable _ => writable value
  | _ => True

inductive ContentsMutation : ValueId → Inst → Prop where
  | push (result owner value origin) : ContentsMutation owner (.def result (.push owner value origin))
  | append (owner value origin) : ContentsMutation owner (.eff (.append owner value origin))
  | pop (result owner origin) : ContentsMutation owner (.def result (.pop owner origin))
  | popN (owner count origin) : ContentsMutation owner (.eff (.popN owner count origin))
  | resize (owner count value origin) : ContentsMutation owner (.eff (.resize owner count value origin))
  | clear (owner origin) : ContentsMutation owner (.eff (.clear owner origin))

structure PermissionRule (module : GIR.Module) (func : Func) (types : Array (Option VTy))
    (writable contents : ValueId → Prop) (instruction : Inst) : Prop where
  storeBinding : ∀ owner value origin, instruction = .eff (.store owner value origin) → writable owner
  storeValue : ∀ owner value origin mu ty, instruction = .eff (.store owner value origin) →
    types[owner]? = some (some (.data (.ref mu ty))) → PermissionTransfer module.profile writable contents value ty
  mutation : ∀ owner, ContentsMutation owner instruction → contents owner
  ownerBorrow : ∀ result owner, instruction = .def result (.ownerBorrow owner) → contents owner
  replacement : ∀ owner value origin, instruction = .eff (.replace owner value origin) →
    writable owner ∧ contents owner
  snapshot : ∀ value mode owner ty, instruction = .def value (.snapshot mode owner) →
    types[value]? = some (some (.view .mutable ty)) → contents value
  call : ∀ value callee args origin descriptor, instruction = .def value (.call callee args origin) →
    module.funcs[callee]? = some descriptor → ∀ entry ∈ descriptor.params.zip args,
      PermissionTransfer module.profile writable contents entry.2 entry.1
  binding : ∀ slot value origin descriptor, instruction = .eff (.slotInit slot value origin) →
    func.slots[slot]? = some descriptor → PermissionTransfer module.profile writable contents value descriptor.ty
  result : ∀ values origin, instruction = .term (.ret values origin) →
    ∀ entry ∈ func.results.zip values, PermissionTransfer module.profile writable contents entry.2 entry.1

theorem PermissionTransfer.check {profile : ArtifactProfile} {writable contents : ValueId → Prop} {value : ValueId} {ty : Ty}
    {caps : Array (Bool × Bool)} (allowed : PermissionTransfer profile writable contents value ty)
    (bindings : WritablePresent caps writable) (elements : ContentsPresent caps contents) :
    (match (generalizing := false) ty with
      | .ref .mutable referent =>
        let cap := permissionsAt caps value
        match (generalizing := false) referent with
        | .grow _ | .growshrink _ => if profile == .shrink then cap.1 && cap.2 else cap.2
        | .structT .. | .arr .. | .limited .. => cap.1 && cap.2
        | _ => cap.1
      | _ => true) = true := by
  cases ty with
  | ref mu referent =>
    cases mu with
    | readOnly => rfl
    | mutable =>
      cases profile <;> cases referent <;> simp only [PermissionTransfer, reduceCtorEq, ↓reduceIte] at allowed <;>
        first | exact elements value allowed
              | exact Bool.and_eq_true_iff.mpr ⟨bindings value allowed.1, elements value allowed.2⟩
              | exact bindings value allowed
  | _ => rfl

private theorem forIn_unit_ok {items : List α} {body : α → PUnit → Check (ForInStep PUnit)}
    (checked : ∀ item ∈ items, body item PUnit.unit = .ok (.yield PUnit.unit)) :
    forIn items PUnit.unit body = .ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn_cons, checked item (by simp)]
    exact ih (fun next member => checked next (by simp [member]))

private theorem forIn_result_ok {items : List α} {body : α → PUnit → Check (ForInStep PUnit)}
    (result : β) (checked : ∀ item ∈ items, body item PUnit.unit = .ok (.yield PUnit.unit)) :
    (forIn items PUnit.unit body >>= fun _ => pure result : Check β) = .ok result := by
  rw [forIn_unit_ok checked]
  rfl

theorem checkPermissions_of_rules {module : GIR.Module} {func : Func} {types : Array (Option VTy)}
    {writable contents : ValueId → Prop}
    (rules : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
      PermissionRule module func types writable contents instruction)
    (bindings : WritablePresent (func.permissions module types) writable)
    (elements : ContentsPresent (func.permissions module types) contents) (label : String) :
    checkPermissions module label func types = .ok () := by
  unfold checkPermissions
  dsimp only
  rw [← Array.forIn_toList]
  apply forIn_result_ok
  intro block blockMember
  apply forIn_result_ok
  intro instruction instMember
  have rule := rules block blockMember instruction instMember
  cases instruction with
  | «def» value op =>
    cases op <;> simp only <;> try rfl
    case ownerBorrow owner =>
      have allowed := elements owner (rule.ownerBorrow value owner rfl)
      simp only [permissionsAt] at allowed
      simp only [allowed, ite_true]
      rfl
    case snapshot mode owner =>
      split <;> try rfl
      rename_i ty typed
      have allowed := elements value (rule.snapshot value mode owner ty rfl typed)
      simp only [permissionsAt] at allowed
      simp only [allowed, ite_true]
      rfl
    case push owner stored origin =>
      have allowed := elements owner (rule.mutation owner (.push value owner stored origin))
      simp only [permissionsAt] at allowed
      simp only [allowed, ite_true]
      rfl
    case pop owner origin =>
      have allowed := elements owner (rule.mutation owner (.pop value owner origin))
      simp only [permissionsAt] at allowed
      simp only [allowed, ite_true]
      rfl
    case call callee args origin =>
      cases row : module.funcs[callee]? with
      | none => rfl
      | some descriptor =>
        apply forIn_result_ok
        intro entry member
        have allowed := (rule.call value callee args origin descriptor rfl row entry member).check bindings elements
        simp only [permissionsAt] at allowed
        cases shape : entry.1 <;> simp_all [pure, Except.pure]
        case ref mu referent =>
          cases profile : module.profile <;> cases mu <;> cases referent <;> simp_all
  | eff effect =>
    cases effect <;> simp only <;> try rfl
    case slotInit slot value origin =>
      cases row : func.slots[slot]? with
      | none => rfl
      | some descriptor =>
        have allowed := (rule.binding slot value origin descriptor rfl row).check bindings elements
        simp only [permissionsAt] at allowed
        cases shape : descriptor.ty <;> simp_all [pure, Except.pure]
        case ref mu referent =>
          cases profile : module.profile <;> cases mu <;> cases referent <;> simp_all
    case store owner value origin =>
      have binding := bindings owner (rule.storeBinding owner value origin rfl)
      simp only [permissionsAt] at binding
      simp only [binding, ite_true]
      split <;> try rfl
      rename_i mu ty typed
      have allowed := (rule.storeValue owner value origin mu ty rfl typed).check bindings elements
      simp only [permissionsAt] at allowed
      cases ty <;> simp_all [pure, Except.pure, bind, Except.bind]
      case ref mu referent =>
        cases profile : module.profile <;> cases mu <;> cases referent <;> simp_all
    case append owner value origin =>
      have allowed := elements owner (rule.mutation owner (.append owner value origin))
      simp only [permissionsAt] at allowed
      simp only [allowed, ite_true]
      rfl
    case popN owner count origin =>
      have allowed := elements owner (rule.mutation owner (.popN owner count origin))
      simp only [permissionsAt] at allowed
      simp only [allowed, ite_true]
      rfl
    case resize owner count value origin =>
      have allowed := elements owner (rule.mutation owner (.resize owner count value origin))
      simp only [permissionsAt] at allowed
      simp only [allowed, ite_true]
      rfl
    case clear owner origin =>
      have allowed := elements owner (rule.mutation owner (.clear owner origin))
      simp only [permissionsAt] at allowed
      simp only [allowed, ite_true]
      rfl
    case replace owner value origin =>
      have both := rule.replacement owner value origin rfl
      have allowed := Bool.and_eq_true_iff.mpr ⟨bindings owner both.1, elements owner both.2⟩
      simp only [permissionsAt] at allowed
      simp only [allowed, ite_true]
      rfl
  | term term =>
    cases term <;> simp only <;> try rfl
    case ret values origin =>
      apply forIn_result_ok
      intro entry member
      have allowed := (rule.result values origin rfl entry member).check bindings elements
      simp only [permissionsAt] at allowed
      cases shape : entry.1 <;> simp_all [pure, Except.pure]
      case ref mu referent =>
        cases profile : module.profile <;> cases mu <;> cases referent <;> simp_all

structure PermissionAuthority (module : GIR.Module) (func : Func) (types : Array (Option VTy))
    (writable contents : ValueId → Prop) : Prop where
  contentGraph : ContentsClosed (module.globals.map (·.kind)) module.structs func types contents
  bindingGraph : WritableClosed (module.globals.map (·.kind)) module.structs func types writable contents
  instructions : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
    PermissionRule module func types writable contents instruction

theorem PermissionAuthority.check {module : GIR.Module} {func : Func} {types : Array (Option VTy)}
    {writable contents : ValueId → Prop}
    (authority : PermissionAuthority module func types writable contents) (label : String) :
    checkPermissions module label func types = .ok () :=
  checkPermissions_of_rules authority.instructions
    (authority.bindingGraph.permissions authority.contentGraph) authority.contentGraph.permissions label

private theorem checkAll_of_forall {items : List α} {action : α → Check Unit}
    (checked : ∀ item ∈ items, action item = .ok ()) : checkAll items action = .ok () := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    unfold checkAll
    rw [checked item (by simp)]
    exact ih (fun next member => checked next (by simp [member]))

theorem checkPermissionStage_of_authority {module : GIR.Module}
    (authority : ∀ info ∈ module.infos, ∃ writable contents,
      PermissionAuthority module info.f info.vt writable contents) :
    (checkAll module.infos fun info => checkPermissions module info.label info.f info.vt) = .ok () := by
  apply checkAll_of_forall
  intro info member
  obtain ⟨writable, contents, checked⟩ := authority info member
  exact checked.check info.label

#print axioms checkPermissions_of_rules
#print axioms PermissionAuthority.check
#print axioms checkPermissionStage_of_authority

end Goose.Lower.Validation
