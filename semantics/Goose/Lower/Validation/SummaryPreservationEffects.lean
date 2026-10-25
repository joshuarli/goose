import Goose.Core.DeclarativeRoots
import Goose.Lower.Validation.SummaryPreservationParameters

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem rootsTargets_param_iff {roots : List RootRef} {index : Nat} :
    Target.param index ∈ rootsTargets roots ↔ RootRef.param index ∈ roots := by
  constructor
  · intro member
    obtain ⟨root, member, mapped⟩ := List.mem_filterMap.mp member
    cases root with
    | param source => simp only [rootTarget, Option.some.injEq, Target.param.injEq] at mapped
                      simpa [mapped] using member
    | _ => simp [rootTarget] at mapped
  · exact mem_rootsTargets_param

def ParameterRootsClosed (func : Func) : Prop :=
  ∀ index root, root ∈ func.parameterRoots index → root = .param index ∨ ∃ global, root = .global global

theorem storageTargets_mono {func : Func} {found declared : List Target}
    (subset : ∀ target ∈ found, target ∈ declared) :
    ∀ target ∈ func.storageTargets found, target ∈ func.storageTargets declared := by
  intro target member
  obtain ⟨source, sourceMember, targetMember⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨source, subset source sourceMember, targetMember⟩

theorem storageTargets_member_closed {func : Func} {declared : List Target} {source : Target}
    (closed : ParameterRootsClosed func) (member : source ∈ func.storageTargets declared) :
    ∀ target ∈ func.storageTargets [source], target ∈ func.storageTargets declared := by
  intro target targetMember
  cases source with
  | global global =>
    simp only [Func.storageTargets, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.mem_singleton] at targetMember
    simpa [targetMember] using member
  | param index =>
    obtain ⟨declaredTarget, declaredMember, sourceMember⟩ := List.mem_flatMap.mp member
    cases declaredTarget with
    | global global => simp at sourceMember
    | param declaredIndex =>
      have rootMember := rootsTargets_param_iff.mp sourceMember
      have same : index = declaredIndex := by
        rcases closed declaredIndex (.param index) rootMember with same | ⟨global, impossible⟩
        · exact RootRef.param.inj same
        · cases impossible
      subst index
      apply List.mem_flatMap.mpr
      refine ⟨.param declaredIndex, declaredMember, ?_⟩
      simpa only [Func.storageTargets, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        using targetMember

theorem storageTargets_idempotent {func : Func} {targets : List Target}
    (closed : ParameterRootsClosed func) :
    ∀ target ∈ func.storageTargets (func.storageTargets targets),
      target ∈ func.storageTargets targets := by
  intro target member
  obtain ⟨source, sourceMember, targetMember⟩ := List.mem_flatMap.mp member
  apply storageTargets_member_closed closed sourceMember target
  simpa only [Func.storageTargets, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    using targetMember

theorem lowerContextAt_parameterRoots_closed {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} (accepted : validate module = .ok ())
    (contextLookup : module.contexts[context]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl) :
    ParameterRootsClosed (lowerContextAt module ctx impl) := by
  obtain ⟨checkedImpl, lookup, checked⟩ := (validate_modOk module accepted).ctx context ctx contextLookup
  rw [implLookup] at lookup
  cases lookup
  intro index root member
  unfold Func.parameterRoots at member
  cases row : (lowerContextRootInfo ctx impl).params.find? (·.1 == index) with
  | none =>
    change root ∈ (match (lowerContextRootInfo ctx impl).params.find? (·.1 == index) with
      | some (_, roots) => roots
      | none => [.param index]) at member
    exact Or.inl (by simpa [row] using member)
  | some entry =>
    have rowMember := Array.mem_of_find?_eq_some row
    simp only [lowerContextRootInfo, ← Array.mem_toList_iff, List.toList_toArray,
      List.mem_filterMap] at rowMember
    obtain ⟨⟨param, position⟩, parameterMember, annotation⟩ := rowMember
    have parameterLookup : impl.params[position]? = some param := by
      simpa using List.mk_mem_zipIdx_iff_getElem?.mp parameterMember
    have paramOk := (validate_modOk module accepted).impl ctx.impl impl implLookup
    have identity := (paramOk.params position param parameterLookup).1
    have key : entry.1 = index := eq_of_beq (Array.find?_some (p := fun entry : Nat × List RootRef => entry.1 == index) (a := entry) row)
    cases annotationRow : ctx.varRoots.find? (·.1 == param.var) with
    | none => simp [annotationRow] at annotation
    | some rootsRow =>
      simp only [annotationRow, Option.map_some, Option.some.injEq] at annotation
      cases annotation
      simp only at key
      have rootMember : root ∈ rootsRow.2 := by
        change root ∈ (match (lowerContextRootInfo ctx impl).params.find? (·.1 == index) with
          | some (_, roots) => roots
          | none => [.param index]) at member
        simpa [row] using member
      have rootClosed := checked.paramAnn position rootsRow.2
        (Array.getElem?_eq_some_iff.mp parameterLookup).1
        (by simpa [identity] using congrArg (Option.map Prod.snd) annotationRow) root rootMember
      simpa only [key] using rootClosed

theorem lowerContextAt_storageTargets_eq {module : Core.Module} {context : ContextId}
    {ctx : Context} {impl : Impl} {targets : List Target}
    (accepted : validate module = .ok ())
    (contextLookup : module.contexts[context]? = some ctx)
    (implLookup : module.impls[ctx.impl]? = some impl)
    (bounds : ∀ target ∈ targets, Target.Within module impl target) :
    (lowerContextAt module ctx impl).storageTargets targets = expandTargets impl ctx targets := by
  obtain ⟨checkedImpl, lookup, checked⟩ := (validate_modOk module accepted).ctx context ctx contextLookup
  rw [implLookup] at lookup
  cases lookup
  have implOk := (validate_modOk module accepted).impl ctx.impl impl implLookup
  unfold Func.storageTargets expandTargets
  apply congrArg List.flatten
  apply List.map_congr_left
  intro target member
  cases target with
  | global global => rfl
  | param index =>
    have bound := bounds (.param index) member
    let param := impl.params[index]'bound
    have parameter : impl.params[index]? = some param := Array.getElem?_eq_getElem bound
    obtain ⟨identity, localVar, variableRow, scope, parameterType⟩ := implOk.params index param parameter
    have rowLookup := lowerContextRootInfo_parameter_lookup (ctx := ctx) parameter
    rw [identity] at rowLookup
    cases annotation : ctx.varRoots.find? (·.1 == index) with
    | none =>
      have missing : (lowerContextAt module ctx impl).roots.params.find? (·.1 == index) = none := by
        change (lowerContextRootInfo ctx impl).params.find? (·.1 == index) = none
        simpa [annotation] using rowLookup
      simp [variableRow, annotation, Func.parameterRoots, missing, rootsTargets, rootTarget]
    | some entry =>
      have entryVar : entry.1 = index :=
        eq_of_beq (List.find?_some (p := fun entry : VarId × List RootRef => entry.1 == index)
          (a := entry) annotation)
      obtain ⟨declaredVar, declaredLookup, refLike, _⟩ :=
        Core.Declarative.annotationRows_sound module impl ctx checked.annotationShape entry.1 entry.2
          (List.mem_of_find?_eq_some annotation)
      rw [entryVar, variableRow] at declaredLookup
      cases declaredLookup
      have parameterRoots := lowerContextAt_parameterRoots_eq (module := module) (ctx := ctx) (roots := entry.2) parameter
        (by simpa [identity, annotation])
      simp [variableRow, annotation, refLike, parameterRoots]

end Goose.Lower.Validation.SummaryPreservation
