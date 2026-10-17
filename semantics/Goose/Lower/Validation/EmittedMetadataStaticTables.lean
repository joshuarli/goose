import Goose.Lower.Validation.EmittedMetadataStaticSourceChecks

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem static_forIn_members {α β : Type} {items : List α} {body : α → β → Core.V (ForInStep β)}
    {property : α → Prop}
    (yielded : ∀ item state step, body item state = .ok step → ∃ next, step = .yield next)
    (checkedItem : ∀ item state step, body item state = .ok step → property item)
    {initial final : β} (checked : forIn items initial body = .ok final) :
    ∀ item ∈ items, property item := by
  induction items generalizing initial final with
  | nil => simp
  | cons item rest ih =>
    rw [List.forIn_cons] at checked
    obtain ⟨step, first, remaining⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
    obtain ⟨next, rfl⟩ := yielded item initial step first
    intro selected member
    rcases List.mem_cons.mp member with rfl | member
    · exact checkedItem selected initial _ first
    · exact ih remaining selected member

set_option maxHeartbeats 800000 in
theorem static_checkStructTables_fields {module : Core.Module}
    (checked : Core.checkStructTables module = .ok ()) :
    ∀ descriptor ∈ module.structs.toList, ∀ field ∈ descriptor.fields.toList,
      Core.checkResolvedType module field.ty = .ok () := by
  unfold Core.checkStructTables at checked
  by_cases forbidden : (module.profile == .pilot && !module.structs.isEmpty) = true
  · simp [forbidden, chk] at checked
  · simp only [forbidden] at checked
    obtain ⟨_, structChecks, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp checked
    rw [← Array.forIn_toList] at structChecks
    refine static_forIn_members (property := fun descriptor => ∀ field ∈ descriptor.fields.toList,
      Core.checkResolvedType module field.ty = .ok ()) ?_ ?_ structChecks
    · intro descriptor state step one
      by_cases zero : (descriptor.byteSize == 0) = true
      · simp [zero, Core.reject, bind, Except.bind] at one
      · simp only [zero] at one
        obtain ⟨_, _, tail⟩ := (Core.Sound.ex_bind_ok _ _ _).mp one
        have same : step = .yield PUnit.unit := by simpa [pure, Except.pure] using tail.symm
        exact ⟨_, same⟩
    · intro descriptor state step one
      by_cases zero : (descriptor.byteSize == 0) = true
      · simp [zero, Core.reject, bind, Except.bind] at one
      · simp only [zero] at one
        obtain ⟨_, fields, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp one
        rw [← Array.forIn_toList] at fields
        refine static_forIn_members (property := fun field => Core.checkResolvedType module field.ty = .ok ())
          ?_ ?_ fields
        · intro field offset next fieldCheck
          try simp only [Core.Sound.ex_bind_ok] at fieldCheck
          repeat' first
            | (rcases fieldCheck with ⟨_, _, fieldCheck⟩)
            | (split at fieldCheck <;> try try simp only [Core.Sound.ex_bind_ok] at fieldCheck)
          all_goals try simp_all only [Core.reject, bind, Except.bind, pure, Except.pure, reduceCtorEq]
          all_goals exact ⟨_, rfl⟩
        · intro field offset next fieldCheck
          obtain ⟨unit, resolved, _⟩ := (Core.Sound.ex_bind_ok _ _ _).mp fieldCheck
          cases unit
          exact resolved

theorem static_lowerEnv_tables {module : Core.Module} {vars : Array LocalVar}
    (checked : Core.checkStructTables module = .ok ())
    (variables : ∀ localVar ∈ vars.toList, Core.checkResolvedType module localVar.ty = .ok ())
    (results : List Ty) : EmittedStaticTables module (lowerEnv module vars results) := by
  constructor
  · intro index descriptor row
    change (vars.mapIdx fun index localVar =>
      (⟨localVar.ty, localVar.kind, localVar.scope, index⟩ : Slot))[index]? = some descriptor at row
    rw [Array.getElem?_mapIdx] at row
    cases variableAt : vars[index]? with
    | none => simp [variableAt] at row
    | some localVar =>
      simp only [variableAt, Option.map_some, Option.some.injEq] at row
      subst descriptor
      exact variables localVar (Array.mem_toList_iff.mpr (Array.mem_of_getElem? variableAt))
  · intro index type kind row
    change (module.globals.map fun global => (global.ty, global.kind))[index]? = some (type, kind) at row
    rw [Array.getElem?_map] at row
    cases globalAt : module.globals[index]? with
    | none => simp [globalAt] at row
    | some global =>
      simp only [globalAt, Option.map_some, Option.some.injEq, Prod.mk.injEq] at row
      rw [← row.1]
      exact checkStructTables_global_resolved checked
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? globalAt))
  · intro index params results row type member
    change (module.contexts.map fun context => match module.impls[context.impl]? with
      | some impl => (impl.params.toList.map (tyOfVar impl ·.var), impl.results.toList)
      | none => ([], []))[index]? = some (params, results) at row
    rw [Array.getElem?_map] at row
    cases contextAt : module.contexts[index]? with
    | none => simp [contextAt] at row
    | some context =>
      simp only [contextAt, Option.map_some, Option.some.injEq] at row
      cases implAt : module.impls[context.impl]? with
      | none =>
        simp only [implAt, Prod.mk.injEq] at row
        rw [← row.2] at member
        cases member
      | some impl =>
        simp only [implAt, Prod.mk.injEq] at row
        rw [← row.2] at member
        exact (checkStructTables_impl_resolved checked
          (Array.mem_toList_iff.mpr (Array.mem_of_getElem? implAt))).2 type member
  · intro index descriptor row fieldIndex field fieldAt
    exact static_checkStructTables_fields checked descriptor
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? row)) field
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? fieldAt))

theorem static_resolvedTypes_ofList {module : Core.Module} (types : List Ty)
    (resolved : ∀ type ∈ types, Core.checkResolvedType module type = .ok ()) :
    Core.checkResolvedTypes module (TyList.ofList types) = .ok () := by
  induction types with
  | nil => rfl
  | cons type rest ih =>
    simp only [TyList.ofList, Core.checkResolvedTypes, resolved type (by simp),
      bind, Except.bind]
    exact ih (fun item member => resolved item (by simp [member]))

theorem static_structDef_resolved {env : Core.TEnv} {type : Ty} {descriptor : StructDef}
    {start finish : Nat} (tables : Core.checkStructTables env.mod = .ok ())
    (typed : Core.structDef env type start = .ok (descriptor, finish)) :
    Core.checkResolvedType env.mod type = .ok () := by
  have profile := static_structDef_profile typed
  obtain ⟨id, fields, shape, _, nominal, lookup, _⟩ := Core.Sound.structDef_ok _ _ _ _ _ typed
  have payload : fields = TyList.ofList (descriptor.fields.toList.map (·.ty)) := by
    simpa only [Core.Module.structType?, lookup, Option.map_some, shape,
      Option.some.injEq, Ty.structT.injEq, true_and] using nominal.symm
  have fieldTypes : Core.checkResolvedTypes env.mod fields = .ok () := by
    rw [payload]
    apply static_resolvedTypes_ofList
    intro fieldType member
    obtain ⟨field, fieldAt, rfl⟩ := List.mem_map.mp member
    exact static_checkStructTables_fields tables descriptor
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup)) field fieldAt
  simp [shape, Core.checkResolvedType, profile, nominal, fieldTypes]

theorem static_tyExpr_structLit_resolved {env : Core.TEnv} {annotation type : Ty}
    {exprs : List Expr} {start finish : Nat} (tables : Core.checkStructTables env.mod = .ok ())
    (typed : Core.tyExpr env (.structLit annotation exprs) start = .ok (type, finish)) :
    Core.checkResolvedType env.mod annotation = .ok () := by
  simp only [Core.tyExpr] at typed
  obtain ⟨_, _, definition, _⟩ := (Core.Sound.st_bind_ok _ _ _ _).mp typed
  exact static_structDef_resolved tables definition

end Goose.Lower.Validation
