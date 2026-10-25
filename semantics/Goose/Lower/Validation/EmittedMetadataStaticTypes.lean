import Goose.Lower.Validation.EmittedMetadataStaticActions

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

structure EmittedTyEnvResolved (module : Core.Module) (env : TyEnv) : Prop where
  values : ∀ value type, env.valTy value = .ok type → EmittedVTyResolved module type
  slots : ∀ (index : Nat) (descriptor : Slot), env.slots[index]? = some descriptor →
    Core.checkResolvedType module descriptor.ty = .ok ()
  globals : ∀ (index : Nat) (type : Ty) (kind : VarKind), env.globals[index]? = some (type, kind) →
    Core.checkResolvedType module type = .ok ()
  signatures : ∀ (index : Nat) (params results : List Ty), env.sigs[index]? = some (params, results) →
    ∀ type ∈ results, Core.checkResolvedType module type = .ok ()
  fields : ∀ (index : Nat) (descriptor : StructDef), env.structs[index]? = some descriptor →
    ∀ (fieldIndex : Nat) (field : StructField), descriptor.fields[fieldIndex]? = some field →
      Core.checkResolvedType module field.ty = .ok ()

theorem EmittedTyEnvResolved.dataTy {module : Core.Module} {env : TyEnv}
    (resolved : EmittedTyEnvResolved module env) {value : ValueId} {type : Ty}
    (typed : env.dataTy value = .ok type) : Core.checkResolvedType module type = .ok () := by
  unfold TyEnv.dataTy at typed
  cases row : env.valTy value with
  | error error => simp [row, bind, Except.bind] at typed
  | ok vtype =>
    cases vtype with
    | data source =>
      have same : source = type := by simpa [row, bind, Except.bind, pure, Except.pure] using typed
      subst type
      exact resolved.values value (.data source) row
    | view _ _ => simp [row, bind, Except.bind, tyErr] at typed

theorem EmittedTyEnvResolved.refTy {module : Core.Module} {env : TyEnv}
    (resolved : EmittedTyEnvResolved module env) {value : ValueId} {mu : Mutability} {type : Ty}
    (typed : env.refTy value = .ok (mu, type)) : Core.checkResolvedType module type = .ok () := by
  unfold TyEnv.refTy at typed
  cases row : env.dataTy value with
  | error error => simp [row, bind, Except.bind] at typed
  | ok source =>
    cases source <;> simp [row, bind, Except.bind, tyErr, pure, Except.pure] at typed
    obtain ⟨rfl, rfl⟩ := typed
    simpa only [Core.checkResolvedType] using resolved.dataTy row

theorem EmittedTyEnvResolved.viewTy {module : Core.Module} {env : TyEnv}
    (resolved : EmittedTyEnvResolved module env) {value : ValueId} {mu : Mutability} {type : Ty}
    (typed : env.viewTy value = .ok (mu, type)) : Core.checkResolvedType module type = .ok () := by
  unfold TyEnv.viewTy at typed
  cases row : env.valTy value with
  | error error => simp [row, bind, Except.bind] at typed
  | ok source =>
    cases source with
    | data _ => simp [row, bind, Except.bind, tyErr] at typed
    | view m element =>
      obtain ⟨rfl, rfl⟩ : m = mu ∧ element = type := by
        simpa [row, bind, Except.bind, pure, Except.pure] using typed
      exact resolved.values value _ row

theorem resolved_ownerElem {module : Core.Module} {type element : Ty}
    (resolved : Core.checkResolvedType module type = .ok ())
    (selected : type.ownerElem? = some element) : Core.checkResolvedType module element = .ok () := by
  cases type <;> simp [Ty.ownerElem?] at selected
  all_goals subst element
  all_goals simp only [Core.checkResolvedType] at resolved
  all_goals first
    | exact resolved
    | (split at resolved <;> simp_all [bind, Except.bind, Core.reject, pure, Except.pure])

theorem resolved_arrayElem {module : Core.Module} {type element : Ty}
    (resolved : Core.checkResolvedType module type = .ok ())
    (selected : GIR.arrayElem? type = some element) : Core.checkResolvedType module element = .ok () := by
  cases type <;> simp [GIR.arrayElem?] at selected
  all_goals subst element
  all_goals simp only [Core.checkResolvedType] at resolved
  all_goals first
    | exact resolved
    | (split at resolved <;> simp_all [bind, Except.bind, Core.reject, pure, Except.pure])

theorem op_resultTy_resolved {module : Core.Module} {env : TyEnv}
    (resolved : EmittedTyEnvResolved module env) (op : Op) {type : VTy}
    (annotation : ∀ value, EmittedAnnotationResolved module (.def value op))
    (typed : op.resultTy env = .ok type) : EmittedVTyResolved module type := by
  cases op with
  | constInt integer number =>
    simp only [Op.resultTy] at typed
    split at typed
    · cases typed
      rfl
    · cases typed
  | constBool value => cases typed; rfl
  | constUnit => cases typed; rfl
  | bin operator integer left right origin
  | cmp operator integer left right
  | boolCmp operator left right
  | boolNot value
  | next integer value
  | viewLen value =>
    simp only [Op.resultTy] at typed
    try simp only [Core.Sound.ex_bind_ok] at typed
    repeat' first
      | (rcases typed with ⟨_, _, typed⟩)
      | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
    all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
    all_goals rfl
  | un operator integer value origin | conv conversion source destination value origin =>
    simp only [Op.resultTy] at typed
    try simp only [Core.Sound.ex_bind_ok] at typed
    repeat' first
      | (rcases typed with ⟨_, _, typed⟩)
      | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
    all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
    all_goals rfl
  | slotAddr slot =>
    simp only [Op.resultTy] at typed
    cases row : env.slots[slot]? with
    | none => simp [row, tyErr] at typed
    | some descriptor =>
      simp only [row] at typed
      cases typed
      exact resolved.slots slot descriptor row
  | globalAddr global =>
    simp only [Op.resultTy] at typed
    cases row : env.globals[global]? with
    | none => simp [row, tyErr] at typed
    | some descriptor =>
      obtain ⟨source, kind⟩ := descriptor
      simp only [row] at typed
      cases typed
      exact resolved.globals global source kind row
  | refElem value index | indexChecked value index origin | indexProven value index =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, element⟩, view, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    obtain ⟨_, _, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    cases typed
    all_goals simpa only [EmittedVTyResolved, Core.checkResolvedType, Prod.fst, Prod.snd] using resolved.viewTy view
  | refFreeze value | load value =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, element⟩, reference, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    cases typed
    simpa only [EmittedVTyResolved, Core.checkResolvedType, Prod.fst, Prod.snd] using resolved.refTy reference
  | ownerBorrow value =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, source⟩, reference, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    dsimp only at typed
    split at typed
    · cases source <;> simp only [tyErr] at typed
      all_goals cases typed
      all_goals simpa only [EmittedVTyResolved, Core.checkResolvedType, Prod.fst, Prod.snd] using resolved.refTy reference
    · simp [tyErr, bind, Except.bind] at typed
  | snapshot mode value =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, source⟩, reference, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    cases selected : GIR.arrayElem? source with
    | none => simp [selected, tyErr] at typed
    | some element =>
      simp only [selected] at typed
      cases typed
      exact resolved_arrayElem (resolved.refTy reference) selected
  | sliceView value =>
    simp only [Op.resultTy] at typed
    obtain ⟨source, data, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    cases source <;> try (cases typed)
    simpa only [EmittedVTyResolved, Core.checkResolvedType] using resolved.dataTy data
  | viewSlice mu value low high origin =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨oldMu, element⟩, view, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    try simp only [Core.Sound.ex_bind_ok] at typed
    repeat' first
      | (rcases typed with ⟨_, _, typed⟩)
      | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
    all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
    all_goals simpa only [EmittedVTyResolved, Core.checkResolvedType, Prod.fst, Prod.snd] using resolved.viewTy view
  | arrayLen value =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, source⟩, _, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    split at typed <;> cases typed
    rfl
  | push owner value origin =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, source⟩, reference, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    cases selected : source.ownerElem? with
    | none => simp [selected, tyErr] at typed
    | some element =>
      simp only [selected] at typed
      try simp only [Core.Sound.ex_bind_ok] at typed
      repeat' first
        | (rcases typed with ⟨_, _, typed⟩)
        | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
      all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
      all_goals simpa only [EmittedVTyResolved, Core.checkResolvedType] using resolved_ownerElem (resolved.refTy reference) selected
  | pop owner origin =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, source⟩, reference, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    cases selected : source.ownerElem? with
    | none => simp [selected, tyErr] at typed
    | some element =>
      simp only [selected] at typed
      cases typed
      all_goals simpa only [EmittedVTyResolved, Core.checkResolvedType] using resolved_ownerElem (resolved.refTy reference) selected
  | call function args origin =>
    simp only [Op.resultTy] at typed
    cases signature : env.sigs[function]? with
    | none => simp [signature, tyErr] at typed
    | some pair =>
      obtain ⟨params, results⟩ := pair
      simp only [signature] at typed
      try simp only [Core.Sound.ex_bind_ok] at typed
      repeat' first
        | (rcases typed with ⟨_, _, typed⟩)
        | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
      all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
      all_goals first
        | rfl
        | exact resolved.signatures function _ _ signature _ (by simp)
  | arrLit source values =>
    have valid := annotation 0
    change Core.checkResolvedType module source = .ok () at valid
    simp only [Op.resultTy] at typed
    cases source <;> try (cases typed)
    all_goals try simp only [Core.Sound.ex_bind_ok] at typed
    repeat' first
      | (rcases typed with ⟨_, _, typed⟩)
      | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
    all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
    all_goals exact valid
  | arrFill source value =>
    have valid := annotation 0
    change Core.checkResolvedType module source = .ok () at valid
    simp only [Op.resultTy] at typed
    cases source <;> try (cases typed)
    try simp only [Core.Sound.ex_bind_ok] at typed
    repeat' first
      | (rcases typed with ⟨_, _, typed⟩)
      | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
    all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
    all_goals exact valid
  | structLit source values =>
    have valid := annotation 0
    change Core.checkResolvedType module source = .ok () at valid
    simp only [Op.resultTy] at typed
    try simp only [Core.Sound.ex_bind_ok] at typed
    repeat' first
      | (rcases typed with ⟨_, _, typed⟩)
      | (split at typed <;> try simp only [Core.Sound.ex_bind_ok] at typed)
    all_goals try simp_all only [tyErr, bind, Except.bind, pure, Except.pure, reduceCtorEq]
    all_goals exact valid
  | fieldAddr owner fieldIndex =>
    simp only [Op.resultTy] at typed
    obtain ⟨⟨mu, source⟩, _, typed⟩ := (Core.Sound.ex_bind_ok _ _ _).mp typed
    cases source with
    | structT id fields =>
      cases descriptorAt : env.structs[id]? with
      | none => simp [descriptorAt, tyErr] at typed
      | some descriptor =>
        dsimp only at typed
        simp only [descriptorAt] at typed
        split at typed
        · cases fieldAt : descriptor.fields[fieldIndex]? with
          | none => simp [fieldAt, tyErr] at typed
          | some field =>
            simp only [fieldAt] at typed
            cases typed
            simpa only [EmittedVTyResolved, Core.checkResolvedType] using
              resolved.fields id descriptor descriptorAt fieldIndex field fieldAt
        · simp [tyErr, bind, Except.bind] at typed
    | _ => cases typed

end Goose.Lower.Validation
