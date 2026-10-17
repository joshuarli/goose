import Goose.GIR.ReplacementContentFlowProofsCanonicalDefinitionTyping

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

inductive SliceDefinition (env : TyEnv) : Op → Prop
  | load (address : ValueId) : SliceDefinition env (.load address)
  | backing (op : Op) (source : ValueId) (backing : BackingOp op source)
      (accessed : ∀ result, source ∈ accessOperands (.def result op))
      (reference : valRefLike env.vals source = true) : SliceDefinition env op
  | call (fn : FnId) (args : List ValueId) (origin : Option OriginId) :
      SliceDefinition env (.call fn args origin)

private theorem slice_bind_ok {α β : Type} (result : Except String α) (next : α → Except String β) (value : β) :
    (result >>= next) = .ok value ↔ ∃ prior, result = .ok prior ∧ next prior = .ok value := by
  cases result <;> simp [bind,Except.bind]

theorem SliceDefinition.of_resultTy {env : TyEnv}
    (values : ValueTypeShapes env.vals)
    (globals : ∀ (index : Nat) (type : Ty) (kind : VarKind), env.globals[index]? = some (type,kind) → type.isRefLike = false)
    (fields : ∀ (index : Nat) (descriptor : StructDef), env.structs[index]? = some descriptor →
      ∀ (fieldIndex : Nat) (field : StructField), descriptor.fields[fieldIndex]? = some field → field.ty.flat = true)
    (op : Op) {mutability : Mutability} {element : Ty}
    (typed : op.resultTy env = .ok (.data (.slice mutability element))) : SliceDefinition env op := by
  have classified := DefinitionTyping.of_resultTy values globals fields op typed
  cases classified with
  | scalar op type ordinary scalar => simp [VTy.refLike,Ty.isRefLike] at scalar
  | load source mu payload reference => exact .load source
  | call fn args origin type => exact .call fn args origin
  | backing op source type backing target =>
      cases backing with
      | slice mu source low high origin =>
          simp only [Op.resultTy] at typed
          obtain ⟨⟨oldMu,elem⟩,view,_⟩ := (slice_bind_ok _ _ _).mp typed
          refine .backing _ source (.slice mu source low high origin) (by intro; simp [accessOperands,Inst.uses,Op.uses]) ?_
          simp [valRefLike,TyEnv.viewTy_known view,VTy.refLike]
      | snapshot mode source =>
          simp only [Op.resultTy] at typed
          obtain ⟨⟨mu,owner⟩,reference,_⟩ := (slice_bind_ok _ _ _).mp typed
          refine .backing _ source (.snapshot mode source) (by intro; simp [accessOperands,Inst.uses,Op.uses]) ?_
          simp [valRefLike,TyEnv.refTy_known reference,VTy.refLike,Ty.isRefLike]
      | view source =>
          simp only [Op.resultTy] at typed
          obtain ⟨sourceTy,_,typed⟩ := (slice_bind_ok _ _ _).mp typed
          cases sourceTy <;> cases typed
      | element source index | checked source index origin | proven source index =>
          simp only [Op.resultTy] at typed
          obtain ⟨⟨mu,elem⟩,_,typed⟩ := (slice_bind_ok _ _ _).mp typed
          obtain ⟨_,_,typed⟩ := (slice_bind_ok _ _ _).mp typed
          cases typed
      | push source value origin =>
          simp only [Op.resultTy] at typed
          obtain ⟨⟨mu,owner⟩,_,typed⟩ := (slice_bind_ok _ _ _).mp typed
          cases selected : owner.ownerElem? with
          | none => simp [selected,tyErr] at typed
          | some elem =>
              simp only [selected] at typed
              repeat' first
                | (obtain ⟨_,_,typed⟩ := (slice_bind_ok _ _ _).mp typed)
                | (split at typed)
              all_goals simp_all [tyErr,bind,Except.bind,pure,Except.pure]
      | field source fieldIndex =>
          simp only [Op.resultTy] at typed
          obtain ⟨⟨mu,owner⟩,_,typed⟩ := (slice_bind_ok _ _ _).mp typed
          cases owner with
          | structT id fieldTypes =>
              cases descriptorAt : env.structs[id]? with
              | none => simp [descriptorAt,tyErr] at typed
              | some descriptor =>
                  simp only [descriptorAt] at typed
                  split at typed
                  · cases fieldAt : descriptor.fields[fieldIndex]? with
                    | none => simp [fieldAt,tyErr] at typed
                    | some field => simp [fieldAt,pure,Except.pure] at typed
                  · simp [tyErr,bind,Except.bind] at typed
          | _ => cases typed

private theorem call_loop_passable (env : TyEnv) (arguments : List (Ty × ValueId))
    (checked : forIn arguments PUnit.unit (fun (param,value) _ => do
      unless (← env.dataTy value).passableTo param do
        tyErr s!"argument %{value} is not accepted by its parameter"
      pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit) :
    ∀ pair ∈ arguments, ∃ actual, env.dataTy pair.2 = .ok actual ∧ actual.passableTo pair.1 = true := by
  induction arguments with
  | nil => simp
  | cons pair rest ih =>
      rcases pair with ⟨param,value⟩
      simp only [List.forIn_cons] at checked
      cases actualAt : env.dataTy value with
      | error error => simp [actualAt,bind,Except.bind] at checked
      | ok actual =>
          by_cases passing : actual.passableTo param = true
          · have remaining : forIn rest PUnit.unit (fun (param,value) _ => do
                unless (← env.dataTy value).passableTo param do
                  tyErr s!"argument %{value} is not accepted by its parameter"
                pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit := by
              simpa [actualAt,passing,bind,Except.bind,pure,Except.pure] using checked
            intro pair member
            rcases List.mem_cons.mp member with same | member
            · subst pair; exact ⟨actual,actualAt,passing⟩
            · exact ih remaining pair member
          · simp [actualAt,passing,tyErr,bind,Except.bind] at checked

theorem call_argument_passable {env : TyEnv} {fn : FnId} {args : List ValueId}
    {origin : Option OriginId} {params results : List Ty} {type : VTy}
    (signature : env.sigs[fn]? = some (params,results))
    (typed : (Op.call fn args origin).resultTy env = .ok type)
    {index : Nat} {param : Ty} {argument : ValueId}
    (formal : params[index]? = some param) (actual : args[index]? = some argument) :
    ∃ argumentType, env.dataTy argument = .ok argumentType ∧ argumentType.passableTo param = true := by
  simp only [Op.resultTy,signature] at typed
  split at typed
  · obtain ⟨_,loop,_⟩ := (slice_bind_ok _ _ _).mp typed
    have pairs : (param,argument) ∈ params.zip args := List.mem_of_getElem? (by
      change (params.zipWith Prod.mk args)[index]? = some (param,argument)
      rw [List.getElem?_zipWith,formal,actual])
    exact call_loop_passable env (params.zip args) loop (param,argument) pairs
  · simp [tyErr,bind,Except.bind] at typed

theorem call_slice_argument_refLike {env : TyEnv} {fn : FnId} {args : List ValueId}
    {origin : Option OriginId} {params results : List Ty} {type : VTy}
    (signature : env.sigs[fn]? = some (params,results))
    (typed : (Op.call fn args origin).resultTy env = .ok type)
    {index argument : Nat} {mutability : Mutability} {element : Ty}
    (formal : params[index]? = some (.slice mutability element)) (actual : args[index]? = some argument) :
    valRefLike env.vals argument = true := by
  obtain ⟨argumentType,argumentAt,passing⟩ := call_argument_passable signature typed formal actual
  have canonical := TyEnv.dataTy_known argumentAt
  cases argumentType <;> simp_all [Ty.passableTo,Ty.isRefLike,valRefLike,VTy.refLike]

#print axioms SliceDefinition.of_resultTy

end Goose.GIR.ReplacementContentFlow.Model
