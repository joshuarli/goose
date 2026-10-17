import Goose.GIR.ReplacementContentFlowProofsCanonicalTypes
import Goose.GIR.ReplacementContentFlowProofsCanonicalOps

namespace Goose.GIR.ReplacementContentFlow.Model

open Goose.Core

inductive BackingOp : Op → ValueId → Prop
  | field (source field : Nat) : BackingOp (.fieldAddr source field) source
  | element (source index : Nat) : BackingOp (.refElem source index) source
  | slice (mutability : Mutability) (source : ValueId) (low high : Bnd) (origin : Option OriginId) :
      BackingOp (.viewSlice mutability source low high origin) source
  | checked (source index : Nat) (origin : Option OriginId) : BackingOp (.indexChecked source index origin) source
  | proven (source index : Nat) : BackingOp (.indexProven source index) source
  | view (source : ValueId) : BackingOp (.sliceView source) source
  | push (source value : ValueId) (origin : Option OriginId) : BackingOp (.push source value origin) source
  | snapshot (mode : SnapshotMode) (source : ValueId) : BackingOp (.snapshot mode source) source

theorem BackingOp.result {func : Func} {vt : Array (Option VTy)} {value source : ValueId} {op : Op}
    (backing : BackingOp op source) (reference : valRefLike vt value = true) (state : State) :
    result func vt state value op = flowAt state.values source := by
  cases backing <;> simp [ReplacementContentFlow.Model.result,reference]

theorem BackingOp.rootsOfDef {results : Array (List RootRef)} {vt : Array (Option VTy)}
    {func : Func} {provenance : Prov} {value source : ValueId} {op : Op}
    (backing : BackingOp op source) :
    rootsOfDef results vt func provenance value op = rootsAt provenance.vals source := by
  cases backing <;> rfl

theorem BackingOp.noncall {source : ValueId} {op : Op} (backing : BackingOp op source)
    (fn : FnId) (args : List ValueId) (origin : Option OriginId) : op ≠ .call fn args origin := by
  cases backing <;> intro same <;> cases same

inductive DefinitionTyping (env : TyEnv) : Op → VTy → Prop
  | scalar (op : Op) (type : VTy) (ordinary : ∀ fn args origin, op ≠ .call fn args origin)
      (scalar : type.refLike = false) : DefinitionTyping env op type
  | slot (index : SlotId) (storage : Slot) (mutability : Mutability)
      (row : env.slots[index]? = some storage) :
      DefinitionTyping env (.slotAddr index) (.data (.ref mutability storage.ty))
  | global (index : GlobalId) (type : Ty) (kind : VarKind) (mutability : Mutability)
      (row : env.globals[index]? = some (type,kind)) (storage : type.isRefLike = false) :
      DefinitionTyping env (.globalAddr index) (.data (.ref mutability type))
  | load (source : ValueId) (mutability : Mutability) (payload : Ty)
      (typed : env.refTy source = .ok (mutability,payload)) :
      DefinitionTyping env (.load source) (.data payload)
  | freeze (source : ValueId) (mutability : Mutability) (payload : Ty)
      (typed : env.refTy source = .ok (mutability,payload)) :
      DefinitionTyping env (.refFreeze source) (.data (.ref .readOnly payload))
  | borrow (source : ValueId) (mutability : Mutability) (payload : Ty)
      (typed : env.refTy source = .ok (mutability,payload)) (owner : payload.ownerElem?.isSome = true) :
      DefinitionTyping env (.ownerBorrow source) (.data (.ref .mutable payload))
  | backing (op : Op) (source : ValueId) (type : VTy) (backing : BackingOp op source)
      (target : ∀ mutability payload, type = .data (.ref mutability payload) →
        payload.isRefLike = false ∧ payload.ownerElem?.isSome = false) : DefinitionTyping env op type
  | call (fn : FnId) (args : List ValueId) (origin : Option OriginId) (type : VTy) :
      DefinitionTyping env (.call fn args origin) type

private theorem typed_bind_ok {α β : Type} (result : Except String α) (next : α → Except String β) (value : β) :
    (result >>= next) = .ok value ↔ ∃ prior, result = .ok prior ∧ next prior = .ok value := by
  cases result <;> simp [bind,Except.bind]

private theorem data_not_address {type : Ty} (flat : type.flat = true) (sourceMutability : Mutability) :
    ∀ mutability payload, VTy.data (.ref sourceMutability type) = .data (.ref mutability payload) →
      payload.isRefLike = false ∧ payload.ownerElem?.isSome = false := by
  intro mutability payload same
  have same : type = payload := (Ty.ref.inj (VTy.data.inj same)).2
  subst payload
  exact flat_not_address flat

theorem DefinitionTyping.of_resultTy {env : TyEnv}
    (values : ValueTypeShapes env.vals)
    (globals : ∀ (index : Nat) (type : Ty) (kind : VarKind), env.globals[index]? = some (type,kind) → type.isRefLike = false)
    (fields : ∀ (index : Nat) (descriptor : StructDef), env.structs[index]? = some descriptor →
      ∀ (fieldIndex : Nat) (field : StructField), descriptor.fields[fieldIndex]? = some field → field.ty.flat = true)
    (op : Op) {type : VTy} (typed : op.resultTy env = .ok type) : DefinitionTyping env op type := by
  cases op with
  | constInt integer number =>
      simp only [Op.resultTy] at typed
      split at typed
      · cases typed; exact .scalar _ _ (by intros; intro h; cases h) rfl
      · cases typed
  | constBool value => cases typed; exact .scalar _ _ (by intros; intro h; cases h) rfl
  | constUnit => cases typed; exact .scalar _ _ (by intros; intro h; cases h) rfl
  | bin operator integer left right origin
  | cmp operator integer left right
  | boolCmp operator left right
  | boolNot value
  | next integer value
  | viewLen value
  | un operator integer value origin
  | conv conversion source destination value origin =>
      simp only [Op.resultTy] at typed
      try simp only [typed_bind_ok] at typed
      repeat' first
        | (rcases typed with ⟨_,_,typed⟩)
        | (split at typed <;> try simp only [typed_bind_ok] at typed)
      all_goals try simp_all only [tyErr,bind,Except.bind,pure,Except.pure,reduceCtorEq]
      all_goals exact .scalar _ _ (by intros; intro h; cases h) rfl
  | slotAddr slot =>
      simp only [Op.resultTy] at typed
      cases row : env.slots[slot]? with
      | none => simp [row,tyErr] at typed
      | some storage =>
          simp only [row] at typed
          cases typed
          exact .slot slot storage _ row
  | globalAddr global =>
      simp only [Op.resultTy] at typed
      cases row : env.globals[global]? with
      | none => simp [row,tyErr] at typed
      | some descriptor =>
          obtain ⟨source,kind⟩ := descriptor
          simp only [row] at typed
          cases typed
          exact .global global source kind _ row (globals global source kind row)
  | refElem value index | indexChecked value index origin | indexProven value index =>
      simp only [Op.resultTy] at typed
      obtain ⟨⟨mu,element⟩,view,typed⟩ := (typed_bind_ok _ _ _).mp typed
      obtain ⟨_,_,typed⟩ := (typed_bind_ok _ _ _).mp typed
      cases typed
      all_goals apply DefinitionTyping.backing _ value _ (by constructor)
      all_goals exact data_not_address (values.view view) mu
  | refFreeze value =>
      simp only [Op.resultTy] at typed
      obtain ⟨⟨mu,element⟩,reference,typed⟩ := (typed_bind_ok _ _ _).mp typed
      cases typed
      exact .freeze value mu element reference
  | load value =>
      simp only [Op.resultTy] at typed
      obtain ⟨⟨mu,element⟩,reference,typed⟩ := (typed_bind_ok _ _ _).mp typed
      cases typed
      exact .load value mu element reference
  | ownerBorrow value =>
      simp only [Op.resultTy] at typed
      obtain ⟨⟨mu,source⟩,reference,typed⟩ := (typed_bind_ok _ _ _).mp typed
      dsimp only at typed
      split at typed
      · cases source <;> simp only [tyErr] at typed
        all_goals cases typed
        all_goals exact .borrow value mu _ reference rfl
      · simp [tyErr,bind,Except.bind] at typed
  | snapshot mode value =>
      simp only [Op.resultTy] at typed
      obtain ⟨⟨mu,source⟩,reference,typed⟩ := (typed_bind_ok _ _ _).mp typed
      cases selected : GIR.arrayElem? source with
      | none => simp [selected,tyErr] at typed
      | some element =>
          simp only [selected] at typed
          cases typed
          exact .backing _ value _ (.snapshot mode value) (by intro mutability payload same; simp at same)
  | sliceView value =>
      simp only [Op.resultTy] at typed
      obtain ⟨source,data,typed⟩ := (typed_bind_ok _ _ _).mp typed
      cases source with
      | slice mutability element =>
          cases typed
          exact .backing _ value _ (.view value) (by intro mutability payload same; simp at same)
      | _ => cases typed
  | viewSlice mu value low high origin =>
      simp only [Op.resultTy] at typed
      obtain ⟨⟨oldMu,element⟩,view,typed⟩ := (typed_bind_ok _ _ _).mp typed
      try simp only [typed_bind_ok] at typed
      repeat' first
        | (rcases typed with ⟨_,_,typed⟩)
        | (split at typed <;> try simp only [typed_bind_ok] at typed)
      all_goals try simp_all only [tyErr,bind,Except.bind,pure,Except.pure,reduceCtorEq]
      all_goals exact .backing _ value _ (.slice mu value low high origin) (by intro mutability payload same; simp at same)
  | arrayLen value =>
      simp only [Op.resultTy] at typed
      obtain ⟨⟨mu,source⟩,_,typed⟩ := (typed_bind_ok _ _ _).mp typed
      split at typed <;> cases typed
      exact .scalar _ _ (by intros; intro h; cases h) rfl
  | push owner value origin | pop owner origin =>
      simp only [Op.resultTy] at typed
      obtain ⟨⟨mu,source⟩,reference,typed⟩ := (typed_bind_ok _ _ _).mp typed
      cases selected : source.ownerElem? with
      | none => simp [selected,tyErr] at typed
      | some element =>
          have flat : element.flat = true := by
            rcases values.reference reference with storable | slice
            · exact storable_owner_element storable selected
            · cases source <;> simp_all [Ty.isRefSlice,Ty.ownerElem?]
          simp only [selected] at typed
          try simp only [typed_bind_ok] at typed
          repeat' first
            | (rcases typed with ⟨_,_,typed⟩)
            | (split at typed <;> try simp only [typed_bind_ok] at typed)
          all_goals try simp_all only [tyErr,bind,Except.bind,pure,Except.pure,reduceCtorEq]
          all_goals first
            | exact .backing _ owner _ (.push owner value origin) (data_not_address flat _)
            | exact .scalar _ _ (by intros; intro h; cases h) (flat_not_address flat).1
  | call fn args origin => exact .call fn args origin type
  | arrLit source args | arrFill source value | structLit source args =>
      simp only [Op.resultTy] at typed
      cases source <;> try (cases typed)
      all_goals try simp only [typed_bind_ok] at typed
      repeat' first
        | (rcases typed with ⟨_,_,typed⟩)
        | (split at typed <;> try simp only [typed_bind_ok] at typed)
      all_goals try simp_all only [tyErr,bind,Except.bind,pure,Except.pure,reduceCtorEq]
      all_goals exact .scalar _ _ (by intros; intro h; cases h) rfl
  | fieldAddr owner fieldIndex =>
      simp only [Op.resultTy] at typed
      obtain ⟨⟨mu,source⟩,_,typed⟩ := (typed_bind_ok _ _ _).mp typed
      cases source with
      | structT id fieldTypes =>
          cases descriptorAt : env.structs[id]? with
          | none => simp [descriptorAt,tyErr] at typed
          | some descriptor =>
              dsimp only at typed
              simp only [descriptorAt] at typed
              split at typed
              · cases fieldAt : descriptor.fields[fieldIndex]? with
                | none => simp [fieldAt,tyErr] at typed
                | some field =>
                    simp only [fieldAt] at typed
                    cases typed
                    exact .backing _ owner _ (.field owner fieldIndex)
                      (data_not_address (fields id descriptor descriptorAt fieldIndex field fieldAt) _)
              · simp [tyErr,bind,Except.bind] at typed
      | _ => cases typed

#print axioms DefinitionTyping.of_resultTy

end Goose.GIR.ReplacementContentFlow.Model
