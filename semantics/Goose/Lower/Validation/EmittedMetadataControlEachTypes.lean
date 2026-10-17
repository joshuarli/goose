import Goose.Lower.Validation.EmittedMetadataSourceContracts
import Goose.Lower.Validation.ExpressionTypingGenerated
import Goose.Lower.Validation.SourceStatementTypingControl

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem metadata_each_reference_binder {localVar : LocalVar} {element : Ty} {writable : Bool} {start finish : Nat}
    (source : loopVarOk localVar true element writable start = .ok ((), finish)) :
    ∃ requested, localVar.ty = .ref requested element ∧ (requested = .mutable → writable = true) := by
  obtain ⟨requested, shape⟩ := (loopVarOk_ok _ _ _ _ _ _ source).2
  refine ⟨requested, shape, ?_⟩
  intro mutable
  subst requested
  have permission : requireWrite "a mutable loop reference" writable start = .ok ((), finish) := by
    simpa [Core.loopVarOk, shape, pure, bind, StateT.pure, StateT.bind, Except.pure, Except.bind] using source
  exact ((requireWrite_ok _ _ _ _).mp permission).1

theorem metadata_each_view_typed (view : View) {env : Core.TEnv} {results : List Ty}
    {element : Ty} {writable : Bool} {start finish : Nat}
    (source : Core.tyView env view start = .ok ((element, writable), finish))
    {before after : LS} {value : ValueId} (generated : GeneratedBuilderState before)
    (run : lowerView view (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) :
    ∃ mu, after.vals[value]? = some (some (.view mu element)) ∧ (writable = true → mu = .mutable) := by
  cases writable with
  | false =>
    obtain ⟨mu, row⟩ := lowerView_generated_typed view source run live generated
    exact ⟨mu, row, by intro impossible; cases impossible⟩
  | true => exact ⟨.mutable, lowerView_generated_writable_typed view source run live generated, by intro; rfl⟩

theorem metadata_each_value_typed {le : LEnv} {before : LS} {slot : SlotId} {localVar : LocalVar}
    {byRef writable : Bool} {element : Ty} {actual : Mutability} {address : ValueId} {start finish : Nat}
    (source : loopVarOk localVar byRef element writable start = .ok ((), finish))
    (row : le.vars[slot]? = some localVar)
    (mutable : writable = true → actual = .mutable)
    (addressAt : before.vals[address]? = some (some (.data (.ref actual element))))
    {block : BlockId} (live : before.cur = some block) :
    let value := eachElemValue slot byRef address le before
    value.2.cur = before.cur ∧ value.2.vals[value.1]? = some (some (.data localVar.ty)) := by
  cases byRef with
  | false =>
    have same : localVar.ty = element := (loopVarOk_ok _ _ _ _ _ _ source).2
    have operation : (Op.load address).resultTy (tyEnv le before) = .ok (.data element) := by
      simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, addressAt,
        pure, Except.pure, bind, Except.bind]
    have recorded := emitDef_recorded live operation
    change (emitDef (.load address) le before).2.cur = before.cur ∧
      (emitDef (.load address) le before).2.vals[(emitDef (.load address) le before).1]? = some (some (.data localVar.ty))
    exact ⟨recorded.2.1, by rw [same]; exact recorded.2.2.1⟩
  | true =>
    obtain ⟨requested, shape, permission⟩ := metadata_each_reference_binder source
    have atLeast : actual.atLeast requested = true := by
      cases requested with
      | readOnly => cases actual <;> rfl
      | mutable => rw [mutable (permission rfl)]; rfl
    have typed := borrowTo_typed (le := le) addressAt atLeast live
    simpa only [eachElemValue, ite_true, bind_run, read_apply, row, shape] using typed

theorem metadata_each_pre_typed {env : Core.TEnv} {results : List Ty} {state : LS}
    {slot : SlotId} {localVar : LocalVar} {index : Option VarId} {value counter : ValueId} {origin : OriginId}
    (row : env.vars[slot]? = some localVar)
    (indexRows : ∀ i, index = some i → ∃ indexVar, env.vars[i]? = some indexVar ∧ indexVar.ty = .int .i64)
    (valueAt : state.vals[value]? = some (some (.data localVar.ty)))
    (counterAt : state.vals[counter]? = some (some (.data (.int .i64)))) :
    EmittedPreTyped (lowerEnv env.mod env.vars results) state
      ((slot, value, origin) :: (match (generalizing := false) index with
        | some i => [(i, counter, origin)] | none => [])) := by
  intro actualSlot actualValue actualOrigin member
  rcases List.mem_cons.mp member with same | rest
  · cases same
    exact ⟨⟨localVar.ty, localVar.kind, localVar.scope, slot⟩,
      by simp [lowerEnv, Array.getElem?_mapIdx, row], valueAt⟩
  · cases index with
    | none => cases rest
    | some i =>
      have same : (actualSlot, actualValue, actualOrigin) = (i, counter, origin) := by simpa using rest
      obtain ⟨indexVar, indexRow, indexType⟩ := indexRows i rfl
      have slotAt : (lowerEnv env.mod env.vars results).slots[i]? =
          some ⟨indexVar.ty, indexVar.kind, indexVar.scope, i⟩ := by
        simp [lowerEnv, Array.getElem?_mapIdx, indexRow]
      have valueAt : state.vals[counter]? = some (some (.data indexVar.ty)) := by
        simpa only [indexType] using counterAt
      cases same
      exact ⟨_, slotAt, valueAt⟩

#print axioms metadata_each_reference_binder
#print axioms metadata_each_value_typed
#print axioms metadata_each_pre_typed

end Goose.Lower.Validation
