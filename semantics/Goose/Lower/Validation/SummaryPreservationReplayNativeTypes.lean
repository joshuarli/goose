import Goose.Lower.Validation.ExpressionTypingGenerated
import Goose.Lower.Validation.EmittedTypingTrace

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.GIR

def NativeRows (types : Array (Option VTy)) (state : LS) : Prop :=
  ∀ (value : ValueId) (type : VTy), state.vals[value]? = some (some type) → types[value]? = some (some type)

namespace NativeRows

theorem refl (state : LS) : NativeRows state.vals state := fun _ _ row => row

theorem of_prefix {types : Array (Option VTy)} {before after : LS}
    (native : NativeRows types after) (retained : TypePrefix before after) : NativeRows types before :=
  fun value type row => native value type (retained value type row)

theorem expression {types : Array (Option VTy)} {env : TEnv} {expr : Expr} {type : Ty}
    {start finish : Nat} {results : List Ty} {before after : LS} {value : ValueId}
    (native : NativeRows types after) (generated : GeneratedBuilderState before)
    (source : Core.tyExpr env expr start = .ok (type, finish))
    (run : lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) : types[value]? = some (some (.data type)) :=
  native value (.data type) (lowerExpr_generated_typed expr source run live generated)

theorem place {types : Array (Option VTy)} {env : TEnv} {place : Place} {info : PlaceInfo}
    {start finish : Nat} {results : List Ty} {before after : LS} {value : ValueId}
    (native : NativeRows types after) (generated : GeneratedBuilderState before)
    (source : Core.tyPlace env place start = .ok (info, finish))
    (run : lowerPlace place (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) : ∃ mutability, types[value]? = some (some (.data (.ref mutability info.ty))) := by
  obtain ⟨mutability, row⟩ := lowerPlace_generated_typed place source run live generated
  exact ⟨mutability, native value _ row⟩

theorem place_ownerTy {types : Array (Option VTy)} {env : TEnv} {place : Place} {info : PlaceInfo}
    {start finish : Nat} {results : List Ty} {before after : LS} {value : ValueId}
    (native : NativeRows types after) (generated : GeneratedBuilderState before)
    (source : Core.tyPlace env place start = .ok (info, finish))
    (run : lowerPlace place (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) : ownerTy types value = some info.ty := by
  obtain ⟨mutability, row⟩ := native.place generated source run live
  simp only [ownerTy, row]

theorem view {types : Array (Option VTy)} {env : TEnv} {view : View} {info : Ty × Bool}
    {start finish : Nat} {results : List Ty} {before after : LS} {value : ValueId}
    (native : NativeRows types after) (generated : GeneratedBuilderState before)
    (source : Core.tyView env view start = .ok (info, finish))
    (run : lowerView view (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) : ∃ mutability, types[value]? = some (some (.view mutability info.1)) := by
  obtain ⟨mutability, row⟩ := lowerView_generated_typed view source run live generated
  exact ⟨mutability, native value _ row⟩

theorem scalar_expression {types : Array (Option VTy)} {env : TEnv} {expr : Expr} {type : Ty}
    {start finish : Nat} {results : List Ty} {before after : LS} {value : ValueId}
    (native : NativeRows types after) (generated : GeneratedBuilderState before)
    (source : Core.tyExpr env expr start = .ok (type, finish))
    (run : lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) (nonref : type.isRefLike = false) : valRefLike types value = false := by
  simp only [valRefLike, native.expression generated source run live, VTy.refLike, nonref]

theorem block {types : Array (Option VTy)} {env : TEnv} {body : Core.Block} {type : Ty}
    {start finish : Nat} {results : List Ty} {before after : LS} {value : ValueId}
    (native : NativeRows types after) (generated : GeneratedBuilderState before)
    (source : Core.tyBlock env [] body start = .ok (type, finish))
    (run : lowerBlock none [] true body (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true) : types[value]? = some (some (.data type)) :=
  native value (.data type) (lowerBlock_generated_typed body source run live generated)

theorem local_read {types : Array (Option VTy)} {module : Core.Module} {vars : Array LocalVar}
    {variableId : VarId} {localVar : LocalVar} {results : List Ty} {before : LS}
    (native : NativeRows types (lowerExpr (.read (.var variableId)) (lowerEnv module vars results) before).2)
    (row : vars[variableId]? = some localVar)
    (live : (lowerExpr (.read (.var variableId)) (lowerEnv module vars results) before).2.cur.isSome = true) :
    types[(lowerExpr (.read (.var variableId)) (lowerEnv module vars results) before).1]? =
      some (some (.data localVar.ty)) := by
  have initial := (dead_lowerExpr (.read (.var variableId))).live_before (le := lowerEnv module vars results) rfl live
  cases current : before.cur with
  | none => simp [current] at initial
  | some block =>
    let le := lowerEnv module vars results
    let address := lowerPlace (.var variableId) le before
    have slotRow : le.slots[variableId]? = some ⟨localVar.ty, localVar.kind, localVar.scope, variableId⟩ := by
      simp [le, lowerEnv, Array.getElem?_mapIdx, row]
    have addressExists : ∃ mutability, (Op.slotAddr variableId).resultTy (tyEnv le before) =
        .ok (.data (.ref mutability localVar.ty)) := by
      simp only [Op.resultTy, tyEnv, slotRow]
      exact ⟨_, rfl⟩
    obtain ⟨mutability, addressType⟩ := addressExists
    have recorded := emitDef_recorded (le := le) current addressType
    have addressRow : address.2.vals[address.1]? = some (some
        (.data (.ref mutability localVar.ty))) := recorded.2.2.1
    have addressCurrent : address.2.cur = some block := recorded.2.1.trans current
    have loaded := lowerExpr_read_typed_of_place (placeRun := (rfl : lowerPlace (.var variableId) le before = address))
      addressRow addressCurrent
    exact native _ _ loaded.2

theorem load {types : Array (Option VTy)} {le : LEnv} {before after : LS} {address value : ValueId}
    {mutability : Mutability} {type : Ty}
    (native : NativeRows types after)
    (addressType : before.vals[address]? = some (some (.data (.ref mutability type))))
    (run : emitDef (.load address) le before = (value, after)) (live : after.cur.isSome = true) :
    types[value]? = some (some (.data type)) := by
  have initial := (dead_emitDef (.load address)).live_before run live
  cases current : before.cur with
  | none => simp [current] at initial
  | some block =>
    have resultType : (Op.load address).resultTy (tyEnv le before) = .ok (.data type) := by
      simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, addressType,
        pure, Except.pure, bind, Except.bind]
    have recorded := emitDef_recorded (le := le) current resultType
    rw [run] at recorded
    exact native value _ recorded.2.2.1

end NativeRows

end Goose.Lower.Validation.SummaryPreservation
