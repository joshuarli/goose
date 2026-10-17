import Goose.Lower.Validation.ExpressionTypingFreshContents

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

inductive IntrinsicContentsOperation : Op → Prop where
  | load (owner) : IntrinsicContentsOperation (.load owner)
  | push (owner value origin) : IntrinsicContentsOperation (.push owner value origin)
  | pop (owner origin) : IntrinsicContentsOperation (.pop owner origin)
  | call (function values origin) : IntrinsicContentsOperation (.call function values origin)
  | viewSlice (mu view lo hi origin) : IntrinsicContentsOperation (.viewSlice mu view lo hi origin)
  | sliceView (owner) : IntrinsicContentsOperation (.sliceView owner)
  | structLit (ty values) : IntrinsicContentsOperation (.structLit ty values)
  | arrLit (ty values) : IntrinsicContentsOperation (.arrLit ty values)
  | arrFill (ty value) : IntrinsicContentsOperation (.arrFill ty value)

theorem freshContentsEvidence_intrinsic {le : LEnv} {before after : LS}
    {value : ValueId} {op : Op} {target : Ty} {current : BlockId}
    (intrinsic : IntrinsicContentsOperation op)
    (typed : op.resultTy (tyEnv le before) = .ok (.data (.ref .mutable target)))
    (checked : before.DenseDefinitions) (bounded : LiveBound before)
    (live : before.cur = some current) (run : emitDef op le before = (value, after)) :
    FreshContentsEvidence le before.vals.size after value := by
  have recorded := (emitDef_recorded live typed).2.2.1
  change (emitDef op le before).2.vals[(emitDef op le before).1]? = _ at recorded
  rw [run] at recorded
  apply freshContentsEvidence_definition checked bounded live run
  cases intrinsic <;> simp only [ContentsOperation, typedPermissions, recorded, beq_self_eq_true]

theorem FreshContentsEvidence.recordReadValueRootRecipe {le : LEnv} {first : Nat}
    {before : LS} {value : ValueId} (evidence : FreshContentsEvidence le first before value)
    (place : Place) :
    FreshContentsEvidence le first (Goose.Lower.recordReadValueRootRecipe value place le before).2 value := by
  have values : (Goose.Lower.recordReadValueRootRecipe value place le before).2.vals = before.vals := by
    cases place <;> simp only [recordReadValueRootRecipe_run] <;> first
      | rfl
      | (split <;> simp only [recordValueRootSource_run] <;> rfl)
  have blocks : (Goose.Lower.recordReadValueRootRecipe value place le before).2.blocks = before.blocks := by
    cases place <;> simp only [recordReadValueRootRecipe_run] <;> first
      | rfl
      | (split <;> simp only [recordValueRootSource_run] <;> rfl)
  simpa only [FreshContentsEvidence, permissionFunc, values, blocks] using evidence

theorem lowerExpr_read_fresh_contents_of_place {le : LEnv} {before middle after : LS}
    {place : Place} {address value : ValueId} {mu : Mutability} {target : Ty} {current : BlockId}
    (placeRun : lowerPlace place le before = (address, middle))
    (placeTyped : middle.vals[address]? = some (some (.data (.ref mu (.ref .mutable target)))))
    (checked : middle.DenseDefinitions) (bounded : LiveBound middle) (live : middle.cur = some current)
    (run : lowerExpr (.read place) le before = (value, after)) :
    FreshContentsEvidence le middle.vals.size after value := by
  have typed : (Op.load address).resultTy (tyEnv le middle) = .ok (.data (.ref .mutable target)) := by
    simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, placeTyped,
      pure, Except.pure, bind, Except.bind]
  let emitted := emitDef (.load address) le middle
  have shape : (emitted.1, (recordReadValueRootRecipe emitted.1 place le emitted.2).2) =
      (value, after) := by
    simpa only [lowerExpr, bind_run, placeRun, pure_run, emitted] using run
  cases shape
  exact (freshContentsEvidence_intrinsic (.load _) typed checked bounded live
    (rfl : emitDef (.load address) le middle = emitted)).recordReadValueRootRecipe place

theorem lowerExpr_pop_fresh_contents_of_owner {le : LEnv} {before middle after : LS}
    {owner : Place} {address value : ValueId} {mu : Mutability} {ownerTy target : Ty}
    {origin : OriginId} {current : BlockId}
    (ownerRun : lowerPlace owner le before = (address, middle))
    (ownerTyped : middle.vals[address]? = some (some (.data (.ref mu ownerTy))))
    (element : ownerTy.ownerElem? = some (.ref .mutable target))
    (checked : middle.DenseDefinitions) (bounded : LiveBound middle) (live : middle.cur = some current)
    (run : lowerExpr (.pop owner origin) le before = (value, after)) :
    FreshContentsEvidence le middle.vals.size after value := by
  have typed : (Op.pop address (some origin)).resultTy (tyEnv le middle) =
      .ok (.data (.ref .mutable target)) := by
    simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, ownerTyped, element,
      pure, Except.pure, bind, Except.bind]
  have emitted : emitDef (.pop address (some origin)) le middle = (value, after) := by
    simpa only [lowerExpr, bind_run, ownerRun] using run
  exact freshContentsEvidence_intrinsic (.pop ..) typed checked bounded live emitted

theorem lowerExpr_push_fresh_contents_of_children {le : LEnv} {before ownerState middle after : LS}
    {owner : Place} {expr : Expr} {address child value : ValueId} {mu : Mutability} {ownerTy target : Ty}
    {origin : Option OriginId} {current : BlockId}
    (ownerRun : lowerPlace owner le before = (address, ownerState))
    (childRun : lowerExpr expr le ownerState = (child, middle))
    (ownerTyped : middle.vals[address]? = some (some (.data (.ref mu ownerTy))))
    (childTyped : middle.vals[child]? = some (some (.data target)))
    (element : ownerTy.ownerElem? = some target)
    (checked : middle.DenseDefinitions) (bounded : LiveBound middle) (live : middle.cur = some current)
    (run : lowerExpr (.push owner expr origin) le before = (value, after)) :
    FreshContentsEvidence le middle.vals.size after value := by
  have typed : (Op.push address child origin).resultTy (tyEnv le middle) =
      .ok (.data (.ref .mutable target)) := by
    simp [Op.resultTy, TyEnv.refTy, TyEnv.dataTy, TyEnv.valTy, tyEnv, ownerTyped, childTyped, element,
      pure, Except.pure, bind, Except.bind]
  have emitted : emitDef (.push address child origin) le middle = (value, after) := by
    simpa only [lowerExpr, bind_run, ownerRun, childRun] using run
  exact freshContentsEvidence_intrinsic (.push ..) typed checked bounded live emitted

#print axioms freshContentsEvidence_intrinsic
#print axioms lowerExpr_read_fresh_contents_of_place
#print axioms lowerExpr_pop_fresh_contents_of_owner
#print axioms lowerExpr_push_fresh_contents_of_children

end Goose.Lower.Validation
