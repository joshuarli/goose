import Goose.Lower.Validation.PermissionInstructionReferencesArgs
import Goose.Lower.Validation.PermissionInstructionControlShortCircuit

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem newPermissions_lowerExpr_un {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before middle after : LS} {child value : ValueId} {expr : Expr}
    {op : UnOp} {origin : OriginId}
    (childRun : lowerExpr expr le before = (child, middle))
    (children : NewPermissionInstructions module func le first before middle)
    (generated : GeneratedBuilderState before)
    (run : lowerExpr (.un op expr origin) le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerExpr, bind_run, childRun] at run
  have same := intTyOf_eq (show intTyOf child le middle = ((intTyOf child le middle).1, (intTyOf child le middle).2) from rfl)
  rw [same] at run
  have emitted := run
  exact children.compose_framed (newPermissions_free_emitDef (by trivial) emitted) emitted
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
    (generated.lowerExpr expr childRun) (by trivial)

theorem newPermissions_lowerExpr_bin {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before leftState middle after : LS} {leftValue rightValue value : ValueId}
    {left right : Expr} {op : BinOp} {origin : OriginId}
    (leftRun : lowerExpr left le before = (leftValue, leftState))
    (rightRun : lowerExpr right le leftState = (rightValue, middle))
    (leftPermissions : NewPermissionInstructions module func le first before leftState)
    (rightPermissions : NewPermissionInstructions module func le first leftState middle)
    (generated : GeneratedBuilderState before)
    (run : lowerExpr (.bin op left right origin) le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerExpr, bind_run, leftRun, rightRun] at run
  have same := intTyOf_eq (show intTyOf leftValue le middle = ((intTyOf leftValue le middle).1, (intTyOf leftValue le middle).2) from rfl)
  rw [same] at run
  have emitted := run
  have leftGenerated := generated.lowerExpr left leftRun
  have children := leftPermissions.compose_framed rightPermissions rightRun (dense_lowerExpr right)
    (advB_lowerExpr right) (types_lowerExpr right) (generatedTargetFrame_lowerExpr none right)
    leftGenerated (by trivial)
  exact children.compose_framed (newPermissions_free_emitDef (by trivial) emitted) emitted
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
    (leftGenerated.lowerExpr right rightRun) (by trivial)

theorem newPermissions_lowerExpr_cmp {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before leftState middle after : LS} {leftValue rightValue value : ValueId}
    {left right : Expr} {op : CmpOp}
    (leftRun : lowerExpr left le before = (leftValue, leftState))
    (rightRun : lowerExpr right le leftState = (rightValue, middle))
    (leftPermissions : NewPermissionInstructions module func le first before leftState)
    (rightPermissions : NewPermissionInstructions module func le first leftState middle)
    (generated : GeneratedBuilderState before)
    (run : lowerExpr (.cmp op left right) le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerExpr, bind_run, leftRun, rightRun] at run
  rw [valTy_run] at run
  generalize (valTy leftValue le middle).1 = type at run
  have emitted := run
  have leftGenerated := generated.lowerExpr left leftRun
  have children := leftPermissions.compose_framed rightPermissions rightRun (dense_lowerExpr right)
    (advB_lowerExpr right) (types_lowerExpr right) (generatedTargetFrame_lowerExpr none right)
    leftGenerated (by trivial)
  have middleGenerated := leftGenerated.lowerExpr right rightRun
  cases type with
  | data ty =>
    cases ty <;> exact children.compose_framed
      (newPermissions_free_emitDef (by trivial) emitted) emitted (dense_emitDef _) (advB_emitDef _)
      (types_emitDef _) (generatedTargetFrame_emitDef none _) middleGenerated (by trivial)
  | view mu element =>
    exact children.compose_framed (newPermissions_free_emitDef (by trivial) emitted) emitted
      (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
      middleGenerated (by trivial)

theorem newPermissions_lowerExpr_conv {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before middle after : LS} {child value : ValueId} {expr : Expr}
    {kind : ConvKind} {target : Ty} {origin : OriginId}
    (childRun : lowerExpr expr le before = (child, middle))
    (children : NewPermissionInstructions module func le first before middle)
    (generated : GeneratedBuilderState before)
    (run : lowerExpr (.conv kind target expr origin) le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerExpr, bind_run, childRun] at run
  have same := intTyOf_eq (show intTyOf child le middle = ((intTyOf child le middle).1, (intTyOf child le middle).2) from rfl)
  rw [same] at run
  have emitted := run
  exact children.compose_framed (newPermissions_free_emitDef (by trivial) emitted) emitted
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
    (generated.lowerExpr expr childRun) (by trivial)

theorem newPermissions_lowerExpr_read {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before middle after : LS} {child value : ValueId} {place : Place}
    (childRun : lowerPlace place le before = (child, middle))
    (children : NewPermissionInstructions module func le first before middle)
    (generated : GeneratedBuilderState before)
    (run : lowerExpr (.read place) le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  change (lowerPlace place >>= fun address => do
    let loaded ← emitDef (.load address)
    recordReadValueRootRecipe loaded place
    pure loaded) le before = (value, after) at run
  obtain ⟨actualAddress, actualState, actualRun, run⟩ := bind_eq.mp run
  rw [childRun] at actualRun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj actualRun
  obtain ⟨loaded, loadedState, emitted, rest⟩ := bind_eq.mp run
  obtain ⟨recordedUnit, recorded, recordRun, result⟩ := bind_eq.mp rest
  obtain ⟨rfl, rfl⟩ := pure_eq.mp result
  have loadedPermissions := children.compose_framed
    (newPermissions_free_emitDef (by trivial) emitted) emitted
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _)
    (generatedTargetFrame_emitDef none _) (generated.lowerPlace place childRun) (by trivial)
  have neutral : NewPermissionInstructions module func le first loadedState recorded := by
    apply NewPermissionInstructions.of_blocks_eq
    have equation := congrArg Prod.snd recordRun
    cases place <;> simp only [recordReadValueRootRecipe_run] at equation
    all_goals try exact congrArg LS.blocks equation.symm
    split at equation
    · rw [recordValueRootSource_run] at equation
      simpa only using congrArg (fun state : LS => state.blocks) equation.symm
    · exact congrArg LS.blocks equation.symm
  exact loadedPermissions.compose_framed neutral recordRun
    (dense_recordReadValueRootRecipe _ _) (advB_recordReadValueRootRecipe _ _)
    (types_recordReadValueRootRecipe _ _) (generatedTargetFrame_recordReadValueRootRecipe none _ _)
    ((generated.lowerPlace place childRun).emitDef _ emitted) (by trivial)

theorem newPermissions_lowerExpr_len {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before middle after : LS} {child value : ValueId} {view : View}
    (childRun : lowerView view le before = (child, middle))
    (children : NewPermissionInstructions module func le first before middle)
    (generated : GeneratedBuilderState before)
    (run : lowerExpr (.len view) le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerExpr, bind_run, childRun] at run
  exact children.compose_framed (newPermissions_free_emitDef (by trivial) run) run
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
    (generated.lowerView view childRun) (by trivial)

theorem newPermissions_lowerExpr_not {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before middle after : LS} {child value : ValueId} {expr : Expr}
    (childRun : lowerExpr expr le before = (child, middle))
    (children : NewPermissionInstructions module func le first before middle)
    (generated : GeneratedBuilderState before)
    (run : lowerExpr (.not expr) le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerExpr, bind_run, childRun] at run
  exact children.compose_framed (newPermissions_free_emitDef (by trivial) run) run
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
    (generated.lowerExpr expr childRun) (by trivial)

theorem newPermissions_lowerExpr_fill {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before middle after : LS} {child value : ValueId} {expr : Expr} {type : Ty}
    (childRun : lowerExpr expr le before = (child, middle))
    (children : NewPermissionInstructions module func le first before middle)
    (generated : GeneratedBuilderState before)
    (run : lowerExpr (.fill type expr) le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerExpr, bind_run, childRun] at run
  exact children.compose_framed (newPermissions_free_emitDef (by trivial) run) run
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
    (generated.lowerExpr expr childRun) (by trivial)

theorem newPermissions_lowerExpr_arrLit {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before middle after : LS} {values : List ValueId} {value : ValueId}
    {expressions : List Expr} {type : Ty}
    (childrenRun : lowerExprs expressions le before = (values, middle))
    (children : NewPermissionInstructions module func le first before middle)
    (generated : GeneratedBuilderState before)
    (run : lowerExpr (.arrLit type expressions) le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerExpr, bind_run, childrenRun] at run
  exact children.compose_framed (newPermissions_free_emitDef (by trivial) run) run
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
    (generated.lowerExprs expressions childrenRun) (by trivial)

theorem newPermissions_lowerExpr_structLit {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before middle after : LS} {values : List ValueId} {value : ValueId}
    {expressions : List Expr} {type : Ty}
    (childrenRun : lowerExprs expressions le before = (values, middle))
    (children : NewPermissionInstructions module func le first before middle)
    (generated : GeneratedBuilderState before)
    (run : lowerExpr (.structLit type expressions) le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerExpr, bind_run, childrenRun] at run
  exact children.compose_framed (newPermissions_free_emitDef (by trivial) run) run
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
    (generated.lowerExprs expressions childrenRun) (by trivial)

theorem newPermissions_lowerExpr_slice {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before viewed lowState middle after : LS} {viewValue value : ValueId}
    {low high : Bnd} {view : View} {lo hi : Bound} {mu : Mutability} {origin : OriginId}
    (viewRun : lowerView view le before = (viewValue, viewed))
    (loRun : lowerBound lo le viewed = (low, lowState))
    (hiRun : lowerBound hi le lowState = (high, middle))
    (viewPermissions : NewPermissionInstructions module func le first before viewed)
    (loPermissions : NewPermissionInstructions module func le first viewed lowState)
    (hiPermissions : NewPermissionInstructions module func le first lowState middle)
    (generated : GeneratedBuilderState before)
    (run : lowerExpr (.slice mu view lo hi origin) le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerExpr, bind_run, viewRun, loRun, hiRun] at run
  have viewedGenerated := generated.lowerView view viewRun
  have lowGenerated := viewedGenerated.lowerBound lo loRun
  have head := viewPermissions.compose_framed loPermissions loRun (dense_lowerBound lo)
    (advB_lowerBound lo) (types_lowerBound lo) (generatedTargetFrame_lowerBound none lo)
    viewedGenerated (by trivial)
  have children := head.compose_framed hiPermissions hiRun (dense_lowerBound hi)
    (advB_lowerBound hi) (types_lowerBound hi) (generatedTargetFrame_lowerBound none hi)
    lowGenerated (by trivial)
  exact children.compose_framed (newPermissions_free_emitDef (by trivial) run) run
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
    (lowGenerated.lowerBound hi hiRun) (by trivial)

#print axioms newPermissions_lowerExpr_read
#print axioms newPermissions_lowerExpr_len
#print axioms newPermissions_lowerExpr_not
#print axioms newPermissions_lowerExpr_fill
#print axioms newPermissions_lowerExpr_arrLit
#print axioms newPermissions_lowerExpr_structLit
#print axioms newPermissions_lowerExpr_slice

#print axioms newPermissions_lowerExpr_un
#print axioms newPermissions_lowerExpr_bin
#print axioms newPermissions_lowerExpr_cmp
#print axioms newPermissions_lowerExpr_conv

end Goose.Lower.Validation
