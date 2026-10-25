import Goose.Lower.Validation.PermissionInstructionReferencesBorrow

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem newPermissions_lowerPlace_var {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {value : ValueId} {index : VarId}
    (run : lowerPlace (.var index) le before = (value, after)) :
    NewPermissionInstructions module func le first before after :=
  newPermissions_free_emitDef (by trivial) run

theorem newPermissions_lowerPlace_global {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {value : ValueId} {index : GlobalId}
    (run : lowerPlace (.global index) le before = (value, after)) :
    NewPermissionInstructions module func le first before after :=
  newPermissions_free_emitDef (by trivial) run

theorem newPermissions_lowerPlace_field {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before middle after : LS} {owner value : ValueId} {place : Place} {index : Nat}
    (placeRun : lowerPlace place le before = (owner, middle))
    (children : NewPermissionInstructions module func le first before middle)
    (generated : GeneratedBuilderState before)
    (run : lowerPlace (.field place index) le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerPlace, bind_run, placeRun] at run
  exact children.compose_framed (newPermissions_free_emitDef (by trivial) run) run
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
    (generated.lowerPlace place placeRun) (by trivial)

theorem newPermissions_lowerPlace_elem {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before viewed indexed after : LS} {viewValue indexValue value : ValueId}
    {view : View} {index : Expr} {origin : OriginId}
    (viewRun : lowerView view le before = (viewValue, viewed))
    (indexRun : lowerExpr index le viewed = (indexValue, indexed))
    (viewPermissions : NewPermissionInstructions module func le first before viewed)
    (indexPermissions : NewPermissionInstructions module func le first viewed indexed)
    (generated : GeneratedBuilderState before)
    (run : lowerPlace (.elem view index origin) le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerPlace, bind_run, viewRun, indexRun] at run
  have viewedGenerated := generated.lowerView view viewRun
  have head := viewPermissions.compose_framed indexPermissions indexRun (dense_lowerExpr index)
    (advB_lowerExpr index) (types_lowerExpr index) (generatedTargetFrame_lowerExpr none index)
    viewedGenerated (by trivial)
  exact head.compose_framed (newPermissions_free_emitDef (by trivial) run) run
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
    (viewedGenerated.lowerExpr index indexRun) (by trivial)

theorem newPermissions_lowerPlace_deref_refSlice {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {value : ValueId} {index : VarId}
    (generated : GeneratedBuilderState before)
    (run : lowerPlace (.deref (.read (.var index))) le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerPlace, lowerExpr] at run
  obtain ⟨owner, middle, slotRun, loadRun⟩ := bind_eq.mp run
  have head : NewPermissionInstructions module func le first before middle :=
    newPermissions_free_emitDef (by trivial) slotRun
  obtain ⟨loaded, loadedState, emitted, rest⟩ := bind_eq.mp loadRun
  obtain ⟨recordedUnit, recorded, recordRun, result⟩ := bind_eq.mp rest
  obtain ⟨rfl, rfl⟩ := pure_eq.mp result
  have loadedPermissions := head.compose_framed
    (newPermissions_free_emitDef (by trivial) emitted) emitted
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _)
    (generatedTargetFrame_emitDef none _) (generated.emitDef _ slotRun) (by trivial)
  have neutral : NewPermissionInstructions module func le first loadedState recorded := by
    apply NewPermissionInstructions.of_blocks_eq
    have equation := congrArg Prod.snd recordRun
    simp only [recordReadValueRootRecipe_run] at equation
    split at equation
    · rw [recordValueRootSource_run] at equation
      simpa only using congrArg (fun state : LS => state.blocks) equation.symm
    · exact congrArg LS.blocks equation.symm
  exact loadedPermissions.compose_framed neutral recordRun
    (dense_recordReadValueRootRecipe _ _) (advB_recordReadValueRootRecipe _ _)
    (types_recordReadValueRootRecipe _ _) (generatedTargetFrame_recordReadValueRootRecipe none _ _)
    ((generated.emitDef _ slotRun).emitDef _ emitted) (by trivial)

theorem newPermissions_lowerView_val {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before middle after : LS} {slice value : ValueId} {expression : Expr}
    (childRun : lowerExpr expression le before = (slice, middle))
    (children : NewPermissionInstructions module func le first before middle)
    (generated : GeneratedBuilderState before)
    (run : lowerView (.val expression) le before = (value, after)) :
    NewPermissionInstructions module func le first before after := by
  simp only [lowerView, bind_run, childRun] at run
  exact children.compose_framed (newPermissions_free_emitDef (by trivial) run) run
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
    (generated.lowerExpr expression childRun) (by trivial)

theorem newPermissions_lowerBound (bound : Bound) {env : Core.TEnv} {start finish : Nat}
    (source : Core.tyBound env bound start = .ok ((), finish))
    {func : Func} {results : List Ty} {first : Nat} {before after : LS} {value : Bnd}
    (floor : first ≤ before.vals.size)
    (children : ∀ expression, bound = .expr expression ∨ bound = .fromEnd expression →
      ∀ intTy next, Core.tyExpr env expression start = .ok (.int intTy, next) →
      ∀ middle result, lowerExpr expression (lowerEnv env.mod env.vars results) before = (result, middle) →
      NewPermissionInstructions (Lower.lower env.mod) func (lowerEnv env.mod env.vars results)
        before.vals.size before middle)
    (run : lowerBound bound (lowerEnv env.mod env.vars results) before = (value, after)) :
    NewPermissionInstructions (Lower.lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  cases bound with
  | omitted =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact .of_blocks_eq rfl
  | expr expression | fromEnd expression =>
    obtain ⟨intTy, next, childSource⟩ := tyBound_child source
    simp only [lowerBound] at run
    obtain ⟨result, middle, childRun, run⟩ := bind_eq.mp run
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact (children expression (by simp) intTy next childSource _ _ childRun).weaken floor

theorem newPermissions_lowerExprs_struct (expressions : List Expr)
    {env : Core.TEnv} {types : List Ty} {start finish : Nat}
    (source : Core.tyStructExprs env types expressions start = .ok ((), finish))
    {func : Func} {results : List Ty} {first : Nat} {before after : LS} {values : List ValueId}
    (floor : first ≤ before.vals.size)
    (children : ∀ expression ∈ expressions, ∀ type start finish,
      Core.tyExpr env expression start = .ok (type, finish) →
      ∀ before middle value, GeneratedBuilderState before →
      lowerExpr expression (lowerEnv env.mod env.vars results) before = (value, middle) →
      NewPermissionInstructions (Lower.lower env.mod) func (lowerEnv env.mod env.vars results)
        before.vals.size before middle)
    (generated : GeneratedBuilderState before)
    (run : lowerExprs expressions (lowerEnv env.mod env.vars results) before = (values, after)) :
    NewPermissionInstructions (Lower.lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  cases expressions with
  | nil =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact .of_blocks_eq rfl
  | cons expression rest =>
    cases types with
    | nil => exact (rej_ok _ _ _ _).mp source |>.elim
    | cons expected types =>
      simp only [Core.tyStructExprs] at source
      obtain ⟨type, next, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
      by_cases equal : (type == expected) = true
      · simp only [equal, ite_true] at source
        simp only [lowerExprs] at run
        obtain ⟨value, middle, childRun, run⟩ := bind_eq.mp run
        obtain ⟨restValues, final, restRun, run⟩ := bind_eq.mp run
        obtain ⟨_, rfl⟩ := pure_eq.mp run
        have middleGenerated := generated.lowerExpr expression childRun
        have head := (children expression (by simp) type start next childSource before middle value generated childRun).weaken floor
        have tail := newPermissions_lowerExprs_struct rest source
          (Nat.le_trans floor (advB_lowerExpr expression _ _ _ _ childRun).vals)
          (fun e member => children e (by simp [member])) middleGenerated restRun
        exact head.compose_framed tail restRun (dense_lowerExprs rest) (advB_lowerExprs rest)
          (types_lowerExprs rest) (generatedTargetFrame_lowerExprs none rest) middleGenerated (by trivial)
      · simp [equal, chk] at source

theorem newPermissions_lowerExprs_as (expressions : List Expr)
    {env : Core.TEnv} {element : Ty} {start finish : Nat}
    (source : Core.tyExprsAs env element expressions start = .ok ((), finish))
    {func : Func} {results : List Ty} {first : Nat} {before after : LS} {values : List ValueId}
    (floor : first ≤ before.vals.size)
    (children : ∀ expression ∈ expressions, ∀ type start finish,
      Core.tyExpr env expression start = .ok (type, finish) →
      ∀ before middle value, GeneratedBuilderState before →
      lowerExpr expression (lowerEnv env.mod env.vars results) before = (value, middle) →
      NewPermissionInstructions (Lower.lower env.mod) func (lowerEnv env.mod env.vars results)
        before.vals.size before middle)
    (generated : GeneratedBuilderState before)
    (run : lowerExprs expressions (lowerEnv env.mod env.vars results) before = (values, after)) :
    NewPermissionInstructions (Lower.lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  cases expressions with
  | nil =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact .of_blocks_eq rfl
  | cons expression rest =>
    simp only [Core.tyExprsAs] at source
    obtain ⟨type, next, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
    by_cases equal : (type == element) = true
    · simp only [equal, ite_true] at source
      simp only [lowerExprs] at run
      obtain ⟨value, middle, childRun, run⟩ := bind_eq.mp run
      obtain ⟨restValues, final, restRun, run⟩ := bind_eq.mp run
      obtain ⟨_, rfl⟩ := pure_eq.mp run
      have middleGenerated := generated.lowerExpr expression childRun
      have head := (children expression (by simp) type start next childSource before middle value generated childRun).weaken floor
      have tail := newPermissions_lowerExprs_as rest source
        (Nat.le_trans floor (advB_lowerExpr expression _ _ _ _ childRun).vals)
        (fun e member => children e (by simp [member])) middleGenerated restRun
      exact head.compose_framed tail restRun (dense_lowerExprs rest) (advB_lowerExprs rest)
        (types_lowerExprs rest) (generatedTargetFrame_lowerExprs none rest) middleGenerated (by trivial)
    · simp [equal, chk] at source

#print axioms newPermissions_lowerPlace_elem
#print axioms newPermissions_lowerBound
#print axioms newPermissions_lowerExprs_struct
#print axioms newPermissions_lowerExprs_as

end Goose.Lower.Validation
