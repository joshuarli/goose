import Goose.Lower.Validation.PermissionSourceInductionAccess
import Goose.Lower.Validation.PermissionPreservationCallSource
import Goose.Lower.Validation.PermissionPreservationMutationSource
import Goose.Lower.Validation.ExpressionTypingAggregateOps
import Goose.Lower.Validation.ExpressionTypingCallOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

def PermissionSourceBound (env : Core.TEnv) (func : Func) (results : List Ty) (bound : Bound) : Prop :=
  ∀ {start finish : Nat}, Core.tyBound env bound start = .ok ((), finish) →
    ∀ {before after : LS} {value : Bnd}, GeneratedBuilderState before →
      lowerBound bound (lowerEnv env.mod env.vars results) before = (value, after) →
      NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) before.vals.size before after

def PermissionSourceArgument (env : Core.TEnv) (func : Func) (results : List Ty) : Arg → Prop
  | .byVal expr => PermissionStorageExprChild env func results expr
  | .byRef _ place => PermissionStoragePlaceChild env func results place

theorem permission_source_bound_children (bound : Bound) {env : Core.TEnv} {func : Func} {results : List Ty}
    (children : ∀ expr, bound = .expr expr ∨ bound = .fromEnd expr → PermissionStorageExprChild env func results expr) :
    PermissionSourceBound env func results bound := by
  intro start finish source before after value generated run
  exact newPermissions_lowerBound bound source (Nat.le_refl _)
    (fun expr member intTy next typed middle result lowered =>
      children expr member typed generated lowered) run

theorem permission_source_bound_omitted (env : Core.TEnv) (func : Func) (results : List Ty) :
    PermissionSourceBound env func results .omitted := by
  exact permission_source_bound_children .omitted (by intro expr selected; rcases selected with h | h <;> cases h)

theorem permission_source_bound_expr {env : Core.TEnv} {func : Func} {results : List Ty}
    (expr : Expr) (child : PermissionStorageExprChild env func results expr) :
    PermissionSourceBound env func results (.expr expr) := by
  apply permission_source_bound_children
  intro value selected
  rcases selected with same | impossible
  · cases same; exact child
  · cases impossible

theorem permission_source_bound_fromEnd {env : Core.TEnv} {func : Func} {results : List Ty}
    (expr : Expr) (child : PermissionStorageExprChild env func results expr) :
    PermissionSourceBound env func results (.fromEnd expr) := by
  apply permission_source_bound_children
  intro value selected
  rcases selected with impossible | same
  · cases impossible
  · cases same; exact child

theorem permission_source_slice {env : Core.TEnv} {func : Func} {results : List Ty}
    (requested : Mutability) (view : View) (lo hi : Bound) (origin : OriginId)
    (viewChild : PermissionStorageViewChild env func results view)
    (lowChild : PermissionSourceBound env func results lo) (highChild : PermissionSourceBound env func results hi) :
    PermissionStorageExprChild env func results (.slice requested view lo hi origin) := by
  intro type start finish source before after value generated run
  obtain ⟨element, writable, viewStart, viewFinish, lowFinish, highFinish, viewSource, lowSource, highSource, _⟩ :=
    tyExpr_slice_children source
  obtain ⟨viewValue, viewed, viewRun, remaining⟩ := bind_eq.mp run
  obtain ⟨low, lowState, lowRun, remaining⟩ := bind_eq.mp remaining
  obtain ⟨high, middle, highRun, remaining⟩ := bind_eq.mp remaining
  have viewedGenerated := generated.lowerView view viewRun
  exact newPermissions_lowerExpr_slice viewRun lowRun highRun (viewChild viewSource generated viewRun)
    ((lowChild lowSource viewedGenerated lowRun).weaken (advB_lowerView view _ _ _ _ viewRun).vals)
    ((highChild highSource (viewedGenerated.lowerBound lo lowRun) highRun).weaken
      (Nat.le_trans (advB_lowerView view _ _ _ _ viewRun).vals (advB_lowerBound lo _ _ _ _ lowRun).vals)) generated run

theorem permission_source_arrayLiteral {env : Core.TEnv} {func : Func} {results : List Ty}
    (type : Ty) (exprs : List Expr) (children : ∀ expr ∈ exprs, PermissionStorageExprChild env func results expr) :
    PermissionStorageExprChild env func results (.arrLit type exprs) := by
  intro result start finish source before after value generated run
  obtain ⟨_, element, childStart, childFinish, shape, count, childSource⟩ := tyExpr_arrayLiteral_children source
  obtain ⟨values, middle, childrenRun, remaining⟩ := bind_eq.mp run
  exact newPermissions_lowerExpr_arrLit childrenRun
    (newPermissions_lowerExprs_as exprs childSource (Nat.le_refl _)
      (fun expr member type childStart childFinish typed before middle value generated lowered =>
        children expr member typed generated lowered) generated childrenRun) generated run

theorem permission_source_structLiteral {env : Core.TEnv} {func : Func} {results : List Ty}
    (type : Ty) (exprs : List Expr) (children : ∀ expr ∈ exprs, PermissionStorageExprChild env func results expr) :
    PermissionStorageExprChild env func results (.structLit type exprs) := by
  intro result start finish source before after value generated run
  obtain ⟨_, descriptor, definitionFinish, childStart, childFinish, definition, childSource⟩ := tyExpr_structLiteral_children source
  obtain ⟨values, middle, childrenRun, remaining⟩ := bind_eq.mp run
  exact newPermissions_lowerExpr_structLit childrenRun
    (newPermissions_lowerExprs_struct exprs childSource (Nat.le_refl _)
      (fun expr member type childStart childFinish typed before middle value generated lowered =>
        children expr member typed generated lowered) generated childrenRun) generated run

theorem permission_source_fill {env : Core.TEnv} {func : Func} {results : List Ty}
    (type : Ty) (expr : Expr) (child : PermissionStorageExprChild env func results expr) :
    PermissionStorageExprChild env func results (.fill type expr) := by
  intro result start finish source before after value generated run
  obtain ⟨_, element, count, childStart, childFinish, shape, childSource⟩ := tyExpr_fill_child source
  obtain ⟨childValue, middle, childRun, remaining⟩ := bind_eq.mp run
  exact newPermissions_lowerExpr_fill childRun (child childSource generated childRun) generated run

theorem permission_source_pop {env : Core.TEnv} {func : Func} {results : List Ty}
    (owner : Place) (origin : OriginId) (child : PermissionStoragePlaceChild env func results owner) :
    PermissionStorageExprChild env func results (.pop owner origin) := by
  intro result start finish source before after value generated run
  obtain ⟨info, ownerStart, ownerFinish, ownerSource, element⟩ := tyExpr_pop_owner source
  exact lowerExpr_pop_newPermissionInstructions source run generated (Nat.le_refl _)
    (fun owner middle lowered => child ownerSource generated lowered)

theorem permission_source_push {env : Core.TEnv} {func : Func} {results : List Ty}
    (owner : Place) (expr : Expr) (origin : Option OriginId)
    (placeChild : PermissionStoragePlaceChild env func results owner)
    (exprChild : PermissionStorageExprChild env func results expr) :
    PermissionStorageExprChild env func results (.push owner expr origin) := by
  intro result start finish source before after value generated run
  obtain ⟨info, element, ownerStart, ownerFinish, childStart, childFinish, ownerSource, shape, childSource, _⟩ :=
    tyExpr_push_children source
  exact lowerExpr_push_newPermissionInstructions source run generated (Nat.le_refl _)
    (fun owner middle lowered => placeChild ownerSource generated lowered)
    (fun before after value generated floor lowered => (exprChild childSource generated lowered).weaken floor)

theorem permission_source_call {env : Core.TEnv} {func : Func} {results : List Ty}
    (context : ContextId) (args : List Arg) (origin : OriginId)
    (children : ∀ arg ∈ args, PermissionSourceArgument env func results arg) :
    PermissionStorageExprChild env func results (.call context args origin) := by
  intro type start finish source before after value generated run
  obtain ⟨ctx, callee, argsStart, argsFinish, resultStart, contextAt, calleeAt, length, argsSource, resultSource⟩ :=
    tyExpr_call_tables source
  exact lowerExpr_call_newPermissionInstructions source run generated (Nat.le_refl _)
    (fun values middle lowered => newPermissions_lowerArgs args length argsSource (Nat.le_refl _)
      (fun expr member type childStart childFinish typed before middle value generated lowered =>
        children (.byVal expr) member typed generated lowered)
      (fun requested place member info childStart childFinish typed before middle value generated lowered =>
        children (.byRef requested place) member typed generated lowered) generated lowered)

#print axioms permission_source_bound_children
#print axioms permission_source_slice
#print axioms permission_source_arrayLiteral
#print axioms permission_source_structLiteral
#print axioms permission_source_fill
#print axioms permission_source_pop
#print axioms permission_source_push
#print axioms permission_source_call

#print axioms permission_source_bound_omitted
#print axioms permission_source_bound_expr
#print axioms permission_source_bound_fromEnd

end Goose.Lower.Validation
