import Goose.Lower.Validation.SourceCanonicalRootFloorsProjection
import Goose.Lower.Validation.SourceCanonicalRootFloorsMetadata

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace Goose.Lower.Validation.SourceCanonicalRootFloors

open Goose.Core

private theorem source_bind_congr (first second : SourceRootsM α)
    (left right : α → SourceRootsM β) (same : first = second)
    (next : ∀ value, left value = right value) :
    (first >>= left) = (second >>= right) := by
  cases same
  have equal : left = right := funext next
  cases equal
  rfl

mutual

theorem collectSourceExprRoots_scopes (env : PEnv) (scopes : List Nat) (expression : Expr) :
    collectSourceExprRoots { env with scopes := scopes } expression =
      collectSourceExprRoots env expression := by
  cases expression
  all_goals conv =>
    lhs
    rw [collectSourceExprRoots.eq_def]
  all_goals conv =>
    rhs
    rw [collectSourceExprRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact collectSourceExprRoots_scopes _ _ _
    | exact collectSourcePlaceRoots_scopes _ _ _
    | exact collectSourceViewRoots_scopes _ _ _
    | exact collectSourceBoundRoots_scopes _ _ _
    | exact collectSourceArgumentRoots_scopes _ _ _
    | exact collectSourceExprListRoots_scopes _ _ _
    | exact collectSourceBlockRoots_scopes _ _ _
    | exact collectSourceStmtListRoots_scopes _ _ _
    | exact collectSourcePrintRoots_scopes _ _ _
    | exact collectSourceStmtRoots_scopes _ _ _
    | apply source_bind_congr
    | intro value
termination_by sizeOf expression

theorem collectSourcePlaceRoots_scopes (env : PEnv) (scopes : List Nat) (place : Place) :
    collectSourcePlaceRoots { env with scopes := scopes } place =
      collectSourcePlaceRoots env place := by
  cases place
  all_goals conv =>
    lhs
    rw [collectSourcePlaceRoots.eq_def]
  all_goals conv =>
    rhs
    rw [collectSourcePlaceRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact collectSourceExprRoots_scopes _ _ _
    | exact collectSourcePlaceRoots_scopes _ _ _
    | exact collectSourceViewRoots_scopes _ _ _
    | exact collectSourceBoundRoots_scopes _ _ _
    | exact collectSourceArgumentRoots_scopes _ _ _
    | exact collectSourceExprListRoots_scopes _ _ _
    | exact collectSourceBlockRoots_scopes _ _ _
    | exact collectSourceStmtListRoots_scopes _ _ _
    | exact collectSourcePrintRoots_scopes _ _ _
    | exact collectSourceStmtRoots_scopes _ _ _
    | apply source_bind_congr
    | intro value
termination_by sizeOf place

theorem collectSourceViewRoots_scopes (env : PEnv) (scopes : List Nat) (view : View) :
    collectSourceViewRoots { env with scopes := scopes } view =
      collectSourceViewRoots env view := by
  cases view
  all_goals conv =>
    lhs
    rw [collectSourceViewRoots.eq_def]
  all_goals conv =>
    rhs
    rw [collectSourceViewRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact collectSourceExprRoots_scopes _ _ _
    | exact collectSourcePlaceRoots_scopes _ _ _
    | exact collectSourceViewRoots_scopes _ _ _
    | exact collectSourceBoundRoots_scopes _ _ _
    | exact collectSourceArgumentRoots_scopes _ _ _
    | exact collectSourceExprListRoots_scopes _ _ _
    | exact collectSourceBlockRoots_scopes _ _ _
    | exact collectSourceStmtListRoots_scopes _ _ _
    | exact collectSourcePrintRoots_scopes _ _ _
    | exact collectSourceStmtRoots_scopes _ _ _
    | apply source_bind_congr
    | intro value
termination_by sizeOf view

theorem collectSourceBoundRoots_scopes (env : PEnv) (scopes : List Nat) (bound : Bound) :
    collectSourceBoundRoots { env with scopes := scopes } bound =
      collectSourceBoundRoots env bound := by
  cases bound
  all_goals conv =>
    lhs
    rw [collectSourceBoundRoots.eq_def]
  all_goals conv =>
    rhs
    rw [collectSourceBoundRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact collectSourceExprRoots_scopes _ _ _
    | exact collectSourcePlaceRoots_scopes _ _ _
    | exact collectSourceViewRoots_scopes _ _ _
    | exact collectSourceBoundRoots_scopes _ _ _
    | exact collectSourceArgumentRoots_scopes _ _ _
    | exact collectSourceExprListRoots_scopes _ _ _
    | exact collectSourceBlockRoots_scopes _ _ _
    | exact collectSourceStmtListRoots_scopes _ _ _
    | exact collectSourcePrintRoots_scopes _ _ _
    | exact collectSourceStmtRoots_scopes _ _ _
    | apply source_bind_congr
    | intro value
termination_by sizeOf bound

theorem collectSourceArgumentRoots_scopes (env : PEnv) (scopes : List Nat) (arguments : List Arg) :
    collectSourceArgumentRoots { env with scopes := scopes } arguments =
      collectSourceArgumentRoots env arguments := by
  cases arguments
  all_goals try (rename_i head rest; cases head)
  all_goals conv =>
    lhs
    rw [collectSourceArgumentRoots.eq_def]
  all_goals conv =>
    rhs
    rw [collectSourceArgumentRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact collectSourceExprRoots_scopes _ _ _
    | exact collectSourcePlaceRoots_scopes _ _ _
    | exact collectSourceViewRoots_scopes _ _ _
    | exact collectSourceBoundRoots_scopes _ _ _
    | exact collectSourceArgumentRoots_scopes _ _ _
    | exact collectSourceExprListRoots_scopes _ _ _
    | exact collectSourceBlockRoots_scopes _ _ _
    | exact collectSourceStmtListRoots_scopes _ _ _
    | exact collectSourcePrintRoots_scopes _ _ _
    | exact collectSourceStmtRoots_scopes _ _ _
    | apply source_bind_congr
    | intro value
termination_by sizeOf arguments

theorem collectSourceExprListRoots_scopes (env : PEnv) (scopes : List Nat) (expressions : List Expr) :
    collectSourceExprListRoots { env with scopes := scopes } expressions =
      collectSourceExprListRoots env expressions := by
  cases expressions
  all_goals conv =>
    lhs
    rw [collectSourceExprListRoots.eq_def]
  all_goals conv =>
    rhs
    rw [collectSourceExprListRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact collectSourceExprRoots_scopes _ _ _
    | exact collectSourcePlaceRoots_scopes _ _ _
    | exact collectSourceViewRoots_scopes _ _ _
    | exact collectSourceBoundRoots_scopes _ _ _
    | exact collectSourceArgumentRoots_scopes _ _ _
    | exact collectSourceExprListRoots_scopes _ _ _
    | exact collectSourceBlockRoots_scopes _ _ _
    | exact collectSourceStmtListRoots_scopes _ _ _
    | exact collectSourcePrintRoots_scopes _ _ _
    | exact collectSourceStmtRoots_scopes _ _ _
    | apply source_bind_congr
    | intro value
termination_by sizeOf expressions

theorem collectSourceBlockRoots_scopes (env : PEnv) (scopes : List Nat) (body : Block) :
    collectSourceBlockRoots { env with scopes := scopes } body =
      collectSourceBlockRoots env body := by
  cases body
  all_goals try (rename_i scope statements value; cases value)
  all_goals conv =>
    lhs
    rw [collectSourceBlockRoots.eq_def]
  all_goals conv =>
    rhs
    rw [collectSourceBlockRoots.eq_def]
  all_goals dsimp only
  all_goals repeat' first
    | exact collectSourceStmtListRoots_scopes { env with scopes := scope :: env.scopes }
        (scope :: scopes) statements
    | exact collectSourceExprRoots_scopes { env with scopes := scope :: env.scopes }
        (scope :: scopes) _
    | rfl
    | exact collectSourceExprRoots_scopes _ _ _
    | exact collectSourcePlaceRoots_scopes _ _ _
    | exact collectSourceViewRoots_scopes _ _ _
    | exact collectSourceBoundRoots_scopes _ _ _
    | exact collectSourceArgumentRoots_scopes _ _ _
    | exact collectSourceExprListRoots_scopes _ _ _
    | exact collectSourceBlockRoots_scopes _ _ _
    | exact collectSourceStmtListRoots_scopes _ _ _
    | exact collectSourcePrintRoots_scopes _ _ _
    | exact collectSourceStmtRoots_scopes _ _ _
    | apply source_bind_congr
    | intro value
termination_by sizeOf body

theorem collectSourceStmtListRoots_scopes (env : PEnv) (scopes : List Nat) (statements : List Stmt) :
    collectSourceStmtListRoots { env with scopes := scopes } statements =
      collectSourceStmtListRoots env statements := by
  cases statements
  all_goals conv =>
    lhs
    rw [collectSourceStmtListRoots.eq_def]
  all_goals conv =>
    rhs
    rw [collectSourceStmtListRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact collectSourceExprRoots_scopes _ _ _
    | exact collectSourcePlaceRoots_scopes _ _ _
    | exact collectSourceViewRoots_scopes _ _ _
    | exact collectSourceBoundRoots_scopes _ _ _
    | exact collectSourceArgumentRoots_scopes _ _ _
    | exact collectSourceExprListRoots_scopes _ _ _
    | exact collectSourceBlockRoots_scopes _ _ _
    | exact collectSourceStmtListRoots_scopes _ _ _
    | exact collectSourcePrintRoots_scopes _ _ _
    | exact collectSourceStmtRoots_scopes _ _ _
    | apply source_bind_congr
    | intro value
termination_by sizeOf statements

theorem collectSourcePrintRoots_scopes (env : PEnv) (scopes : List Nat) (arguments : List PrintArg) :
    collectSourcePrintRoots { env with scopes := scopes } arguments =
      collectSourcePrintRoots env arguments := by
  cases arguments
  all_goals try (rename_i head rest; cases head)
  all_goals conv =>
    lhs
    rw [collectSourcePrintRoots.eq_def]
  all_goals conv =>
    rhs
    rw [collectSourcePrintRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact collectSourceExprRoots_scopes _ _ _
    | exact collectSourcePlaceRoots_scopes _ _ _
    | exact collectSourceViewRoots_scopes _ _ _
    | exact collectSourceBoundRoots_scopes _ _ _
    | exact collectSourceArgumentRoots_scopes _ _ _
    | exact collectSourceExprListRoots_scopes _ _ _
    | exact collectSourceBlockRoots_scopes _ _ _
    | exact collectSourceStmtListRoots_scopes _ _ _
    | exact collectSourcePrintRoots_scopes _ _ _
    | exact collectSourceStmtRoots_scopes _ _ _
    | apply source_bind_congr
    | intro value
termination_by sizeOf arguments

theorem collectSourceStmtRoots_scopes (env : PEnv) (scopes : List Nat) (statement : Stmt) :
    collectSourceStmtRoots { env with scopes := scopes } statement =
      collectSourceStmtRoots env statement := by
  cases statement
  case ret value origin =>
    cases value
    all_goals conv =>
      lhs
      rw [collectSourceStmtRoots.eq_def]
    all_goals conv =>
      rhs
      rw [collectSourceStmtRoots.eq_def]
    all_goals repeat' first
      | rfl
      | exact collectSourceExprRoots_scopes _ _ _
      | exact collectSourcePlaceRoots_scopes _ _ _
      | exact collectSourceViewRoots_scopes _ _ _
      | exact collectSourceBoundRoots_scopes _ _ _
      | exact collectSourceArgumentRoots_scopes _ _ _
      | exact collectSourceExprListRoots_scopes _ _ _
      | exact collectSourceBlockRoots_scopes _ _ _
      | exact collectSourceStmtListRoots_scopes _ _ _
      | exact collectSourcePrintRoots_scopes _ _ _
      | exact collectSourceStmtRoots_scopes _ _ _
      | apply source_bind_congr
      | intro value
  case resize owner count fill origin =>
    cases fill
    all_goals conv =>
      lhs
      rw [collectSourceStmtRoots.eq_def]
    all_goals conv =>
      rhs
      rw [collectSourceStmtRoots.eq_def]
    all_goals repeat' first
      | rfl
      | exact collectSourceExprRoots_scopes _ _ _
      | exact collectSourcePlaceRoots_scopes _ _ _
      | exact collectSourceViewRoots_scopes _ _ _
      | exact collectSourceBoundRoots_scopes _ _ _
      | exact collectSourceArgumentRoots_scopes _ _ _
      | exact collectSourceExprListRoots_scopes _ _ _
      | exact collectSourceBlockRoots_scopes _ _ _
      | exact collectSourceStmtListRoots_scopes _ _ _
      | exact collectSourcePrintRoots_scopes _ _ _
      | exact collectSourceStmtRoots_scopes _ _ _
      | apply source_bind_congr
      | intro value
  case ifS condition yes no origin =>
    cases no
    all_goals conv =>
      lhs
      rw [collectSourceStmtRoots.eq_def]
    all_goals conv =>
      rhs
      rw [collectSourceStmtRoots.eq_def]
    all_goals repeat' first
      | rfl
      | exact collectSourceExprRoots_scopes _ _ _
      | exact collectSourcePlaceRoots_scopes _ _ _
      | exact collectSourceViewRoots_scopes _ _ _
      | exact collectSourceBoundRoots_scopes _ _ _
      | exact collectSourceArgumentRoots_scopes _ _ _
      | exact collectSourceExprListRoots_scopes _ _ _
      | exact collectSourceBlockRoots_scopes _ _ _
      | exact collectSourceStmtListRoots_scopes _ _ _
      | exact collectSourcePrintRoots_scopes _ _ _
      | exact collectSourceStmtRoots_scopes _ _ _
      | apply source_bind_congr
      | intro value
  all_goals conv =>
    lhs
    rw [collectSourceStmtRoots.eq_def]
  all_goals conv =>
    rhs
    rw [collectSourceStmtRoots.eq_def]
  all_goals repeat' first
    | rfl
    | exact collectSourceExprRoots_scopes _ _ _
    | exact collectSourcePlaceRoots_scopes _ _ _
    | exact collectSourceViewRoots_scopes _ _ _
    | exact collectSourceBoundRoots_scopes _ _ _
    | exact collectSourceArgumentRoots_scopes _ _ _
    | exact collectSourceExprListRoots_scopes _ _ _
    | exact collectSourceBlockRoots_scopes _ _ _
    | exact collectSourceStmtListRoots_scopes _ _ _
    | exact collectSourcePrintRoots_scopes _ _ _
    | exact collectSourceStmtRoots_scopes _ _ _
    | apply source_bind_congr
    | intro value
termination_by sizeOf statement

end

theorem sourceNodeRootTable_scopes (env : PEnv) (scopes : List Nat) (root : DemandNode) :
    sourceNodeRootTable { env with scopes := scopes } root = sourceNodeRootTable env root := by
  cases root <;> simp only [sourceNodeRootTable, collectSourceExprRoots_scopes,
    collectSourcePlaceRoots_scopes, collectSourceViewRoots_scopes, collectSourceBoundRoots_scopes,
    collectSourceStmtRoots_scopes, collectSourceBlockRoots_scopes]

theorem sourceNodeRootTable_access (left right : PEnv) (root : DemandNode)
    (same : left.access = right.access) :
    sourceNodeRootTable left root = sourceNodeRootTable right root := by
  cases left with
  | mk leftMod leftImpl leftCtx leftScopes =>
      cases right with
      | mk rightMod rightImpl rightCtx rightScopes =>
          have fields : leftMod = rightMod ∧ leftImpl = rightImpl ∧ leftCtx = rightCtx := by
            simpa only [PEnv.access, AccessEnv.mk.injEq] using same
          rcases fields with ⟨rfl, rfl, rfl⟩
          exact sourceNodeRootTable_scopes ⟨leftMod, leftImpl, leftCtx, rightScopes⟩ leftScopes root

theorem RecipeMetadataProjects.access {left right : PEnv} {root : DemandNode}
    {func : Goose.GIR.Func} {state : LS} (same : left.access = right.access)
    (projects : RecipeMetadataProjects left root func state) :
    RecipeMetadataProjects right root func state := by
  intro recipe member roots row
  have projected := projects recipe member roots row
  have ctx : left.ctx = right.ctx := congrArg AccessEnv.ctx same
  have impl : left.impl = right.impl := congrArg AccessEnv.impl same
  simpa only [ctx, impl, sourceNodeRootTable_access left right root same] using projected

end Goose.Lower.Validation.SourceCanonicalRootFloors
