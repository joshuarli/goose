import Goose.Lower.Validation.ReplacementSourceSitesActions
import Goose.Lower.Validation.ExpressionTypingScalarOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {root : DemandNode} {targets : List BlockId}

def ReplacementSitesPlaceChild (env : Core.TEnv) (results : List Ty) (place : Place) : Prop :=
  ∀ {info : PlaceInfo} {start finish : Nat}, Core.tyPlace env place start = .ok (info, finish) →
    ∀ {before : LS}, GeneratedBuilderState before →
      ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerPlace place)

def ReplacementSitesExprChild (env : Core.TEnv) (results : List Ty) (expr : Expr) : Prop :=
  ∀ {type : Ty} {start finish : Nat}, Core.tyExpr env expr start = .ok (type, finish) →
    ∀ {before : LS}, GeneratedBuilderState before →
      ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerExpr expr)

def ReplacementSitesViewChild (env : Core.TEnv) (results : List Ty) (view : View) : Prop :=
  ∀ {element : Ty} {writable : Bool} {start finish : Nat},
    Core.tyView env view start = .ok ((element, writable), finish) →
    ∀ {before : LS}, GeneratedBuilderState before →
      ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerView view)

theorem replacementSites_read_source {env : Core.TEnv} {results : List Ty}
    {place : Place} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.read place) start = .ok (type, finish))
    (child : ReplacementSitesPlaceChild (root := root) (targets := targets) env results place) {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerExpr (.read place)) := by
  simp only [Core.tyExpr] at source
  obtain ⟨info, next, placeSource, rest⟩ := (st_bind_ok _ _ _ _).mp source
  change ReplacementSitesAt (root := root) (targets := targets) _ _ (lowerPlace place >>= fun address => emitDef (.load address))
  apply (child placeSource generated).bind
  exact ReplacementSitesAt.emitDef _ (by intros; trivial)

theorem replacementSites_pop_source {env : Core.TEnv} {results : List Ty}
    {owner : Place} {origin : OriginId} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.pop owner origin) start = .ok (type, finish))
    (child : ReplacementSitesPlaceChild (root := root) (targets := targets) env results owner) {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerExpr (.pop owner origin)) := by
  obtain ⟨info, ownerStart, ownerFinish, placeSource, element⟩ := tyExpr_pop_owner source
  change ReplacementSitesAt (root := root) (targets := targets) _ _ (lowerPlace owner >>= fun address => emitDef (.pop address (some origin)))
  apply (child placeSource generated).bind
  exact ReplacementSitesAt.emitDef _ (by intros; trivial)

theorem replacementSites_push_source {env : Core.TEnv} {results : List Ty}
    {owner : Place} {expr : Expr} {origin : Option OriginId}
    {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.push owner expr origin) start = .ok (type, finish))
    (placeChild : ReplacementSitesPlaceChild (root := root) (targets := targets) env results owner) (exprChild : ReplacementSitesExprChild (root := root) (targets := targets) env results expr)
    {before : LS} (generated : GeneratedBuilderState before) :
    ReplacementSitesAt (root := root) (targets := targets) (lowerEnv env.mod env.vars results) before (lowerExpr (.push owner expr origin)) := by
  obtain ⟨info, element, ownerStart, ownerFinish, childStart, childFinish,
    ownerSource, shape, childSource, _⟩ := tyExpr_push_children source
  let ownerValue := lowerPlace owner (lowerEnv env.mod env.vars results) before
  have ownerGenerated := generated.lowerPlace owner (show lowerPlace owner _ before = ownerValue from rfl)
  change ReplacementSitesAt (root := root) (targets := targets) _ _ (lowerPlace owner >>= fun address => do
    let value ← lowerExpr expr
    emitDef (.push address value origin))
  apply (placeChild ownerSource generated).bind
  apply (exprChild childSource ownerGenerated).bind
  exact ReplacementSitesAt.emitDef _ (by intros; trivial)

#print axioms replacementSites_read_source
#print axioms replacementSites_push_source
#print axioms replacementSites_pop_source

end Goose.Lower.Validation
