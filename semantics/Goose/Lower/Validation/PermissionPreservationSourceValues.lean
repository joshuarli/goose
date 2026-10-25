import Goose.Lower.Validation.PermissionPreservationGenerated
import Goose.Lower.Validation.PermissionPreservationTransfers

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lowerExpr_generated_permissionTransfer (expr : Expr)
    {env : Core.TEnv} {sourceTy targetTy : Ty} {start finish : Nat}
    (source : Core.tyExpr env expr start = .ok (sourceTy, finish))
    (compatible : sourceTy.passableTo targetTy = true)
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by assumption) :
    PermissionTransfer env.mod.profile
      (FreshWritableEvidence (lowerEnv env.mod env.vars results) before.vals.size after)
      (FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size after)
      value targetTy := by
  apply PermissionTransfer.of_source compatible
  · intro referent same demand
    subst sourceTy
    exact lowerExpr_generated_binding expr source demand run live generated
  · intro referent same container
    subst sourceTy
    exact lowerExpr_generated_contents expr source container run live generated

theorem lowerBlock_generated_permissionTransfer (body : Core.Block)
    {env : Core.TEnv} {sourceTy targetTy : Ty} {start finish : Nat}
    (source : Core.tyBlock env [] body start = .ok (sourceTy, finish))
    (compatible : sourceTy.passableTo targetTy = true)
    {results : List Ty} {before after : LS} {value : ValueId}
    (run : lowerBlock none [] true body (lowerEnv env.mod env.vars results) before = (value, after))
    (live : after.cur.isSome = true)
    (generated : GeneratedBuilderState before := by assumption) :
    PermissionTransfer env.mod.profile
      (FreshWritableEvidence (lowerEnv env.mod env.vars results) before.vals.size after)
      (FreshContentsEvidence (lowerEnv env.mod env.vars results) before.vals.size after)
      value targetTy := by
  apply PermissionTransfer.of_source compatible
  · intro referent same demand
    subst sourceTy
    exact lowerBlock_generated_binding body source demand run live generated
  · intro referent same container
    subst sourceTy
    exact lowerBlock_generated_contents body source container run live generated

#print axioms lowerExpr_generated_permissionTransfer
#print axioms lowerBlock_generated_permissionTransfer

end Goose.Lower.Validation
