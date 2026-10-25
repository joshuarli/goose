import Goose.Lower.Validation.ExpressionContentsRules
import Goose.Lower.Validation.ExpressionTypingScalarOps

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem lowerExpr_read_fresh_contents {env : Core.TEnv} {place : Place} {target : Ty}
    {start finish : Nat} (source : Core.tyExpr env (.read place) start = .ok (.ref .mutable target, finish))
    {results : List Ty} {before middle after : LS} {address value : ValueId} {current : BlockId}
    (placeRun : lowerPlace place (lowerEnv env.mod env.vars results) before = (address, middle))
    (child : ∀ info childFinish, Core.tyPlace env place start = .ok (info, childFinish) →
      ∃ mu, middle.vals[address]? = some (some (.data (.ref mu info.ty))))
    (checked : middle.DenseDefinitions) (bounded : LiveBound middle) (live : middle.cur = some current)
    (run : lowerExpr (.read place) (lowerEnv env.mod env.vars results) before = (value, after)) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) middle.vals.size after value := by
  obtain ⟨info, childFinish, childSource, shape⟩ := tyExpr_read_place source
  obtain ⟨mu, typed⟩ := child info childFinish childSource
  rw [← shape] at typed
  exact lowerExpr_read_fresh_contents_of_place placeRun typed checked bounded live run

theorem lowerExpr_pop_fresh_contents {env : Core.TEnv} {owner : Place} {target : Ty}
    {origin : OriginId} {start finish : Nat}
    (source : Core.tyExpr env (.pop owner origin) start = .ok (.ref .mutable target, finish))
    {results : List Ty} {before middle after : LS} {address value : ValueId} {current : BlockId}
    (ownerRun : lowerPlace owner (lowerEnv env.mod env.vars results) before = (address, middle))
    (child : ∀ info childStart childFinish, Core.tyPlace env owner childStart = .ok (info, childFinish) →
      ∃ mu, middle.vals[address]? = some (some (.data (.ref mu info.ty))))
    (checked : middle.DenseDefinitions) (bounded : LiveBound middle) (live : middle.cur = some current)
    (run : lowerExpr (.pop owner origin) (lowerEnv env.mod env.vars results) before = (value, after)) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) middle.vals.size after value := by
  obtain ⟨info, childStart, childFinish, childSource, element⟩ := tyExpr_pop_owner source
  obtain ⟨mu, typed⟩ := child info childStart childFinish childSource
  exact lowerExpr_pop_fresh_contents_of_owner ownerRun typed element checked bounded live run

theorem lowerExpr_push_fresh_contents {env : Core.TEnv} {owner : Place} {expr : Expr} {target : Ty}
    {origin : Option OriginId} {start finish : Nat}
    (source : Core.tyExpr env (.push owner expr origin) start = .ok (.ref .mutable target, finish))
    {results : List Ty} {before ownerState middle after : LS} {address childValue value : ValueId}
    {current : BlockId}
    (ownerRun : lowerPlace owner (lowerEnv env.mod env.vars results) before = (address, ownerState))
    (childRun : lowerExpr expr (lowerEnv env.mod env.vars results) ownerState = (childValue, middle))
    (ownerChild : ∀ info childStart childFinish, Core.tyPlace env owner childStart = .ok (info, childFinish) →
      ∃ mu, middle.vals[address]? = some (some (.data (.ref mu info.ty))))
    (valueChild : ∀ ty childStart childFinish, Core.tyExpr env expr childStart = .ok (ty, childFinish) →
      middle.vals[childValue]? = some (some (.data ty)))
    (checked : middle.DenseDefinitions) (bounded : LiveBound middle) (live : middle.cur = some current)
    (run : lowerExpr (.push owner expr origin) (lowerEnv env.mod env.vars results) before = (value, after)) :
    FreshContentsEvidence (lowerEnv env.mod env.vars results) middle.vals.size after value := by
  obtain ⟨info, element, ownerStart, ownerFinish, childStart, childFinish,
    ownerSource, elementShape, childSource, shape⟩ := tyExpr_push_children source
  have elementEq : target = element := (Ty.ref.inj shape).2
  subst element
  obtain ⟨mu, ownerTyped⟩ := ownerChild info ownerStart ownerFinish ownerSource
  exact lowerExpr_push_fresh_contents_of_children ownerRun childRun ownerTyped
    (valueChild target childStart childFinish childSource) elementShape checked bounded live run

#print axioms lowerExpr_read_fresh_contents
#print axioms lowerExpr_pop_fresh_contents
#print axioms lowerExpr_push_fresh_contents

end Goose.Lower.Validation
