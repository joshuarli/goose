import Goose.Lower.Validation.PermissionPreservationGenerated
import Goose.Lower.Validation.ExpressionTypingGeneratedChecks
import Goose.Lower.Validation.PermissionPreservationChecks

namespace Goose.Lower.Validation.PermissionGeneratedChecks

open Goose.Core Goose.GIR
open ExpressionTypingChecks ExpressionTypingGeneratedChecks

theorem compound_owner_binding {before after : LS} {value : ValueId}
    (generated : GeneratedBuilderState before)
    (run : lowerPlace compoundOwner (lowerEnv module env.vars []) before = (value, after))
    (live : after.cur.isSome = true) :
    FreshWritableEvidence (lowerEnv module env.vars []) before.vals.size after value := by
  exact lowerPlace_generated_binding compoundOwner compound_owner_source rfl (by trivial) run live

theorem compound_owner_element_binding {before after : LS} {value : ValueId}
    (generated : GeneratedBuilderState before)
    (run : lowerPlace compoundOwnerElement (lowerEnv module env.vars []) before = (value, after))
    (live : after.cur.isSome = true) :
    FreshWritableEvidence (lowerEnv module env.vars []) before.vals.size after value := by
  exact lowerPlace_generated_binding compoundOwnerElement compound_owner_element_source rfl (by trivial) run live

def ownerModule : Core.Module := PermissionChecks.ownerBorrowReplacement (.grow (.int .i64)) true

def ownerEnv : Core.TEnv :=
  { mod := ownerModule, impl := ownerModule.impls[0]?, vars := #[⟨"owner", .grow (.int .i64), .immutable, 0, 0⟩],
    visible := [0], loops := 0, inExpr := false, scopes := [0], globalLimit := 0, initializing := none }

def ownerReference : Expr :=
  .ifE (.bool true) (.mk 1 [] (some (.ref .mutable (.var 0))))
    (.mk 2 [] (some (.ref .mutable (.var 0))))

theorem owner_reference_source : Core.tyExpr ownerEnv ownerReference 2 =
    .ok (.ref .mutable (.grow (.int .i64)), 2) := by rfl

theorem immutable_owner_borrow_binding {before after : LS} {value : ValueId}
    (generated : GeneratedBuilderState before)
    (run : lowerExpr ownerReference (lowerEnv ownerModule ownerEnv.vars []) before = (value, after))
    (live : after.cur.isSome = true) :
    FreshWritableEvidence (lowerEnv ownerModule ownerEnv.vars []) before.vals.size after value := by
  exact lowerExpr_generated_binding ownerReference owner_reference_source (by rfl) run live

def sliceEnv : Core.TEnv :=
  { mod := module, impl := none,
    vars := #[⟨"reference", .ref .mutable (.slice .mutable (.int .i64)), .immutable, 0, 0⟩],
    visible := [0], loops := 0, inExpr := false, scopes := [0], globalLimit := 0, initializing := none }

def slicePlace : Place := .deref (.read (.var 0))

theorem slice_place_source : Core.tyPlace sliceEnv slicePlace 2 =
    .ok (⟨.slice .mutable (.int .i64), true, true⟩, 2) := by rfl

theorem slice_reference_binding {before after : LS} {value : ValueId}
    (generated : GeneratedBuilderState before)
    (run : lowerPlace slicePlace (lowerEnv module sliceEnv.vars []) before = (value, after))
    (live : after.cur.isSome = true) :
    FreshWritableEvidence (lowerEnv module sliceEnv.vars []) before.vals.size after value := by
  exact lowerPlace_generated_binding slicePlace slice_place_source rfl (by trivial) run live

#guard let le := lowerEnv module sliceEnv.vars []
  let (value, after) := lowerPlace slicePlace le initial
  (permissionsAt ((permissionFunc le after).permissionsFromTables
    (le.globals.map (·.2)) le.mod.structs after.vals) value).1

#print axioms compound_owner_binding
#print axioms immutable_owner_borrow_binding
#print axioms slice_reference_binding

end Goose.Lower.Validation.PermissionGeneratedChecks
