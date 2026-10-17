import Goose.Lower.Validation.PermissionPreservationArguments
import Goose.Lower.Validation.PermissionPreservationGeneratedChecks

namespace Goose.Lower.Validation.PermissionArgumentsChecks

open Goose.Core Goose.GIR
open PermissionGeneratedChecks ExpressionTypingChecks

def callee : Core.Impl :=
  { name := "callee", params := #[⟨0, .byRef⟩], results := #[],
    vars := #[⟨"p", .ref .mutable (.grow (.int .i64)), .immutable, 0, 0⟩],
    body := .mk 0 [] none, summary := .unknown }

def byRef : List Arg := [.byRef .mutable (.var 0)]

theorem byRef_source : Core.tyArgs ownerEnv callee callee.params.toList byRef 2 = .ok ((), 2) := by rfl

theorem immutable_owner_argument_permissions {before after : LS} {values : List ValueId}
    (generated : GeneratedBuilderState before)
    (run : lowerArgs byRef (lowerEnv ownerModule ownerEnv.vars []) before = (values, after))
    (live : after.cur.isSome = true) :
    ∀ entry ∈ [Ty.ref .mutable (.grow (.int .i64))].zip values,
      PermissionTransfer .shrink
        (FreshWritableEvidence (lowerEnv ownerModule ownerEnv.vars []) before.vals.size after)
        (FreshContentsEvidence (lowerEnv ownerModule ownerEnv.vars []) before.vals.size after) entry.2 entry.1 := by
  exact lowerArgs_generated_permissions byRef rfl byRef_source run live generated

def byValueCallee : Core.Impl := { callee with params := #[⟨0, .byValue⟩] }

def byValue : List Arg := [.byVal (.ref .mutable (.var 0))]

theorem byValue_source : Core.tyArgs ownerEnv byValueCallee byValueCallee.params.toList byValue 2 =
    .ok ((), 2) := by rfl

theorem immutable_owner_value_argument_permissions {before after : LS} {values : List ValueId}
    (generated : GeneratedBuilderState before)
    (run : lowerArgs byValue (lowerEnv ownerModule ownerEnv.vars []) before = (values, after))
    (live : after.cur.isSome = true) :
    ∀ entry ∈ [Ty.ref .mutable (.grow (.int .i64))].zip values,
      PermissionTransfer .shrink
        (FreshWritableEvidence (lowerEnv ownerModule ownerEnv.vars []) before.vals.size after)
        (FreshContentsEvidence (lowerEnv ownerModule ownerEnv.vars []) before.vals.size after) entry.2 entry.1 := by
  exact lowerArgs_generated_permissions byValue rfl byValue_source run live generated

#guard let le := lowerEnv ownerModule ownerEnv.vars []
  let (values, after) := lowerArgs byRef le initial
  permissionsAt ((permissionFunc le after).permissionsFromTables
    (le.globals.map (·.2)) le.mod.structs after.vals) (values.headD 0) == (true, true)

#guard let le := lowerEnv { ownerModule with profile := .pilot } ownerEnv.vars []
  let (values, after) := lowerArgs byRef le initial
  permissionsAt ((permissionFunc le after).permissionsFromTables
    (le.globals.map (·.2)) le.mod.structs after.vals) (values.headD 0) == (false, true)

#print axioms immutable_owner_argument_permissions
#print axioms immutable_owner_value_argument_permissions

end Goose.Lower.Validation.PermissionArgumentsChecks
