import Goose.Lower.Validation.PermissionInstructionReferencesArgs
import Goose.Lower.Validation.PermissionPreservationGeneratedChecks

namespace Goose.Lower.Validation.PermissionInstructionReferencesChecks

open Goose.Core Goose.GIR
open PermissionGeneratedChecks

def reference : Expr := .ref .mutable (.var 0)

theorem reference_source : Core.tyExpr ownerEnv reference 2 =
    .ok (.ref .mutable (.grow (.int .i64)), 2) := by rfl

theorem immutable_owner_reference_new {func : Func} {before after : LS} {value : ValueId}
    (generated : GeneratedBuilderState before)
    (run : lowerExpr reference (lowerEnv ownerModule ownerEnv.vars []) before = (value, after)) :
    NewPermissionInstructions (Lower.lower ownerModule) func (lowerEnv ownerModule ownerEnv.vars [])
      before.vals.size before after := by
  apply newPermissions_lowerExpr_ref reference_source (Nat.le_refl _) _ generated run
  intro info next source before middle owner generated placeRun
  exact newPermissions_lowerPlace_var placeRun

def callee : Core.Impl :=
  { name := "arguments", params := #[⟨0, .byValue⟩, ⟨1, .byRef⟩], results := #[],
    vars := #[⟨"value", .int .i64, .immutable, 0, 0⟩,
      ⟨"owner", .ref .mutable (.grow (.int .i64)), .immutable, 0, 0⟩],
    body := .mk 1 [] none, summary := .unknown }

def arguments : List Arg := [.byVal (.lit .i64 7), .byRef .mutable (.var 0)]

theorem arguments_source : Core.tyArgs ownerEnv callee callee.params.toList arguments 2 = .ok ((), 2) := by rfl

theorem mixed_arguments_new {func : Func} {before after : LS} {values : List ValueId}
    (generated : GeneratedBuilderState before)
    (run : lowerArgs arguments (lowerEnv ownerModule ownerEnv.vars []) before = (values, after)) :
    NewPermissionInstructions (Lower.lower ownerModule) func (lowerEnv ownerModule ownerEnv.vars [])
      before.vals.size before after := by
  apply newPermissions_lowerArgs arguments (by rfl) arguments_source (Nat.le_refl _) _ _ generated run
  · intro expression member type start finish source before middle value generated exprRun
    simp [arguments] at member
    subst expression
    exact newPermissions_free_emitDef (by trivial) exprRun
  · intro requested place member info start finish source before middle value generated placeRun
    simp [arguments] at member
    obtain ⟨rfl, rfl⟩ := member
    exact newPermissions_lowerPlace_var placeRun

def borrowsOwner (profile : ArtifactProfile) (requested : Mutability) (referent : Ty) : Bool :=
  let sourceModule := { ownerModule with profile := profile }
  let variables := #[LocalVar.mk "owner" referent .immutable 0 0]
  let (_, after) := lowerExpr (.ref requested (.var 0)) (lowerEnv sourceModule variables [])
    ExpressionTypingChecks.initial
  after.insts.any fun instruction => match instruction with
    | .def _ (.ownerBorrow _) => true
    | _ => false

#guard borrowsOwner .shrink .mutable (.grow (.int .i64))
#guard borrowsOwner .shrink .mutable (.growshrink (.int .i64))
#guard !borrowsOwner .pilot .mutable (.grow (.int .i64))
#guard !borrowsOwner .shrink .readOnly (.grow (.int .i64))
#guard !borrowsOwner .shrink .mutable (.arr (.int .i64) 3)

#print axioms immutable_owner_reference_new
#print axioms mixed_arguments_new

end Goose.Lower.Validation.PermissionInstructionReferencesChecks
