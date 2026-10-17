import Goose.Lower.Validation.PermissionPreservationMutationInstructions
import Goose.Lower.Validation.PermissionPreservationNewEmit
import Goose.Lower.Validation.PermissionInstructionControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem lowerExpr_push_newPermissionInstructions
    {env : Core.TEnv} {place : Place} {expr : Expr} {origin : Option OriginId}
    {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.push place expr origin) start = .ok (type, finish))
    {results : List Ty} {before after : LS} {result : ValueId}
    {module : GIR.Module} {func : Func} {first : Nat}
    (run : lowerExpr (.push place expr origin) (lowerEnv env.mod env.vars results) before = (result, after))
    (generated : GeneratedBuilderState before) (firstBound : first ≤ before.vals.size)
    (placePermissions : ∀ owner ownerState,
      lowerPlace place (lowerEnv env.mod env.vars results) before = (owner, ownerState) →
      NewPermissionInstructions module func (lowerEnv env.mod env.vars results) first before ownerState)
    (childPermissions : ∀ before after value, GeneratedBuilderState before → first ≤ before.vals.size →
      lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, after) →
      NewPermissionInstructions module func (lowerEnv env.mod env.vars results) first before after) :
    NewPermissionInstructions module func (lowerEnv env.mod env.vars results) first before after := by
  simp only [lowerExpr] at run
  obtain ⟨owner, ownerState, ownerRun, run⟩ := bind_eq.mp run
  obtain ⟨value, middle, childRun, emitted⟩ := bind_eq.mp run
  have ownerGenerated := generated.lowerPlace place ownerRun
  have middleGenerated := ownerGenerated.lowerExpr expr childRun
  have ownerBound := Nat.le_trans firstBound (advB_lowerPlace place _ _ _ _ ownerRun).vals
  have children := (placePermissions owner ownerState ownerRun).compose_framed
    (childPermissions ownerState middle value ownerGenerated ownerBound childRun)
    childRun (dense_lowerExpr expr) (advB_lowerExpr expr) (types_lowerExpr expr)
    (generatedTargetFrame_lowerExpr none expr) ownerGenerated (by trivial)
  have issued := NewPermissionInstructions.emitDef (module := module) (func := func)
    (first := first) emitted (fun live =>
      (lowerExpr_push_emitted_permissionInstruction source ownerRun childRun emitted live generated).weaken firstBound)
  exact children.compose_framed issued emitted (dense_emitDef _) (advB_emitDef _) (types_emitDef _)
    (generatedTargetFrame_emitDef none _) middleGenerated (by trivial)

theorem lowerExpr_pop_newPermissionInstructions
    {env : Core.TEnv} {place : Place} {origin : OriginId} {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.pop place origin) start = .ok (type, finish))
    {results : List Ty} {before after : LS} {result : ValueId}
    {module : GIR.Module} {func : Func} {first : Nat}
    (run : lowerExpr (.pop place origin) (lowerEnv env.mod env.vars results) before = (result, after))
    (generated : GeneratedBuilderState before) (firstBound : first ≤ before.vals.size)
    (placePermissions : ∀ owner ownerState,
      lowerPlace place (lowerEnv env.mod env.vars results) before = (owner, ownerState) →
      NewPermissionInstructions module func (lowerEnv env.mod env.vars results) first before ownerState) :
    NewPermissionInstructions module func (lowerEnv env.mod env.vars results) first before after := by
  simp only [lowerExpr] at run
  obtain ⟨owner, middle, ownerRun, emitted⟩ := bind_eq.mp run
  have middleGenerated := generated.lowerPlace place ownerRun
  have issued := NewPermissionInstructions.emitDef (module := module) (func := func)
    (first := first) emitted (fun live =>
      (lowerExpr_pop_emitted_permissionInstruction source ownerRun emitted live generated).weaken firstBound)
  exact (placePermissions owner middle ownerRun).compose_framed issued emitted
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
    middleGenerated (by trivial)

#print axioms lowerExpr_push_newPermissionInstructions
#print axioms lowerExpr_pop_newPermissionInstructions

end Goose.Lower.Validation
