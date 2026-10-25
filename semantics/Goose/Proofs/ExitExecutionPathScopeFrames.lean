import Goose.Proofs.ExitExecutionPathScopes
import Goose.Proofs.ExitExecutionPathOutsideScopeReads

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

theorem ExitReached.block_escape_reads {rootFuel fuel : Nat} {config : EvalConfig}
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    {initial final : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitReached rootFuel config (ExitInvocation.block fuel environment pre channels (.mk scope statements tail)) initial)
    (escaped : (ExitInvocation.block fuel environment pre channels (.mk scope statements tail)).action config initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared before : ExecutionState),
      ExitCallSite config (ExitInvocation.block fuel environment pre channels (.mk scope statements tail)) initial child prepared ∧
      ExitReached rootFuel config child prepared ∧
      child.action config prepared = .escape address carriers before ∧
      final = releaseScopeState environment scope initial.nextScope before ∧
      final.construction.stdout = before.construction.stdout ∧
      (∀ entry, entry ∈ final.objects ↔ entry ∈ before.objects ∧
        (Goose.Proofs.Exit.runtimeScopeRoots environment scope initial.nextScope).contains entry.1 = false) ∧
      (∀ queryFuel location,
        (Goose.Proofs.Exit.runtimeScopeRoots environment scope initial.nextScope).contains location.root = false →
        OutsideReadFrame before final (Goose.Construct.readLoc queryFuel config.layout location)) := by
  obtain ⟨β, child, prepared, before, site, evaluated, released⟩ :=
    blockInvocation_escape_inv fuel config environment pre channels scope statements tail initial final address carriers escaped
  refine ⟨β, child, prepared, before, site, .call reached site, evaluated, released, ?_, ?_, ?_⟩
  · rw [released]
    rfl
  · intro entry
    rw [released]
    exact Goose.Proofs.Exit.runtime_release_scope_members environment scope initial.nextScope before entry
  · intro queryFuel location outside
    rw [released]
    exact releaseScopeState_outside_read queryFuel config.layout environment scope initial.nextScope before location outside

#print axioms ExitReached.block_escape_reads

theorem ExitReached.activationScope_escape_reads {rootFuel fuel : Nat} {config : EvalConfig}
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    {initial final : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitReached rootFuel config (ExitInvocation.activationScope fuel environment pre (.mk scope statements tail)) initial)
    (escaped : (ExitInvocation.activationScope fuel environment pre (.mk scope statements tail)).action config initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared before : ExecutionState),
      ExitCallSite config (ExitInvocation.activationScope fuel environment pre (.mk scope statements tail)) initial child prepared ∧
      ExitReached rootFuel config child prepared ∧
      child.action config prepared = .escape address carriers before ∧
      final = releaseScopeState environment scope initial.nextScope before ∧
      final.construction.stdout = before.construction.stdout ∧
      (∀ entry, entry ∈ final.objects ↔ entry ∈ before.objects ∧
        (Goose.Proofs.Exit.runtimeScopeRoots environment scope initial.nextScope).contains entry.1 = false) ∧
      (∀ queryFuel location,
        (Goose.Proofs.Exit.runtimeScopeRoots environment scope initial.nextScope).contains location.root = false →
        OutsideReadFrame before final (Goose.Construct.readLoc queryFuel config.layout location)) := by
  obtain ⟨β, child, prepared, before, site, evaluated, released⟩ :=
    activationScopeInvocation_escape_inv fuel config environment pre  scope statements tail initial final address carriers escaped
  refine ⟨β, child, prepared, before, site, .call reached site, evaluated, released, ?_, ?_, ?_⟩
  · rw [released]
    rfl
  · intro entry
    rw [released]
    exact Goose.Proofs.Exit.runtime_release_scope_members environment scope initial.nextScope before entry
  · intro queryFuel location outside
    rw [released]
    exact releaseScopeState_outside_read queryFuel config.layout environment scope initial.nextScope before location outside

#print axioms ExitReached.activationScope_escape_reads

theorem ExitReached.resultScope_escape_reads {rootFuel fuel : Nat} {config : EvalConfig}
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr)
    {initial final : ExecutionState} {address : ExitAddress} {carriers : List Carrier}
    (reached : ExitReached rootFuel config (ExitInvocation.resultScope fuel environment pre channels (.mk scope statements tail)) initial)
    (escaped : (ExitInvocation.resultScope fuel environment pre channels (.mk scope statements tail)).action config initial = .escape address carriers final) :
    ∃ (β : Type) (child : ExitInvocation β) (prepared before : ExecutionState),
      ExitCallSite config (ExitInvocation.resultScope fuel environment pre channels (.mk scope statements tail)) initial child prepared ∧
      ExitReached rootFuel config child prepared ∧
      child.action config prepared = .escape address carriers before ∧
      final = releaseScopeState environment scope initial.nextScope before ∧
      final.construction.stdout = before.construction.stdout ∧
      (∀ entry, entry ∈ final.objects ↔ entry ∈ before.objects ∧
        (Goose.Proofs.Exit.runtimeScopeRoots environment scope initial.nextScope).contains entry.1 = false) ∧
      (∀ queryFuel location,
        (Goose.Proofs.Exit.runtimeScopeRoots environment scope initial.nextScope).contains location.root = false →
        OutsideReadFrame before final (Goose.Construct.readLoc queryFuel config.layout location)) := by
  obtain ⟨β, child, prepared, before, site, evaluated, released⟩ :=
    resultScopeInvocation_escape_inv fuel config environment pre channels scope statements tail initial final address carriers escaped
  refine ⟨β, child, prepared, before, site, .call reached site, evaluated, released, ?_, ?_, ?_⟩
  · rw [released]
    rfl
  · intro entry
    rw [released]
    exact Goose.Proofs.Exit.runtime_release_scope_members environment scope initial.nextScope before entry
  · intro queryFuel location outside
    rw [released]
    exact releaseScopeState_outside_read queryFuel config.layout environment scope initial.nextScope before location outside

#print axioms ExitReached.resultScope_escape_reads

end Goose.Proofs.ExitExecution
