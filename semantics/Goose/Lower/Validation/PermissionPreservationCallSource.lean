import Goose.Lower.Validation.PermissionPreservationCalls
import Goose.Lower.Validation.PermissionPreservationNewEmit
import Goose.Lower.Validation.PermissionInstructionControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem permission_unreachable (module : GIR.Module) (func : Func) (le : LEnv)
    (first : Nat) (state : LS) :
    FreshPermissionInstruction module func le first state (.term .unreachable) := by
  constructor
  · constructor
    · intro a b c impossible; cases impossible
    · intro a b c d e impossible; cases impossible
    · intro a impossible; cases impossible
    · intro a b impossible; cases impossible
    · intro a b c impossible; cases impossible
    · intro a b c d impossible; cases impossible
    · intro a b c d e impossible; cases impossible
    · intro a b c d impossible; cases impossible
    · intro a b impossible; cases impossible
  · constructor
    · intro a b c impossible; cases impossible
    · intro a b c impossible; cases impossible

theorem lowerExpr_call_newPermissionInstructions
    {env : Core.TEnv} {context : ContextId} {args : List Arg} {origin : OriginId}
    {type : Ty} {start finish : Nat}
    (source : Core.tyExpr env (.call context args origin) start = .ok (type, finish))
    {results : List Ty} {before after : LS} {value : ValueId} {func : Func} {first : Nat}
    (run : lowerExpr (.call context args origin) (lowerEnv env.mod env.vars results) before = (value, after))
    (generated : GeneratedBuilderState before) (firstBound : first ≤ before.vals.size)
    (argsPermissions : ∀ values middle,
      lowerArgs args (lowerEnv env.mod env.vars results) before = (values, middle) →
      NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before middle) :
    NewPermissionInstructions (lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  have lowering := run
  simp only [lowerExpr] at lowering
  obtain ⟨values, middle, argsRun, lowering⟩ := bind_eq.mp lowering
  obtain ⟨callValue, emittedState, emitted, tailRun⟩ := bind_eq.mp lowering
  have middleGenerated := generated.lowerArgs args argsRun
  have emittedGenerated := middleGenerated.emitDef _ emitted
  have issued := NewPermissionInstructions.emitDef (module := lower env.mod) (func := func)
    (first := first) emitted (fun live =>
      (lowerExpr_call_emitted_permissionInstruction source argsRun emitted live generated).weaken firstBound)
  have prior := (argsPermissions values middle argsRun).compose_framed issued emitted
    (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef none _)
    middleGenerated (by trivial)
  have reader : (read : B LEnv) (lowerEnv env.mod env.vars results) emittedState =
      (lowerEnv env.mod env.vars results, emittedState) := rfl
  simp only [bind_run, reader] at tailRun
  by_cases noReturn : (lowerEnv env.mod env.vars results).mod.noReturn context = true
  · simp only [noReturn, ite_true, bind_run, pure_run] at tailRun
    have afterEq : (emitTerm .unreachable (lowerEnv env.mod env.vars results) emittedState).2 = after :=
      congrArg Prod.snd tailRun
    have termRun : emitTerm .unreachable (lowerEnv env.mod env.vars results) emittedState = ((), after) :=
      Prod.ext (Subsingleton.elim _ _) afterEq
    have terminal := NewPermissionInstructions.emitTerm (module := lower env.mod) (func := func)
      (first := first) termRun (fun _ => permission_unreachable _ _ _ _ _)
    exact prior.compose_framed terminal termRun (dense_emitTerm _) (advB_emitTerm _) (types_emitTerm _)
      (generatedTargetFrame_emitNoSuccessors none _ (by simp [Term.successors])) emittedGenerated (by trivial)
  · have isFalse : (lowerEnv env.mod env.vars results).mod.noReturn context = false := Bool.eq_false_iff.mpr noReturn
    simp only [isFalse, Bool.false_eq_true, ite_false, pure_run] at tailRun
    have same : emittedState = after := congrArg Prod.snd tailRun
    simpa only [same] using prior

#print axioms lowerExpr_call_newPermissionInstructions

end Goose.Lower.Validation
