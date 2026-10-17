import Goose.Lower.GeneratedBuilder
import Goose.Lower.GeneratedTargetFramesControl
import Goose.Lower.Validation.PermissionPreservationNewEmit
import Goose.Lower.Validation.PermissionInstructionControl

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

def PermissionFreeEffect : Effect → Prop
  | .enter _ | .leave _ | .print .. => True
  | _ => False

def PermissionFreeTerm : Term → Prop
  | .ret .. => False
  | _ => True

theorem FreshPermissionInstruction.freeEffect {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {state : LS} {effect : Effect} (free : PermissionFreeEffect effect) :
    FreshPermissionInstruction module func le first state (.eff effect) := by
  cases effect <;> simp only [PermissionFreeEffect] at free
  all_goals try contradiction
  all_goals
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

theorem FreshPermissionInstruction.freeTerm {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {state : LS} {term : Term} (free : PermissionFreeTerm term) :
    FreshPermissionInstruction module func le first state (.term term) := by
  cases term <;> simp only [PermissionFreeTerm] at free
  all_goals try contradiction
  all_goals
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

theorem NewPermissionInstructions.emitFreeEffect {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {effect : Effect} {result : Unit}
    (run : Goose.Lower.emitEffect effect le before = (result, after)) (free : PermissionFreeEffect effect) :
    NewPermissionInstructions module func le first before after :=
  .emitEffect run (fun _ => .freeEffect free)

theorem NewPermissionInstructions.emitFreeTerm {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {before after : LS} {term : Term} {result : Unit}
    (run : Goose.Lower.emitTerm term le before = (result, after)) (free : PermissionFreeTerm term) :
    NewPermissionInstructions module func le first before after :=
  .emitTerm run (fun _ => .freeTerm free)

theorem NewPermissionInstructions.leaveAll (scopes : List ScopeId)
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat}
    {before after : LS} {result : Unit}
    (run : Goose.Lower.leaveAll scopes le before = (result, after))
    (generated : GeneratedBuilderState before) :
    NewPermissionInstructions module func le first before after := by
  induction scopes generalizing before after with
  | nil =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact .of_blocks_eq rfl
  | cons scope rest ih =>
    obtain ⟨_, middle, emitted, remaining⟩ := bind_eq.mp run
    have middleGenerated := generated.emitEffect (.leave scope) emitted
    exact (NewPermissionInstructions.emitFreeEffect (module := module) (func := func)
      (first := first) emitted trivial).compose_framed (ih remaining middleGenerated)
      remaining (dense_leaveAll rest) (advB_leaveAll rest) (types_leaveAll rest)
      (generatedTargetFrame_leaveAll none rest) middleGenerated (by trivial)

theorem NewPermissionInstructions.leaveTo (depth : Nat)
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat}
    {before after : LS} {result : Unit}
    (run : Goose.Lower.leaveTo depth le before = (result, after))
    (generated : GeneratedBuilderState before) :
    NewPermissionInstructions module func le first before after := by
  change Goose.Lower.leaveAll (before.stack.take (before.stack.length - depth)) le before = (result, after) at run
  exact .leaveAll _ run generated

#print axioms NewPermissionInstructions.leaveAll
#print axioms NewPermissionInstructions.leaveTo

#print axioms FreshPermissionInstruction.freeEffect
#print axioms FreshPermissionInstruction.freeTerm
#print axioms NewPermissionInstructions.emitFreeEffect
#print axioms NewPermissionInstructions.emitFreeTerm

end Goose.Lower.Validation
