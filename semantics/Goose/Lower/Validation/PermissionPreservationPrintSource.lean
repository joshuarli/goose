import Goose.Lower.Validation.PermissionPreservationControlEffects
import Goose.Lower.GeneratedTargetFramesSource
import Goose.Core.Sound.Check

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem permissionInstructions_printArgs_source (args : List Core.PrintArg)
    {env : Core.TEnv} {start finish : Nat}
    (source : Core.tyPrintArgs env args start = .ok ((), finish))
    {module : GIR.Module} {func : Func} {results : List Ty} {first : Nat}
    {before after : LS} {parts : List PrintPart}
    (run : lowerPrintArgs args (lowerEnv env.mod env.vars results) before = (parts, after))
    (generated : GeneratedBuilderState before) (floor : first ≤ before.vals.size)
    (children : ∀ expr, Core.PrintArg.expr expr ∈ args → ∀ type childStart childFinish,
      Core.tyExpr env expr childStart = .ok (type, childFinish) →
      ∀ before after value, GeneratedBuilderState before → first ≤ before.vals.size →
      lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, after) →
      NewPermissionInstructions module func (lowerEnv env.mod env.vars results) first before after) :
    NewPermissionInstructions module func (lowerEnv env.mod env.vars results) first before after := by
  induction args generalizing start before after parts with
  | nil =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact .of_blocks_eq rfl
  | cons arg rest ih =>
    cases arg with
    | text text =>
      obtain ⟨_, middle, restRun, returned⟩ := bind_eq.mp run
      obtain ⟨_, rfl⟩ := pure_eq.mp returned
      exact ih source restRun generated floor (fun expr member => children expr (by simp [member]))
    | expr expr =>
      simp only [Core.tyPrintArgs] at source
      obtain ⟨type, childFinish, childSource, source⟩ := (st_bind_ok _ _ _ _).mp source
      have remainingSource : Core.tyPrintArgs env rest childFinish = .ok ((), finish) := by
        cases type <;> first
          | exact source
          | exact ((rej_ok _ _ _ _).mp source).elim
      obtain ⟨value, middle, childRun, lowered⟩ := bind_eq.mp run
      obtain ⟨_, finalState, restRun, returned⟩ := bind_eq.mp lowered
      obtain ⟨_, rfl⟩ := pure_eq.mp returned
      have middleGenerated := generated.lowerExpr expr childRun
      have nextFloor := Nat.le_trans floor (advB_lowerExpr expr _ _ _ _ childRun).vals
      have head := children expr (by simp) type _ childFinish childSource before middle value
        generated floor childRun
      have tail := ih remainingSource restRun middleGenerated nextFloor
        (fun expr member => children expr (by simp [member]))
      exact head.compose_framed tail restRun (dense_lowerPrintArgs rest) (advB_lowerPrintArgs rest)
        (types_lowerPrintArgs rest) (generatedTargetFrame_lowerPrintArgs none rest) middleGenerated (by trivial)

theorem permissionInstructions_print_source {env sourceAfter : Core.TEnv} {scope start finish : Nat}
    {args : List Core.PrintArg} {origin : OriginId}
    (source : Core.tyStmt env scope (.print args origin) start = .ok (sourceAfter, finish))
    {module : GIR.Module} {func : Func} {results : List Ty} {loop : Option LoopCtx} {first : Nat}
    {before after : LS} {result : Unit}
    (run : lowerStmt loop (.print args origin) (lowerEnv env.mod env.vars results) before = (result, after))
    (generated : GeneratedBuilderState before) (floor : first ≤ before.vals.size)
    (children : ∀ expr, Core.PrintArg.expr expr ∈ args → ∀ type childStart childFinish,
      Core.tyExpr env expr childStart = .ok (type, childFinish) →
      ∀ before after value, GeneratedBuilderState before → first ≤ before.vals.size →
      lowerExpr expr (lowerEnv env.mod env.vars results) before = (value, after) →
      NewPermissionInstructions module func (lowerEnv env.mod env.vars results) first before after) :
    NewPermissionInstructions module func (lowerEnv env.mod env.vars results) first before after := by
  simp only [Core.tyStmt] at source
  obtain ⟨_, _, _, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, _, argsSource, _⟩ := (st_bind_ok _ _ _ _).mp source
  simp only [lowerStmt] at run
  obtain ⟨parts, middle, argsRun, emitted⟩ := bind_eq.mp run
  have permitted := permissionInstructions_printArgs_source args argsSource argsRun generated floor children
  have middleGenerated := generated.lowerPrintArgs args argsRun
  exact permitted.compose_framed (.emitFreeEffect emitted trivial) emitted
    (dense_emitEffect _) (advB_emitEffect _) (types_emitEffect _) (generatedTargetFrame_emitEffect none _)
    middleGenerated (by trivial)

#print axioms permissionInstructions_printArgs_source
#print axioms permissionInstructions_print_source

end Goose.Lower.Validation
