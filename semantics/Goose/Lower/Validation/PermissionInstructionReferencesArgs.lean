import Goose.Lower.Validation.PermissionInstructionReferencesComposition

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem newPermissions_lowerArg_byRef {env : Core.TEnv} {callee : Core.Impl} {param : Param}
    {params : List Param} {requested : Mutability} {place : Place} {args : List Arg} {start finish : Nat}
    (source : Core.tyArgs env callee (param :: params) (.byRef requested place :: args) start = .ok ((), finish))
    {func : Func} {results : List Ty} {first : Nat} {before after : LS} {value : ValueId}
    (floor : first ≤ before.vals.size)
    (children : ∀ info next, Core.tyPlace env place start = .ok (info, next) →
      ∀ before middle owner, GeneratedBuilderState before →
      lowerPlace place (lowerEnv env.mod env.vars results) before = (owner, middle) →
      NewPermissionInstructions (Lower.lower env.mod) func (lowerEnv env.mod env.vars results)
        before.vals.size before middle)
    (generated : GeneratedBuilderState before)
    (run : lowerArg (.byRef requested place) (lowerEnv env.mod env.vars results) before = (value, after)) :
    NewPermissionInstructions (Lower.lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  obtain ⟨localVar, info, next, restStart, row, placeSource, reference, writable, passing, restSource⟩ :=
    source_argument_permissions source
  simp only [lowerArg] at run
  obtain ⟨owner, middle, placeRun, borrowed⟩ := bind_eq.mp run
  have head := (children info next placeSource before middle owner generated placeRun).weaken floor
  have tail := newPermissions_borrowTo_of_source_place (func := func)
    placeSource reference writable floor placeRun generated borrowed
  exact head.compose_framed tail borrowed (dense_borrowTo _ _) (advB_borrowTo _ _)
    (types_borrowTo _ _) (generatedTargetFrame_borrowTo none _ _) (generated.lowerPlace place placeRun) (by trivial)

theorem newPermissions_lowerArgs (args : List Arg)
    {env : Core.TEnv} {callee : Core.Impl} {params : List Param} {start finish : Nat}
    (sameLength : params.length = args.length)
    (source : Core.tyArgs env callee params args start = .ok ((), finish))
    {func : Func} {results : List Ty} {first : Nat} {before after : LS} {values : List ValueId}
    (floor : first ≤ before.vals.size)
    (expressions : ∀ expression, .byVal expression ∈ args → ∀ type start finish,
      Core.tyExpr env expression start = .ok (type, finish) →
      ∀ before middle value, GeneratedBuilderState before →
      lowerExpr expression (lowerEnv env.mod env.vars results) before = (value, middle) →
      NewPermissionInstructions (Lower.lower env.mod) func (lowerEnv env.mod env.vars results)
        before.vals.size before middle)
    (places : ∀ requested place, .byRef requested place ∈ args → ∀ info start finish,
      Core.tyPlace env place start = .ok (info, finish) →
      ∀ before middle value, GeneratedBuilderState before →
      lowerPlace place (lowerEnv env.mod env.vars results) before = (value, middle) →
      NewPermissionInstructions (Lower.lower env.mod) func (lowerEnv env.mod env.vars results)
        before.vals.size before middle)
    (generated : GeneratedBuilderState before)
    (run : lowerArgs args (lowerEnv env.mod env.vars results) before = (values, after)) :
    NewPermissionInstructions (Lower.lower env.mod) func (lowerEnv env.mod env.vars results) first before after := by
  cases args with
  | nil =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact .of_blocks_eq rfl
  | cons arg args =>
    cases params with
    | nil => simp at sameLength
    | cons param params =>
      simp only [lowerArgs] at run
      obtain ⟨value, middle, argRun, run⟩ := bind_eq.mp run
      obtain ⟨restValues, final, restRun, run⟩ := bind_eq.mp run
      obtain ⟨_, rfl⟩ := pure_eq.mp run
      have middleGenerated := generated.lowerArg arg argRun
      cases arg with
      | byVal expression =>
        obtain ⟨localVar, type, childStart, childFinish, restStart, row, childSource, passing, restSource⟩ :=
          tyArgs_byVal_head source
        have head := (expressions expression (by simp) type childStart childFinish childSource
          before middle value generated argRun).weaken floor
        have tail := newPermissions_lowerArgs args (by simpa using sameLength) restSource
          (Nat.le_trans floor (advB_lowerArg (.byVal expression) _ _ _ _ argRun).vals)
          (fun e member => expressions e (by simp [member]))
          (fun mu place member => places mu place (by simp [member])) middleGenerated restRun
        exact head.compose_framed tail restRun (dense_lowerArgs args) (advB_lowerArgs args)
          (types_lowerArgs args) (generatedTargetFrame_lowerArgs none args) middleGenerated (by trivial)
      | byRef requested place =>
        obtain ⟨localVar, info, childFinish, restStart, row, placeSource, reference, writable, passing, restSource⟩ :=
          source_argument_permissions source
        have head := newPermissions_lowerArg_byRef source floor
          (fun info next source => places requested place (by simp) info start next source)
          generated argRun
        have tail := newPermissions_lowerArgs args (by simpa using sameLength) restSource
          (Nat.le_trans floor (advB_lowerArg (.byRef requested place) _ _ _ _ argRun).vals)
          (fun e member => expressions e (by simp [member]))
          (fun mu p member => places mu p (by simp [member])) middleGenerated restRun
        exact head.compose_framed tail restRun (dense_lowerArgs args) (advB_lowerArgs args)
          (types_lowerArgs args) (generatedTargetFrame_lowerArgs none args) middleGenerated (by trivial)

#print axioms newPermissions_lowerArg_byRef
#print axioms newPermissions_lowerArgs

end Goose.Lower.Validation
