import Goose.Lower.Validation.PermissionPreservationControlEffects
import Goose.Lower.Validation.PermissionInstructionReferencesOps

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem permissionInstructions_break {module : GIR.Module} {func : Func} {le : LEnv}
    {loop : Option LoopCtx} {first : Nat} {origin : OriginId} {before after : LS} {result : Unit}
    (run : lowerStmt loop (.brk origin) le before = (result, after))
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before) :
    NewPermissionInstructions module func le first before after := by
  cases loop with
  | none =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact .of_blocks_eq rfl
  | some context =>
    simp only [lowerStmt] at run
    obtain ⟨_, middle, leaveRun, branchRun⟩ := bind_eq.mp run
    have middleGenerated := generated.leaveTo context.depth leaveRun
    have middleFrames := frames.mono (advB_leaveTo context.depth le before _ middle leaveRun).ext
    apply (NewPermissionInstructions.leaveTo (module := module) (func := func) (first := first) context.depth leaveRun generated).compose_framed
      (NewPermissionInstructions.branch branchRun) branchRun (dense_emitTerm _) (advB_emitTerm _)
      (types_emitTerm _) ?_ middleGenerated middleFrames
    apply generatedTargetFrame_emitTerm (some context)
    intro base target successor targetBound
    simp only [Term.successors, List.mem_singleton] at successor
    subst target
    exact Or.inl rfl

theorem permissionInstructions_continue {module : GIR.Module} {func : Func} {le : LEnv}
    {loop : Option LoopCtx} {first : Nat} {origin : OriginId} {before after : LS} {result : Unit}
    (run : lowerStmt loop (.cont origin) le before = (result, after))
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before) :
    NewPermissionInstructions module func le first before after := by
  cases loop with
  | none =>
    obtain ⟨_, rfl⟩ := pure_eq.mp run
    exact .of_blocks_eq rfl
  | some context =>
    cases continuation : context.cont with
    | jump header =>
      simp only [lowerStmt, continuation] at run
      obtain ⟨_, middle, leaveRun, branchRun⟩ := bind_eq.mp run
      have middleGenerated := generated.leaveTo context.depth leaveRun
      have middleFrames := frames.mono (advB_leaveTo context.depth le before _ middle leaveRun).ext
      apply (NewPermissionInstructions.leaveTo (module := module) (func := func) (first := first) context.depth leaveRun generated).compose_framed
        (NewPermissionInstructions.branch branchRun) branchRun (dense_emitTerm _) (advB_emitTerm _)
        (types_emitTerm _) ?_ middleGenerated middleFrames
      apply generatedTargetFrame_emitTerm (some context)
      intro base target successor targetBound
      simp only [Term.successors, List.mem_singleton] at successor
      subst target
      simp only [LoopBuilderFrameTarget, continuation]
      exact Or.inr True.intro
    | next header type counter =>
      simp only [lowerStmt, continuation] at run
      obtain ⟨_, middle, leaveRun, run⟩ := bind_eq.mp run
      obtain ⟨value, incremented, incrementRun, branchRun⟩ := bind_eq.mp run
      have middleGenerated := generated.leaveTo context.depth leaveRun
      have middleFrames := frames.mono (advB_leaveTo context.depth le before _ middle leaveRun).ext
      have incrementedGenerated := middleGenerated.emitDef (.next type counter) incrementRun
      have incrementedFrames := middleFrames.mono (advB_emitDef _ le middle _ incremented incrementRun).ext
      have permitted := (NewPermissionInstructions.leaveTo (module := module) (func := func) (first := first) context.depth leaveRun generated).compose_framed
        (newPermissions_free_emitDef (by trivial) incrementRun) incrementRun
        (dense_emitDef _) (advB_emitDef _) (types_emitDef _) (generatedTargetFrame_emitDef (some context) _)
        middleGenerated middleFrames
      apply permitted.compose_framed (NewPermissionInstructions.branch branchRun) branchRun
        (dense_emitTerm _) (advB_emitTerm _) (types_emitTerm _) ?_ incrementedGenerated incrementedFrames
      apply generatedTargetFrame_emitTerm (some context)
      intro base target successor targetBound
      simp only [Term.successors, List.mem_singleton] at successor
      subst target
      simp only [LoopBuilderFrameTarget, continuation]
      exact Or.inr True.intro

#print axioms permissionInstructions_break
#print axioms permissionInstructions_continue

end Goose.Lower.Validation
