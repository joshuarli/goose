import Goose.Lower.Validation.PermissionInstructionControl
import Goose.Lower.Validation.PermissionPreservationInitializers
import Goose.Lower.Validation.PermissionPreservationControlEffects

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

private theorem generatedBuilderState_changeStack {state : LS}
    (generated : GeneratedBuilderState state) (stack : List ScopeId) :
    GeneratedBuilderState { state with stack := stack } := by
  cases state
  refine ⟨?_, ?_, ?_⟩
  · simpa [LS.DenseDefinitions, LS.defs] using generated.dense
  · simpa [LiveBound] using generated.live
  · simpa [TargetsBounded] using generated.targets

private theorem PermissionTransfer.stack {profile : ArtifactProfile} {le : LEnv}
    {first : Nat} {before : LS} {value : ValueId} {descriptor : Slot}
    (transfer : PermissionTransfer profile (FreshWritableEvidence le first before)
      (FreshContentsEvidence le first before) value descriptor.ty) (scope : ScopeId) :
    PermissionTransfer profile (FreshWritableEvidence le first { before with stack := scope :: before.stack })
      (FreshContentsEvidence le first { before with stack := scope :: before.stack }) value descriptor.ty := by
  apply transfer.mono
  · intro candidate evidence
    simpa [FreshWritableEvidence, permissionFunc] using evidence
  · intro candidate evidence
    simpa [FreshContentsEvidence, permissionFunc] using evidence

private def lowerBlockScopeBody (loop : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (want : Bool)
    (scope : ScopeId) (statements : List Stmt) (value : Option Expr) : B ValueId := do
  initSlots pre
  lowerStmts loop statements
  let result ← lowerBlockValue want value
  emitEffect (.leave scope)
  pure result

private theorem dense_lowerBlockScopeBody (loop : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (want : Bool)
    (scope : ScopeId) (statements : List Stmt) (value : Option Expr) :
    DenseRun (lowerBlockScopeBody loop pre want scope statements value) := by
  unfold lowerBlockScopeBody
  exact DenseRun.bind (dense_initSlots pre) fun _ =>
    DenseRun.bind (dense_lowerStmts loop statements) fun _ =>
    DenseRun.bind (dense_lowerBlockValue want value) fun _ =>
    DenseRun.bind (dense_emitEffect (.leave scope)) fun _ =>
    DenseRun.pure _

private theorem advB_lowerBlockScopeBody (loop : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (want : Bool)
    (scope : ScopeId) (statements : List Stmt) (value : Option Expr) :
    AdvB (lowerBlockScopeBody loop pre want scope statements value) := by
  unfold lowerBlockScopeBody
  exact AdvB.bind (advB_initSlots pre) fun _ =>
    AdvB.bind (advB_lowerStmts loop statements) fun _ =>
    AdvB.bind (advB_lowerBlockValue want value) fun _ =>
    AdvB.bind (advB_emitEffect (.leave scope)) fun _ =>
    AdvB.pure _

private theorem types_lowerBlockScopeBody (loop : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (want : Bool)
    (scope : ScopeId) (statements : List Stmt) (value : Option Expr) :
    TypeRun (lowerBlockScopeBody loop pre want scope statements value) := by
  unfold lowerBlockScopeBody
  exact TypeRun.bind (types_initSlots pre) fun _ =>
    TypeRun.bind (types_lowerStmts loop statements) fun _ =>
    TypeRun.bind (types_lowerBlockValue want value) fun _ =>
    TypeRun.bind (types_emitEffect (.leave scope)) fun _ =>
    TypeRun.pure _

private theorem generatedTargetFrame_lowerBlockScopeBody (loop : Option LoopCtx)
    (pre : List (SlotId × ValueId × OriginId)) (want : Bool)
    (scope : ScopeId) (statements : List Stmt) (value : Option Expr) :
    GeneratedTargetFrameRun loop (lowerBlockScopeBody loop pre want scope statements value) := by
  unfold lowerBlockScopeBody
  exact GeneratedTargetFrameRun.bind (generatedTargetFrame_initSlots loop pre) fun _ =>
    GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerStmts loop statements) fun _ =>
    GeneratedTargetFrameRun.bind (generatedTargetFrame_lowerBlockValue loop want value) fun _ =>
    GeneratedTargetFrameRun.bind (generatedTargetFrame_emitEffect loop (.leave scope)) fun _ =>
    generatedTargetFrame_pure loop _

private theorem FreshPermissionInstruction.of_blocks_vals_eq {module : GIR.Module}
    {func : Func} {le : LEnv} {first : Nat} {before after : LS} {instruction : Inst}
    (permitted : FreshPermissionInstruction module func le first before instruction)
    (blocks : after.blocks = before.blocks) (values : after.vals = before.vals) :
    FreshPermissionInstruction module func le first after instruction := by
  have functions : permissionFunc le after = permissionFunc le before := by
    simp [permissionFunc, blocks]
  have writable : FreshWritableEvidence le first after = FreshWritableEvidence le first before := by
    unfold FreshWritableEvidence
    rw [functions, values]
  have contents : FreshContentsEvidence le first after = FreshContentsEvidence le first before := by
    unfold FreshContentsEvidence
    rw [functions, values]
  simpa [FreshPermissionInstruction, functions, values, writable, contents] using permitted

private theorem NewPermissionInstructions.of_blocks_vals_eq {module : GIR.Module}
    {func : Func} {le : LEnv} {first : Nat} {source before after : LS}
    (permitted : NewPermissionInstructions module func le first source before)
    (blocks : after.blocks = before.blocks) (values : after.vals = before.vals) :
    NewPermissionInstructions module func le first source after := by
  intro instruction member
  have beforeMember : instruction ∈ before.insts := by
    simpa [LS.insts, blocks] using member
  rcases permitted instruction beforeMember with old | fresh
  · exact Or.inl (by simpa [LS.insts, blocks] using old)
  · exact Or.inr (fresh.of_blocks_vals_eq blocks values)

private theorem NewPermissionInstructions.blockScopeBody
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat}
    {loop : Option LoopCtx} {pre : List (SlotId × ValueId × OriginId)} {want : Bool}
    {scope : ScopeId} {statements : List Stmt} {value : Option Expr}
    {before after : LS} {result : ValueId}
    (run : lowerBlockScopeBody loop pre want scope statements value le before = (result, after))
    (transfer : ∀ entry ∈ pre, ∀ descriptor,
      func.slots[entry.1]? = some descriptor →
      PermissionTransfer module.profile (FreshWritableEvidence le first before)
        (FreshContentsEvidence le first before) entry.2.1 descriptor.ty)
    (firstBound : first ≤ before.vals.size)
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before)
    (statementsNew : ∀ {input output}, lowerStmts loop statements le input = ((), output) →
      GeneratedBuilderState input → LoopBuilderFrames loop input → first ≤ input.vals.size →
      NewPermissionInstructions module func le first input output)
    (valueNew : ∀ {input output id}, lowerBlockValue want value le input = (id, output) →
      GeneratedBuilderState input → LoopBuilderFrames loop input → first ≤ input.vals.size →
      NewPermissionInstructions module func le first input output) :
    NewPermissionInstructions module func le first before after := by
  unfold lowerBlockScopeBody at run
  simp only [bind_eq] at run
  obtain ⟨_, initialized, initRun, _, stated, statementsRun, id, valued, valueRun,
    _, left, leaveRun, finish⟩ := run
  rw [pure_run] at finish
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj finish
  have initializedNew := initSlots_newPermissionInstructions pre initRun generated transfer
  have initializedGenerated := generated.initSlots pre initRun
  have initializedAdvance := advB_initSlots pre _ _ _ _ initRun
  have initializedFrames := frames.mono initializedAdvance.ext
  have initializedFloor := Nat.le_trans firstBound initializedAdvance.vals
  have statementsNew' := statementsNew statementsRun initializedGenerated initializedFrames initializedFloor
  have statementsGenerated := initializedGenerated.lowerStmts loop statements
    (initializedFrames.toTargets) statementsRun
  have statementsFrames := initializedFrames.mono
    (advB_lowerStmts loop statements _ _ _ _ statementsRun).ext
  have firstComposition := NewPermissionInstructions.compose_framed initializedNew statementsNew'
    statementsRun (dense_lowerStmts loop statements) (advB_lowerStmts loop statements)
    (types_lowerStmts loop statements) (generatedTargetFrame_lowerStmts loop statements)
    initializedGenerated initializedFrames
  have statementsAdvance := advB_lowerStmts loop statements _ _ _ _ statementsRun
  have statementsFloor := Nat.le_trans initializedFloor statementsAdvance.vals
  have valueNew' := valueNew valueRun statementsGenerated statementsFrames statementsFloor
  have valueGenerated := statementsGenerated.lowerBlockValue want value valueRun
  have valueFrames := statementsFrames.mono
    (advB_lowerBlockValue want value _ _ _ _ valueRun).ext
  have secondComposition := NewPermissionInstructions.compose_framed firstComposition valueNew'
    valueRun (dense_lowerBlockValue want value) (advB_lowerBlockValue want value)
    (types_lowerBlockValue want value) (generatedTargetFrame_lowerBlockValue loop want value)
    statementsGenerated statementsFrames
  have leaveNew := NewPermissionInstructions.emitFreeEffect (module := module) (func := func)
    (first := first) leaveRun (by trivial)
  have thirdComposition := NewPermissionInstructions.compose_framed secondComposition leaveNew
    leaveRun (dense_emitEffect (.leave scope)) (advB_emitEffect (.leave scope))
    (types_emitEffect (.leave scope)) (generatedTargetFrame_emitEffect loop (.leave scope))
    valueGenerated valueFrames
  exact thirdComposition

theorem lowerBlock_newPermissionInstructions
    {module : GIR.Module} {func : Func} {le : LEnv} {first : Nat}
    {loop : Option LoopCtx} {pre : List (SlotId × ValueId × OriginId)} {want : Bool}
    {scope : ScopeId} {statements : List Stmt} {value : Option Expr}
    {before after : LS} {result : ValueId}
    (run : lowerBlock loop pre want (.mk scope statements value) le before = (result, after))
    (firstBound : first ≤ before.vals.size)
    (generated : GeneratedBuilderState before) (frames : LoopBuilderFrames loop before)
    (preTransfer : ∀ entry ∈ pre, ∀ descriptor,
      func.slots[entry.1]? = some descriptor →
      PermissionTransfer module.profile (FreshWritableEvidence le first before)
        (FreshContentsEvidence le first before) entry.2.1 descriptor.ty)
    (statementsNew : ∀ {input output}, lowerStmts loop statements le input = ((), output) →
      GeneratedBuilderState input → LoopBuilderFrames loop input → first ≤ input.vals.size →
      NewPermissionInstructions module func le first input output)
    (valueNew : ∀ {input output id}, lowerBlockValue want value le input = (id, output) →
      GeneratedBuilderState input → LoopBuilderFrames loop input → first ≤ input.vals.size →
      NewPermissionInstructions module func le first input output) :
    NewPermissionInstructions module func le first before after := by
  change (emitEffect (.enter scope) >>= fun _ =>
    inScope scope (lowerBlockScopeBody loop pre want scope statements value)) le before =
    (result, after) at run
  obtain ⟨_, entered, enterRun, scopeRun⟩ := bind_eq.mp run
  have enterNew := NewPermissionInstructions.emitFreeEffect (module := module) (func := func)
    (first := first) enterRun (by trivial)
  have enteredGenerated := generated.emitEffect (.enter scope) enterRun
  have enteredFloor := Nat.le_trans firstBound (advB_emitEffect (.enter scope) _ _ _ _ enterRun).vals
  have enteredFrames := frames.mono (advB_emitEffect (.enter scope) _ _ _ _ enterRun).ext
  have enteredTransfer : ∀ entry ∈ pre, ∀ descriptor,
      func.slots[entry.1]? = some descriptor →
      PermissionTransfer module.profile (FreshWritableEvidence le first entered)
        (FreshContentsEvidence le first entered) entry.2.1 descriptor.ty := by
    intro entry member descriptor row
    exact (preTransfer entry member descriptor row).mono
      (fun _ evidence => evidence.of_framed_run enterRun (dense_emitEffect (.enter scope))
        (advB_emitEffect (.enter scope)) (types_emitEffect (.enter scope))
        (generatedTargetFrame_emitEffect loop (.enter scope)) generated.dense generated.live frames)
      (fun _ evidence => evidence.of_framed_run enterRun (dense_emitEffect (.enter scope))
        (advB_emitEffect (.enter scope)) (types_emitEffect (.enter scope))
        (generatedTargetFrame_emitEffect loop (.enter scope)) generated.dense generated.live frames)
  have scopedUnfold := inScope_eq scopeRun
  rcases scopedUnfold with ⟨middle, bodyRun, afterEq⟩
  have pushedGenerated := generatedBuilderState_changeStack enteredGenerated
    (scope :: entered.stack)
  have pushedFloor : first ≤ ({ entered with stack := scope :: entered.stack } : LS).vals.size := by
    simpa using enteredFloor
  have pushedTransfer : ∀ entry ∈ pre, ∀ descriptor,
      func.slots[entry.1]? = some descriptor →
      PermissionTransfer module.profile
        (FreshWritableEvidence le first { entered with stack := scope :: entered.stack })
        (FreshContentsEvidence le first { entered with stack := scope :: entered.stack })
        entry.2.1 descriptor.ty := by
    intro entry member descriptor row
    exact PermissionTransfer.stack (enteredTransfer entry member descriptor row) scope
  have bodyNew := NewPermissionInstructions.blockScopeBody bodyRun pushedTransfer pushedFloor pushedGenerated
    (enteredFrames.of_blocks (by rfl)) statementsNew valueNew
  have scopeNew' : NewPermissionInstructions module func le first entered after :=
    bodyNew.of_blocks_vals_eq (source := entered)
    (by rw [afterEq]) (by rw [afterEq])
  have scopeRunProperties :
      DenseRun (inScope scope (lowerBlockScopeBody loop pre want scope statements value)) ∧
      AdvB (inScope scope (lowerBlockScopeBody loop pre want scope statements value)) ∧
      TypeRun (inScope scope (lowerBlockScopeBody loop pre want scope statements value)) ∧
      GeneratedTargetFrameRun loop
        (inScope scope (lowerBlockScopeBody loop pre want scope statements value)) := by
    exact ⟨dense_inScope scope (dense_lowerBlockScopeBody loop pre want scope statements value),
      advB_inScope scope (advB_lowerBlockScopeBody loop pre want scope statements value),
      types_inScope scope (types_lowerBlockScopeBody loop pre want scope statements value),
      generatedTargetFrame_inScope scope
        (generatedTargetFrame_lowerBlockScopeBody loop pre want scope statements value)⟩
  exact NewPermissionInstructions.compose_framed enterNew scopeNew' scopeRun
    (scopeRunProperties.1) (scopeRunProperties.2.1) (scopeRunProperties.2.2.1)
    (scopeRunProperties.2.2.2) enteredGenerated enteredFrames

end Goose.Lower.Validation
