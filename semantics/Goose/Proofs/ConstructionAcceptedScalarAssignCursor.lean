import Goose.Proofs.ConstructionAcceptedScalarAssignSource
import Lean.Elab.Tactic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

private def assignCursorHelperName (name : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Goose") "Construct") "Roots") 0) "Goose") "Construct") name

elab "unfold_assign_cursor_helpers" : tactic => do
  let capture := Lean.mkIdent (assignCursorHelperName "captureEffects")
  let named := Lean.mkIdent (assignCursorHelperName "noteNamed")
  let shrink := Lean.mkIdent (assignCursorHelperName "checkRetainedShrinks")
  let merge := Lean.mkIdent (assignCursorHelperName "mergeEffects")
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $capture $named $shrink $merge at *))

private theorem scalarAssign_addTargets_members (before added : List Target) (target : Target) :
    target ∈ addTargets before added ↔ target ∈ before ∨ target ∈ added := by
  induction added generalizing before with
  | nil => simp [addTargets]
  | cons selected rest ih =>
    simp only [addTargets, List.foldl_cons]
    split
    · rename_i retained
      change target ∈ addTargets before rest ↔ _
      rw [ih]
      have present : selected ∈ before := by simpa using retained
      simp only [List.mem_cons]
      constructor
      · intro member
        rcases member with member | member
        · exact Or.inl member
        · exact Or.inr (Or.inr member)
      · intro member
        rcases member with member | equal | member
        · exact Or.inl member
        · exact Or.inl (equal ▸ present)
        · exact Or.inr member
    · change target ∈ addTargets (before ++ [selected]) rest ↔ _
      rw [ih]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc]

def scalarAssignmentRoots : Place → List RootRef
  | .var id => [.local id]
  | .global id => [.global id]
  | _ => []

theorem rpStmt_directAssign_cursor (env : PEnv) (place : Place) (expression : Expr) (origin : Goose.Core.OriginId)
    (before after middle : RState) (roots : List RootRef)
    (direct : (∃ id, place = .var id) ∨ ∃ id, place = .global id)
    (operand : rpExpr env expression { before with eff := {} } = .ok (roots, middle))
    (checked : rpStmt env (.assign place expression origin) before = .ok ((), after)) :
    after.nextVar = middle.nextVar := by
  have modifyState (f : RState → RState) (state : RState) : (modify f : P Unit) state = .ok ((), f state) := rfl
  rcases direct with ⟨id, rfl⟩ | ⟨id, rfl⟩ <;>
    simp only [rpStmt, rpPlace, bind, StateT.bind] at checked <;>
    unfold_assign_cursor_helpers <;>
    simp [bind, Except.bind, modifyState, pure, StateT.pure, Except.pure, operand] at checked
  case inl =>
    cases store : checkStore env (.var id) roots <;>
      simp [liftV, store, addWrites, addRoots, modifyState] at checked
    all_goals
      split at checked
      all_goals rename_i result actionEq
      all_goals split at actionEq <;> simp_all [rejP, StateT.pure, Except.pure, pure]
      all_goals try (change Except.error _ = Except.ok _ at actionEq; cases actionEq)
      all_goals cases actionEq <;> cases checked <;> rfl
  case inr =>
    cases store : checkStore env (.global id) roots <;>
      simp [liftV, store, addWrites, addRoots, modifyState] at checked
    all_goals
      split at checked
      all_goals rename_i result actionEq
      all_goals split at actionEq <;> simp_all [rejP, StateT.pure, Except.pure, pure]
      all_goals try (change Except.error _ = Except.ok _ at actionEq; cases actionEq)
      all_goals cases actionEq <;> cases checked <;> rfl

theorem rpStmt_directAssign_accessTargets (env : PEnv) (place : Place) (expression : Expr) (origin : Goose.Core.OriginId)
    (before after middle : RState) (roots : List RootRef)
    (direct : (∃ id, place = .var id) ∨ ∃ id, place = .global id)
    (operand : rpExpr env expression { before with eff := {} } = .ok (roots, middle))
    (checked : rpStmt env (.assign place expression origin) before = .ok ((), after)) :
    after.eff.accessTargets =
      addTargets before.eff.reads middle.eff.reads ++
      addTargets (addTargets before.eff.writes middle.eff.writes) (rootsTargets (scalarAssignmentRoots place)) ++
      addTargets before.eff.grows middle.eff.grows ++ addTargets before.eff.shrinks middle.eff.shrinks := by
  have modifyState (f : RState → RState) (state : RState) : (modify f : P Unit) state = .ok ((), f state) := rfl
  rcases direct with ⟨id, rfl⟩ | ⟨id, rfl⟩ <;>
    simp only [rpStmt, rpPlace, bind, StateT.bind] at checked <;>
    unfold_assign_cursor_helpers <;>
    simp [bind, Except.bind, modifyState, pure, StateT.pure, Except.pure, operand] at checked
  case inl =>
    cases store : checkStore env (.var id) roots <;>
      simp [liftV, store, addWrites, addRoots, modifyState] at checked
    all_goals
      split at checked
      all_goals rename_i result actionEq
      all_goals split at actionEq <;> simp_all [rejP, StateT.pure, Except.pure, pure]
      all_goals try (change Except.error _ = Except.ok _ at actionEq; cases actionEq)
      all_goals cases actionEq <;> cases checked <;> simp [Eff.accessTargets, scalarAssignmentRoots]
  case inr =>
    cases store : checkStore env (.global id) roots <;>
      simp [liftV, store, addWrites, addRoots, modifyState] at checked
    all_goals
      split at checked
      all_goals rename_i result actionEq
      all_goals split at actionEq <;> simp_all [rejP, StateT.pure, Except.pure, pure]
      all_goals try (change Except.error _ = Except.ok _ at actionEq; cases actionEq)
      all_goals cases actionEq <;> cases checked <;> simp [Eff.accessTargets, scalarAssignmentRoots]


theorem rpStmt_directAssign_effects_bounded (env : PEnv) (place : Place) (expression : Expr) (origin : Goose.Core.OriginId)
    (before after middle : RState) (roots : List RootRef) (count : Nat)
    (direct : (∃ id, place = .var id) ∨ ∃ id, place = .global id)
    (operand : rpExpr env expression { before with eff := {} } = .ok (roots, middle))
    (checked : rpStmt env (.assign place expression origin) before = .ok ((), after))
    (beforeBounded : GlobalEffectTargetsBounded before.eff count)
    (operandBounded : GlobalEffectTargetsBounded middle.eff count)
    (targetBounded : ∀ id, .global id ∈ rootsTargets (scalarAssignmentRoots place) → id < count) :
    GlobalEffectTargetsBounded after.eff count := by
  have access := rpStmt_directAssign_accessTargets env place expression origin before after middle roots direct operand checked
  intro id member
  rw [access] at member
  simp only [List.mem_append, scalarAssign_addTargets_members] at member
  rcases member with ((((oldRead | newRead) | ((oldWrite | newWrite) | target)) | (oldGrow | newGrow)) | (oldShrink | newShrink))
  · exact beforeBounded id (by simp [Eff.accessTargets, oldRead])
  · exact operandBounded id (by simp [Eff.accessTargets, newRead])
  · exact beforeBounded id (by simp [Eff.accessTargets, oldWrite])
  · exact operandBounded id (by simp [Eff.accessTargets, newWrite])
  · exact targetBounded id target
  · exact beforeBounded id (by simp [Eff.accessTargets, oldGrow])
  · exact operandBounded id (by simp [Eff.accessTargets, newGrow])
  · exact beforeBounded id (by simp [Eff.accessTargets, oldShrink])
  · exact operandBounded id (by simp [Eff.accessTargets, newShrink])

theorem SourcePosition.scalarAssign_tailReplay {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (types : RootTypes)
    (place : Place) (expression : Expr) (origin : Goose.Core.OriginId) (rest : List Stmt)
    (checkFuel : Nat) (form : AcceptedBinaryExpression expression)
    (source : AcceptedFrame config accepted frame before types)
    (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (position : SourcePosition accepted frame (.statements (.assign place expression origin :: rest)))
    (nesting : frame.typingFuel = checkFuel + 2)
    (direct : (∃ id, place = .var id) ∨ ∃ id, place = .global id) :
    ∃ rootsAfter, rootsAfter.nextVar = frame.rootCursor.nextVar ∧
      GlobalEffectTargetsBounded rootsAfter.eff config.module.globals.size ∧
      typeStatement (checkFuel + 1) frame.typing (.assign place expression origin) frame.typingCounter = .ok (frame.typing, frame.typingCounter) ∧
      rpStmt frame.source (.assign place expression origin) frame.rootCursor = .ok ((), rootsAfter) ∧
      SourcePosition accepted { frame with typingFuel := checkFuel + 1, rootCursor := rootsAfter } (.statements rest) := by
  have headPosition := position.statements_head accepted frame (.assign place expression origin) rest (checkFuel + 1) nesting
  obtain ⟨next, typingAfter, rootsAfter, typed, rooted⟩ := headPosition.checked accepted _ _
  obtain ⟨ty, roots, expressionTypingAfter, expressionRootsAfter, checked, operandSource, sameNext, sameAfter,
      writable, binding, placeTyped, mutable⟩ :=
    checkedValue_scalarAssign_operand checkFuel config accepted frame before types place expression origin form
      next typingAfter rootsAfter source initialized direct typed rooted
  have cursor := checked_binary_recursive_cursor form (scalarAssignmentOperandFrame frame checkFuel) ty roots
    expressionTypingAfter expressionRootsAfter checked
  have nextVar := rpStmt_directAssign_cursor frame.source place expression origin frame.rootCursor rootsAfter expressionRootsAfter
    roots direct checked.provenance rooted
  have sameRoot : rootsAfter.nextVar = frame.rootCursor.nextVar := by
    rw [nextVar]
    simpa [scalarAssignmentOperandFrame, ordinaryOperandFrame] using cursor.2
  have operandBounded : GlobalEffectTargetsBounded expressionRootsAfter.eff config.module.globals.size := by
    exact (globalEffectsAvailable_iff_bounded frame.interpretation expressionRootsAfter.eff).1
      (by simpa [scalarAssignmentOperandFrame, ordinaryOperandFrame, initialized, source.compatible.globalCount] using checked.available)
      |> fun h => by simpa [source.compatible.globalCount] using h
  have targetBounded : ∀ id, .global id ∈ rootsTargets (scalarAssignmentRoots place) → id < config.module.globals.size := by
    intro id member
    rcases direct with ⟨localId, same⟩ | ⟨globalId, same⟩
    · subst place; simp [scalarAssignmentRoots, rootsTargets, rootTarget] at member
    · subst place
      have equal : id = globalId := by simpa [scalarAssignmentRoots, rootsTargets, rootTarget] using member
      subst id
      obtain ⟨descriptor, inside, declared, sameTy, sameMutable, sameCounter⟩ :=
        typePlace_global_scalarFacts checkFuel frame.typing globalId frame.typingCounter frame.typingCounter ty writable binding placeTyped
      exact Nat.lt_of_lt_of_le inside source.compatible.globals
  have finalBounded := rpStmt_directAssign_effects_bounded frame.source place expression origin frame.rootCursor rootsAfter
    expressionRootsAfter roots config.module.globals.size direct checked.provenance rooted bounded operandBounded targetBounded
  have tail := position.statements_tail accepted frame (.assign place expression origin) rest (checkFuel + 1) next typingAfter
    rootsAfter nesting typed rooted
  have sameCounter : typingAfter = frame.typingCounter := by
    rw [sameAfter]
    simpa [scalarAssignmentOperandFrame, ordinaryOperandFrame] using cursor.1
  refine ⟨rootsAfter, sameRoot, finalBounded, ?_, rooted, ?_⟩
  · simpa [sameNext, sameCounter] using typed
  · simpa [sameNext, sameCounter] using tail



theorem SourcePosition.scalarAssign_tail {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (before : ExecutionState) (types : RootTypes)
    (place : Place) (expression : Expr) (origin : Goose.Core.OriginId) (rest : List Stmt)
    (checkFuel : Nat) (form : AcceptedBinaryExpression expression)
    (source : AcceptedFrame config accepted frame before types)
    (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (position : SourcePosition accepted frame (.statements (.assign place expression origin :: rest)))
    (nesting : frame.typingFuel = checkFuel + 2)
    (direct : (∃ id, place = .var id) ∨ ∃ id, place = .global id) :
    ∃ rootsAfter, rootsAfter.nextVar = frame.rootCursor.nextVar ∧
      GlobalEffectTargetsBounded rootsAfter.eff config.module.globals.size ∧
      SourcePosition accepted { frame with typingFuel := checkFuel + 1, rootCursor := rootsAfter } (.statements rest) := by
  obtain ⟨rootsAfter, sameRoot, finalBounded, typed, rooted, tail⟩ :=
    position.scalarAssign_tailReplay accepted frame before types place expression origin rest checkFuel form source initialized bounded nesting direct
  exact ⟨rootsAfter, sameRoot, finalBounded, tail⟩

#print axioms SourcePosition.scalarAssign_tail
#print axioms SourcePosition.scalarAssign_tailReplay
#print axioms rpStmt_directAssign_effects_bounded
#print axioms rpStmt_directAssign_accessTargets
#print axioms rpStmt_directAssign_cursor
end Goose.Proofs.ConstructionAcceptedExecution
