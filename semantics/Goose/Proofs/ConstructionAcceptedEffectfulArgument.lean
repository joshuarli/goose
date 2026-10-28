import Goose.Proofs.ConstructionAcceptedArgumentPrefixPosition
import Goose.Proofs.ConstructionAcceptedStatefulArgumentListSafety
import Goose.Proofs.ConstructionAcceptedStatefulCallFuel

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

inductive EffectfulScalarArgument : Expr → Prop
  | scalar {expression : Expr} (form : AcceptedBinaryExpression expression) : EffectfulScalarArgument expression
  | globalAssign (scope id origin blockOrigin : Nat) (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int)
      (form : AcceptedBinaryExpression expression) : EffectfulScalarArgument
        (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin)

def ArgumentBlockSafe (config : EvalConfig) (frame : ConstructionSourceFrame) (value : Expr) : Prop :=
  ∀ scope id origin blockOrigin expression intTy literal,
    value = .blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin →
    (∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ scope) ∧
    (∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope) ∧
    (∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool)

theorem checkedEffectfulScalarArgument (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes) (ambient : OwnershipAmbient)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (expression : Expr) (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (form : EffectfulScalarArgument expression) (blockSafe : ArgumentBlockSafe config frame expression)
    (source : AcceptedFrame config accepted frame state types) (initialized : frame.initialized = config.module.globals.size)
    (bounded : GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size)
    (typed : typeExpr frame.typingFuel frame.typing expression frame.typingCounter = .ok ([ty], typingAfter))
    (rooted : rpExpr frame.source expression frame.rootCursor = .ok (roots, rootsAfter))
    (scalar : (∃ intTy, ty = .int intTy) ∨ ty = .bool)
    (position : SourcePosition accepted frame (.expression expression)) :
    typingAfter = frame.typingCounter ∧ rootsAfter.nextVar = frame.rootCursor.nextVar ∧
      ∀ runtimeFuel current, AcceptedWorld config frame.initialized current ambient types live regions pending →
        AcceptedFrame config accepted frame current types →
        FirstArgumentOutcome config accepted frame ambient types live regions pending ty []
          (evalValue runtimeFuel config frame.interpretation.environment expression current) := by
  cases form with
  | scalar form =>
    have afterBounded := recursiveScalar_effects_bounded form frame.typingFuel frame.typing frame.source config.module.globals.size
      frame.typingCounter typingAfter frame.rootCursor rootsAfter [ty] roots source.compatible.globals bounded typed rooted
    have available : GlobalEffectsAvailable frame.interpretation frame.initialized rootsAfter.eff := by
      rw [initialized, ← source.compatible.globalCount]
      exact (globalEffectsAvailable_iff_bounded frame.interpretation rootsAfter.eff).2
        (by simpa only [source.compatible.globalCount] using afterBounded)
    have checked : CheckedValue frame _ ty roots typingAfter rootsAfter := ⟨typed, rooted, available⟩
    have cursors := checked_binary_recursive_cursor form frame ty roots typingAfter rootsAfter checked
    refine ⟨cursors.1, cursors.2, ?_⟩
    intro runtimeFuel current world currentSource
    exact evalValue_checkedScalar_argumentOutcome form runtimeFuel config accepted frame current ambient types live regions pending
      world currentSource ty roots typingAfter rootsAfter checked scalar
  | globalAssign scope id origin blockOrigin expression intTy literal form =>
    obtain ⟨fresh, absent, globalScalar⟩ := blockSafe scope id origin blockOrigin expression intTy literal rfl
    have enough := typeExpr_statefulBlock_fuel frame.typingFuel frame.typing scope id origin blockOrigin expression intTy literal
      frame.typingCounter typingAfter [ty] typed
    let checkFuel := frame.typingFuel - 4
    have nesting : frame.typingFuel = checkFuel + 4 := by dsimp [checkFuel]; omega
    have sameType := typeExpr_integerTail_result (checkFuel + 1) frame.typing scope [.assign (.global id) expression origin]
      intTy literal blockOrigin frame.typingCounter typingAfter [ty] (by simpa [nesting, Nat.add_assoc] using typed)
    have tyEq : ty = .int intTy := by simpa using sameType
    have cursors := statefulBlock_expression_cursors checkFuel config accepted frame state types scope id origin blockOrigin expression intTy literal
      form source initialized fresh absent position nesting [ty] typingAfter roots rootsAfter typed rooted
    refine ⟨cursors.1, cursors.2, ?_⟩
    intro runtimeFuel current world currentSource
    have result := evalValue_globalAssign_integerTail_world runtimeFuel checkFuel config accepted frame current ambient types live regions pending
      scope id expression origin blockOrigin intTy literal form world currentSource initialized fresh absent position nesting globalScalar
    simpa [tyEq] using result

#print axioms checkedEffectfulScalarArgument
end Goose.Proofs.ConstructionAcceptedExecution
