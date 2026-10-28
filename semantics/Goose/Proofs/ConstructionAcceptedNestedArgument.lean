import Goose.Proofs.ConstructionAcceptedEffectfulArgument
import Goose.Proofs.ConstructionAcceptedNestedBlockCursors

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

inductive NestedEffectfulArgument : Expr → Prop
  | flat {expression : Expr} (form : EffectfulScalarArgument expression) : NestedEffectfulArgument expression
  | nested (outerScope innerScope id origin innerOrigin outerOrigin : Nat) (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int)
      (form : AcceptedBinaryExpression expression) : NestedEffectfulArgument (.blockE ⟨outerScope, [], some (.blockE
        ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ innerOrigin)⟩ outerOrigin)

def NestedArgumentSafe (config : EvalConfig) (frame : ConstructionSourceFrame) (value : Expr) : Prop :=
  ArgumentBlockSafe config frame value ∧
  ∀ outerScope innerScope id origin innerOrigin outerOrigin expression intTy literal,
    value = .blockE ⟨outerScope, [], some (.blockE
      ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ innerOrigin)⟩ outerOrigin →
    (∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ outerScope) ∧
    (∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ innerScope) ∧
    innerScope ≠ outerScope ∧
    (∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ outerScope) ∧
    (∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ innerScope) ∧
    (∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool)

theorem checkedNestedEffectfulArgument (config : EvalConfig) (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes) (ambient : OwnershipAmbient)
    (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (expression : Expr) (ty : Ty) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (form : NestedEffectfulArgument expression) (blockSafe : NestedArgumentSafe config frame expression)
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
  | flat form =>
    exact checkedEffectfulScalarArgument config accepted frame state types ambient live regions pending expression ty roots typingAfter rootsAfter
      form blockSafe.1 source initialized bounded typed rooted scalar position
  | nested outerScope innerScope id origin innerOrigin outerOrigin expression intTy literal form =>
    obtain ⟨outerFresh, innerFresh, different, outerAbsent, innerAbsent, globalScalar⟩ :=
      blockSafe.2 outerScope innerScope id origin innerOrigin outerOrigin expression intTy literal rfl
    cases outerFuel : frame.typingFuel with
    | zero => rw [outerFuel] at typed; change Except.error _ = Except.ok _ at typed; cases typed
    | succ fuel =>
      cases fuel with
      | zero =>
        simp [outerFuel, typeExpr, blockResultTypes?, expressionResultTypes?] at typed
        change Except.error _ = Except.ok _ at typed
        cases typed
      | succ sourceFuel =>
        have nesting : frame.typingFuel = sourceFuel + 2 := by simpa [Nat.add_assoc] using outerFuel
        have cursors := nestedBlock_expression_cursors sourceFuel config accepted frame state types outerScope innerScope id origin innerOrigin outerOrigin
          expression intTy literal form source initialized outerFresh innerFresh different outerAbsent innerAbsent position nesting [ty] typingAfter roots rootsAfter typed rooted
        have sameType : ty = .int intTy := by simpa using cursors.2.2
        refine ⟨cursors.1, cursors.2.1, ?_⟩
        intro runtimeFuel current world currentSource
        have result := evalValue_nestedGlobalAssign_world runtimeFuel sourceFuel config accepted frame current ambient types live regions pending
          outerScope innerScope id origin innerOrigin outerOrigin expression intTy literal form world currentSource initialized outerFresh innerFresh
          different outerAbsent innerAbsent globalScalar position nesting
        simpa [sameType] using result

#print axioms checkedNestedEffectfulArgument
end Goose.Proofs.ConstructionAcceptedExecution
