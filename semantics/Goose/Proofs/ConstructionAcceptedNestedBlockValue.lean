import Goose.Proofs.ConstructionAcceptedNestedTailProduce
import Goose.Proofs.ConstructionAcceptedNestedBlockProduce
import Goose.Proofs.ConstructionAcceptedNestedBlockQuery
import Goose.Proofs.ConstructionAcceptedTwoArgumentExecution

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem evalValue_nestedGlobalAssign_world (fuel sourceFuel : Nat)
    (config : EvalConfig) (accepted : AcceptedModule config) (frame : ConstructionSourceFrame)
    (state : ExecutionState) (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (outerScope innerScope id origin innerOrigin outerOrigin : Nat) (expression : Expr) (intTy : Goose.Core.IntTy) (literal : Int)
    (form : AcceptedBinaryExpression expression)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types) (initialized : frame.initialized = config.module.globals.size)
    (outerFresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ outerScope)
    (innerFresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ innerScope)
    (different : innerScope ≠ outerScope)
    (outerAbsent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ outerScope)
    (innerAbsent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ innerScope)
    (scalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool)
    (position : SourcePosition accepted frame (.expression (.blockE ⟨outerScope, [], some (.blockE
      ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ innerOrigin)⟩ outerOrigin)))
    (nesting : frame.typingFuel = sourceFuel + 2) :
    FirstArgumentOutcome config accepted frame ambient types live regions pending (.int intTy) []
      (evalValue fuel config frame.interpretation.environment (.blockE ⟨outerScope, [], some (.blockE
        ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ innerOrigin)⟩ outerOrigin) state) := by
  cases fuel with
  | zero => simp [evalValue, timeout, EvalM.stop, FirstArgumentOutcome, Goose.Proofs.Exit.stepState, world, source]
  | succ fuel =>
    obtain ⟨expected, bodyPosition, innerPosition⟩ := position.emptyBlock_nestedTail accepted frame outerScope state.nextScope outerOrigin sourceFuel
      (.blockE ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ innerOrigin) nesting
    let bodyFrame := valueBlockExpressionFrame frame outerScope (sourceFuel + 1) expected
    have bodySource : AcceptedFrame config accepted bodyFrame state types := source.valueBlockExpression outerScope (sourceFuel + 1) expected
    have callback : ∀ tailFuel before outerAmbient,
        AcceptedWorld config bodyFrame.initialized before outerAmbient types live regions pending →
        AcceptedFrame config accepted bodyFrame before types →
        let scopeState := ownershipResultScopeState bodyFrame.interpretation.environment outerScope before
        let child := unusedChildScopeFrame bodyFrame outerScope before.nextScope sourceFuel
        let step := evalProduce tailFuel config child.interpretation.environment [.register (.int intTy)]
          (.blockE ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ innerOrigin) scopeState
        RegisterBreakActionOutcome config accepted child outerAmbient types live regions pending step ∧
          match step with | .ok carriers _ => carriers = [.register (.int intTy literal)] | _ => True := by
      intro tailFuel before outerAmbient currentWorld currentSource
      exact nestedTail_globalAssign_safe tailFuel sourceFuel config accepted bodyFrame before outerAmbient types live regions pending
        outerScope innerScope id origin innerOrigin expression intTy literal form currentWorld currentSource initialized outerFresh innerFresh
        different outerAbsent innerAbsent scalar bodyPosition rfl
    have safe := evalProduce_emptyTail_world fuel sourceFuel config accepted bodyFrame state ambient types live regions pending
      outerScope outerOrigin (.blockE ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ innerOrigin)
      intTy literal world bodySource outerFresh outerAbsent callback
    cases produced : evalProduce fuel config frame.interpretation.environment [.register (.int intTy)]
        (.blockE ⟨outerScope, [], some (.blockE ⟨innerScope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ innerOrigin)⟩ outerOrigin) state with
    | escape address carriers after | jump target kind after => simp [bodyFrame, valueBlockExpressionFrame, produced, RegisterBreakActionOutcome] at safe
    | stop reason after =>
      simp only [bodyFrame, valueBlockExpressionFrame, produced, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] at safe
      have evaluated := evalValue_nestedIntegerBlock_of_produceStop fuel config frame.interpretation.environment outerScope innerScope id origin innerOrigin outerOrigin
        expression intTy literal state after reason produced
      have finalSource := source.leaveValueBlockExpression outerScope (sourceFuel + 1) expected safe.1.2.1
      simpa [evaluated, FirstArgumentOutcome, Goose.Proofs.Exit.stepState] using And.intro safe.1.1 (And.intro finalSource True.intro)
    | ok carriers after =>
      simp only [bodyFrame, valueBlockExpressionFrame, produced, RegisterBreakActionOutcome, Goose.Proofs.Exit.stepState] at safe
      have carrierShape := safe.2
      subst carriers
      have evaluated := evalValue_nestedIntegerBlock_of_produce fuel config frame.interpretation.environment outerScope innerScope id origin innerOrigin outerOrigin
        expression intTy literal state after (.int intTy literal) produced
      have finalSource := source.leaveValueBlockExpression outerScope (sourceFuel + 1) expected safe.1.2.1
      have value : AcceptedValue config.layout types frame.interpretation after (.int intTy) [] (.int intTy literal) :=
        ⟨.integer intTy literal, .integer intTy literal, .integer intTy literal, by intro location reference; cases reference⟩
      simpa [evaluated, FirstArgumentOutcome, Goose.Proofs.Exit.stepState] using And.intro safe.1.1 (And.intro finalSource value)

#print axioms evalValue_nestedGlobalAssign_world
end Goose.Proofs.ConstructionAcceptedExecution
