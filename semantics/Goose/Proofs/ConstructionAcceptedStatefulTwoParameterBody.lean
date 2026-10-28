import Goose.Proofs.ConstructionAcceptedIntegerBlockTyping
import Goose.Proofs.ConstructionAcceptedTwoParameterCall

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRepresentation

theorem evalArguments_statefulTwoParameter_body {config : EvalConfig} {accepted : AcceptedModule config}
    (fuel checkFuel : Nat) (frame : ConstructionSourceFrame) (state : ExecutionState) (ambient : OwnershipAmbient)
    (types : RootTypes) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (contextId callOrigin : Nat) (context : Context) (callee : Impl) (first second : Param)
    (firstDescriptor secondDescriptor : LocalVar) (scope id origin blockOrigin : Nat) (expression : Expr)
    (intTy : Goose.Core.IntTy) (literal : Int) (right : Expr) (resultTy : Ty)
    (form : AcceptedBinaryExpression expression) (rightForm : AcceptedBinaryExpression right)
    (world : AcceptedWorld config frame.initialized state ambient types live regions pending)
    (source : AcceptedFrame config accepted frame state types)
    (contextAt : config.module.contexts[contextId]? = some context)
    (calleeAt : config.module.impls[context.impl]? = some callee)
    (parameters : callee.params = #[first, second])
    (firstMode : first.mode = .byValue) (secondMode : second.mode = .byValue)
    (firstDeclared : callee.vars[0]? = some firstDescriptor) (secondDeclared : callee.vars[1]? = some secondDescriptor)
    (firstScalar : (∃ t, firstDescriptor.ty = .int t) ∨ firstDescriptor.ty = .bool)
    (secondScalar : (∃ t, secondDescriptor.ty = .int t) ∨ secondDescriptor.ty = .bool)
    (initialized : frame.initialized = config.module.globals.size)
    (fresh : ∀ entry ∈ frame.interpretation.environment.scopes, entry.1 ≠ scope)
    (absent : ∀ descriptor ∈ frame.interpretation.environment.vars.toList, descriptor.scope ≠ scope)
    (nesting : frame.typingFuel = checkFuel + 6)
    (position : SourcePosition accepted frame (.expression (.call contextId
      [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] callOrigin)))
    (globalScalar : ∀ descriptor, config.module.globals[id]? = some descriptor →
      (∃ scalarTy, descriptor.ty = .int scalarTy) ∨ descriptor.ty = .bool) :
    ∃ rightFrame : ConstructionSourceFrame,
      rightFrame.interpretation = frame.interpretation ∧ rightFrame.initialized = frame.initialized ∧
      let step := evalArguments fuel config frame.interpretation.environment callee.vars [first, second]
        [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] state
      AcceptedWorld config frame.initialized (Goose.Proofs.Exit.stepState step) ambient types live regions pending ∧
      AcceptedFrame config accepted rightFrame (Goose.Proofs.Exit.stepState step) types ∧
      match step with
      | .ok values argumentState => ∃ firstValue secondValue, values = [firstValue, secondValue] ∧
          ∃ helperFrame activation after,
          let activated := { argumentState with nextAct := argumentState.nextAct + 1, activations := activation :: argumentState.activations }
          let scopeState := ownershipResultScopeState activation callee.body.scope activated
          let firstRoot := Goose.Core.RootInst.local activation.act argumentState.nextScope 0
          let secondRoot := Goose.Core.RootInst.local activation.act argumentState.nextScope 1
          let afterTypes := registerRootType (registerRootType types firstRoot firstDescriptor.ty) secondRoot secondDescriptor.ty
          helperFrame.source.impl = callee ∧ helperFrame.initialized = config.module.globals.size ∧
          helperFrame.phase = .implementation contextId ∧ helperFrame.interpretation.environment = activation ∧
          activation.act = argumentState.nextAct ∧ activation.scopes = [] ∧ activation.channels = [.register resultTy] ∧
          freshAct argumentState = .ok activation.act { argumentState with nextAct := argumentState.nextAct + 1 } ∧
          freshScope activated = .ok activated.nextScope { activated with nextScope := activated.nextScope + 1 } ∧
          bindAll activation.act argumentState.nextScope [(first.var, firstValue), (second.var, secondValue)] scopeState = .ok () after ∧
          RootTypesExtend types afterTypes ∧
          AcceptedWorld config config.module.globals.size after (.callChannels activation [] :: ambient) afterTypes
            (fun other => other = secondRoot ∨ other = firstRoot ∨ live other) regions pending ∧
          AcceptedFrame config accepted (entryStatementsFrame config helperFrame argumentState.nextScope) after afterTypes ∧
          SourcePosition accepted (entryStatementsFrame config helperFrame argumentState.nextScope) (.statements callee.body.stmts)
      | .stop .. => True
      | _ => False := by
  have firstAt : callee.params[0]? = some first := by simp [parameters]
  have secondAt : callee.params[1]? = some second := by simp [parameters]
  have firstId := validated_parameter_variable config.module context.impl callee 0 first accepted.accepted calleeAt firstAt
  have secondId := validated_parameter_variable config.module context.impl callee 1 second accepted.accepted calleeAt secondAt
  have firstDeclared' : callee.vars[first.var]? = some firstDescriptor := by simpa [firstId] using firstDeclared
  have secondDeclared' : callee.vars[second.var]? = some secondDescriptor := by simpa [secondId] using secondDeclared
  have firstType := statefulCall_firstParameterType frame checkFuel contextId callOrigin context callee first second
    firstDescriptor secondDescriptor scope id origin blockOrigin expression intTy literal right source.compatible contextAt calleeAt
    parameters firstMode secondMode firstDeclared' secondDeclared' firstScalar secondScalar nesting position
  obtain ⟨rightFrame, sameInterpretation, sameInitialized, outcome⟩ :=
    evalArguments_statefulScalar_world fuel checkFuel frame state ambient types live regions pending contextId callOrigin context callee
      first second firstDescriptor secondDescriptor scope id origin blockOrigin expression intTy literal right form rightForm
      world source contextAt calleeAt parameters firstMode secondMode firstDeclared' secondDeclared' firstScalar secondScalar
      initialized fresh absent nesting position globalScalar
  refine ⟨rightFrame, sameInterpretation, sameInitialized, ?_⟩
  cases executed : evalArguments fuel config frame.interpretation.environment callee.vars [first, second]
      [.byVal (.blockE ⟨scope, [.assign (.global id) expression origin], some (.lit intTy literal)⟩ blockOrigin), .byVal right] state with
  | escape address carriers after | jump target kind after => simp [executed] at outcome
  | stop reason after => simpa [executed] using outcome
  | ok values argumentState =>
    simp only [executed, Goose.Proofs.Exit.stepState] at outcome ⊢
    obtain ⟨argumentWorld, callerSource, firstValue, secondValue, valuesEq, firstValid, secondValid⟩ := outcome
    have initialWorld : AcceptedWorld config config.module.globals.size argumentState ambient types live regions pending := initialized ▸ argumentWorld
    have firstRepresented : ValueRepresentation firstDescriptor.ty firstValue := by simpa [firstType] using firstValid.represented
    have firstPointers : PointerTypedValue types firstDescriptor.ty firstValue := by simpa [firstType] using firstValid.pointers
    obtain ⟨helperFrame, activation, after, sameImpl, helperInitialized, phase, environment, act, scopes, channels, freshActStep, freshScopeStep,
      bound, extended, helperWorld, helperSource, helperPosition⟩ :=
      acceptedRegisterTwoParameterCallBody config accepted argumentState ambient types live regions pending contextId context callee
        first second firstDescriptor secondDescriptor firstValue secondValue resultTy contextAt calleeAt parameters firstDeclared secondDeclared
        firstScalar secondScalar firstRepresented secondValid.represented firstPointers secondValid.pointers initialWorld
    exact ⟨argumentWorld, callerSource, firstValue, secondValue, valuesEq, helperFrame, activation, after, sameImpl, helperInitialized,
      phase, environment, act, scopes, channels, freshActStep, freshScopeStep, bound, extended, helperWorld, helperSource, helperPosition⟩

#print axioms evalArguments_statefulTwoParameter_body
end Goose.Proofs.ConstructionAcceptedExecution
