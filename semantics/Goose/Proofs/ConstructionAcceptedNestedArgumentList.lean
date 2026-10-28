import Goose.Proofs.ConstructionAcceptedNestedArgumentAnyUse

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence

theorem checkedNestedArgumentList_safety (config : EvalConfig) (accepted : AcceptedModule config)
    (implementationId : Nat) (implementation : Impl)
    (implementationAt : config.module.impls[implementationId]? = some implementation)
    {index : Nat} {parameters : List Param} {parameterTypes : List Ty}
    (descriptors : ScalarParameterDescriptors implementation index parameters parameterTypes) :
    ∀ (expressions : List Expr), NestedEffectfulArguments expressions →
      ∀ (frame : ConstructionSourceFrame) (state : ExecutionState) (types : RootTypes)
        (ambient : OwnershipAmbient) (live : Goose.Core.RootInst → Prop) (regions : List ReceivingRegion) (pending : List PendingCarrierFrame),
        AcceptedFrame config accepted frame state types → frame.initialized = config.module.globals.size →
        frame.typing.use = .ordinary → frame.typing.request = .value → frame.typing.resultRequests = [] →
        GlobalEffectTargetsBounded frame.rootCursor.eff config.module.globals.size →
        (∀ expression ∈ expressions, NestedArgumentSafe config frame expression) →
        SourcePosition accepted frame (.arguments implementation parameters (expressions.map Arg.byVal)) →
        ∃ specifications : List (Expr × Ty), specifications.map Prod.fst = expressions ∧ specifications.map Prod.snd = parameterTypes ∧
          ∀ specification ∈ specifications, ∀ runtimeFuel current,
            AcceptedWorld config frame.initialized current ambient types live regions pending →
            AcceptedFrame config accepted frame current types →
            FirstArgumentOutcome config accepted frame ambient types live regions pending specification.2 []
              (evalValue runtimeFuel config frame.interpretation.environment specification.1 current) := by
  intro expressions forms frame state types ambient live regions pending source initialized ordinary request requests bounded blocks position
  exact checkedNestedArgumentList_safetyAnyUse config accepted implementationId implementation implementationAt descriptors expressions forms
    frame state types ambient live regions pending source initialized bounded blocks position

#print axioms checkedNestedArgumentList_safety
end Goose.Proofs.ConstructionAcceptedExecution
