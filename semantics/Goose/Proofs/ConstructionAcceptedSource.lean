import Goose.Proofs.ConstructionRootCorrespondenceEntry
import Goose.Proofs.ConstructionRootCorrespondenceScopes

set_option Elab.async false

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRootCorrespondence

structure AcceptedModule (config : EvalConfig) : Prop where
  accepted : validate config.module = .ok ()
  roots : ModuleRootFacts config.module

theorem acceptedModule (config : EvalConfig) (accepted : validate config.module = .ok ()) : AcceptedModule config :=
  ⟨accepted, validated_moduleRootFacts config.module accepted⟩

noncomputable def AcceptedModule.aliases {config : EvalConfig} (valid : AcceptedModule config) :
    Array (List (RootRef × RootRef)) := Classical.choose valid.roots

theorem AcceptedModule.aliases_size {config : EvalConfig} (valid : AcceptedModule config) :
    valid.aliases.size = config.module.contexts.size := (Classical.choose_spec valid.roots).1

inductive SourcePhase
  | initializer (global : Goose.Core.GlobalId)
  | implementation (context : Goose.Core.ContextId)

structure ConstructionSourceFrame where
  phase : SourcePhase
  typing : TypingEnv
  source : PEnv
  interpretation : RootInterpretation
  initialized : Nat
  typingFuel : Nat
  typingCounter : Nat
  rootCursor : RState

def SourceOrigin {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) : Prop :=
  match frame.phase with
  | .initializer global =>
      ∃ descriptor, config.module.globals[global]? = some descriptor ∧
        frame.typing.implementation = none ∧ frame.typing.globalLimit = global ∧ frame.initialized = global ∧
        frame.source.impl = initImpl ∧ frame.source.ctx = initContext ∧ frame.source.aliases = [] ∧
        frame.source.escaping = #[] ∧ frame.source.targetEscapes = #[] ∧
        ∃ calls, InitializerRootFacts config.module global calls
  | .implementation contextId =>
      ∃ original calls, config.module.contexts[contextId]? = some original ∧
        config.module.impls[original.impl]? = some frame.source.impl ∧
        frame.interpretation.environment.implementation = original.impl ∧
        frame.typing.implementation = some frame.source.impl ∧
        parameterBodyRootContext config.module frame.source.impl original = .ok frame.source.ctx ∧
        frame.source.aliases = accepted.aliases[contextId]! ∧
        ContextRootFacts config.module original frame.source.aliases calls ∧
        bodyTargets config.module = .ok frame.source.targetEscapes ∧
        ∃ roots next,
          (rpBlockValue { frame.source with scopes := [], valueBlock := none, initializing := [] }
            [] frame.source.impl.body).run ⟨frame.source.impl.params.size, {}, []⟩ = .ok (roots, next)

structure SourceFrameCompatible {config : EvalConfig} (accepted : AcceptedModule config)
    (frame : ConstructionSourceFrame) : Prop where
  module : frame.typing.module = config.module
  rootModule : frame.source.mod = config.module
  variables : frame.interpretation.environment.vars = frame.typing.variables
  sourceVariables : frame.source.impl.vars = frame.typing.variables
  scopes : frame.source.scopes = frame.interpretation.environment.scopes.map Prod.fst
  globalCount : frame.interpretation.globalCount = config.module.globals.size
  globals : frame.typing.globalLimit ≤ frame.initialized
  initialized : frame.initialized ≤ config.module.globals.size
  declarations : frame.rootCursor.nextVar ≤ frame.typingCounter
  typingBound : frame.typingCounter ≤ frame.typing.variables.size
  visible : ∀ id ∈ frame.typing.visible, id < frame.rootCursor.nextVar
  initializing : ∀ id ∈ frame.source.initializing, id ∉ frame.typing.visible
  currentScope : ∀ scope rest, frame.source.scopes = scope :: rest → frame.typing.scope = scope
  origin : SourceOrigin accepted frame

structure CheckedValue (frame : ConstructionSourceFrame) (expression : Expr) (ty : Ty)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState) : Prop where
  typing : typeExpr frame.typingFuel frame.typing expression frame.typingCounter = .ok ([ty], typingAfter)
  provenance : (rpExpr frame.source expression).run frame.rootCursor = .ok (roots, rootsAfter)

structure CheckedPlace (frame : ConstructionSourceFrame) (place : Place) (ty : Ty)
    (binding contents : Bool) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState) : Prop where
  typing : typePlace frame.typingFuel frame.typing place frame.typingCounter =
    .ok ((ty, binding, contents), typingAfter)
  provenance : (rpPlace frame.source place).run frame.rootCursor = .ok (roots, rootsAfter)

structure CheckedView (frame : ConstructionSourceFrame) (view : View) (element : Ty)
    (writable : Bool) (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState) : Prop where
  typing : typeView frame.typingFuel frame.typing view frame.typingCounter = .ok ((element, writable), typingAfter)
  provenance : (rpView frame.source view).run frame.rootCursor = .ok (roots, rootsAfter)

#print axioms acceptedModule
#print axioms AcceptedModule.aliases_size

end Goose.Proofs.ConstructionAcceptedExecution
