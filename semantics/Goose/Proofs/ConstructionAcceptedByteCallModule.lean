import Goose.Proofs.ConstructionAcceptedByteCallEntry
import Goose.Proofs.ConstructionAcceptedCheckedSequenceModule

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionRepresentation
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ExitExecution

theorem acceptedByteCallModule_allFuel (fuel : Nat) (config : EvalConfig) (accepted : AcceptedModule config)
    (original : Context) (entry : Impl) (context : Context) (helper : Impl)
    (localId contextId helperScope : Nat) (bytes : List UInt8) (statementOrigin origin : Nat)
    (globals : ∀ id, id < config.module.globals.size →
      ∃ descriptor, config.module.globals[id]? = some descriptor ∧ RecursiveGlobalInitializer descriptor)
    (originalAt : config.module.contexts[config.module.entry]? = some original)
    (entryAt : config.module.impls[original.impl]? = some entry)
    (entryStatements : entry.body.stmts = [.letS localId (.call contextId [] origin) statementOrigin])
    (entryTail : entry.body.value = none)
    (owner : (entry.vars[localId]?).map (·.ty) = some (.varr (.int .u8)))
    (contextAt : config.module.contexts[contextId]? = some context)
    (helperAt : config.module.impls[context.impl]? = some helper)
    (parameters : helper.params = #[])
    (results : helper.results = #[⟨.varr (.int .u8), .value, none⟩])
    (body : helper.body = ⟨helperScope, [], some (.bytes (.varr (.int .u8)) bytes origin)⟩)
    (absent : ∀ item ∈ helper.vars.toList, item.scope ≠ helperScope)
    (fits : bytes.length < 2 ^ 32) :
    ∃ initialized ambient types live regions,
      AcceptedWorld config initialized (Goose.Proofs.Exit.stepState (runModule fuel config .initial)) ambient types live regions [] ∧
      (match runModule fuel config .initial with | .ok .. | .stop .. => True | .escape .. | .jump .. => False) := by
  apply acceptedCheckedModuleFromGlobals_emptyRegions_allFuel fuel config accepted original entry
    (recursiveInitialGlobalsOutcome fuel config accepted globals) entryTail originalAt entryAt
  intro sequenceFuel frame activation before types live scopeInst world source phase sameImpl scopes activationEmpty channels position initialized limit bounded
  have singlePosition : SourcePosition accepted frame (.statements [.letS localId (.call contextId [] origin) statementOrigin]) := by
    simpa only [entryStatements] using position
  have singleOwner : (frame.source.impl.vars[localId]?).map (·.ty) = some (.varr (.int .u8)) := by
    simpa only [sameImpl] using owner
  have result := acceptedEntry_byteCall_statement sequenceFuel config accepted frame activation before types live entry.body.scope scopeInst
    localId contextId helperScope bytes statementOrigin origin context helper world source phase scopes channels singlePosition singleOwner
    contextAt helperAt parameters results body absent fits
  simpa only [entryStatements] using result

#print axioms acceptedByteCallModule_allFuel
end Goose.Proofs.ConstructionAcceptedExecution
