import Goose.Lower.DemandGeneratedSequencePrefix
import Goose.Lower.DemandScalarClear
import Goose.Lower.DemandControlProgressCursor
import Goose.Lower.DemandGeneratedExpressionStatementPrefix
import Goose.Lower.DemandControlStatementPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem ScalarClearCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env} {place : Place}
    {origin : OriginId} {state : St} {source : StmtSource cfg env (.clear place origin) state}
    {map : RetainedSsaMap} {cx : FnCtx} {runtime : DemandRuntimePoint}
    (cursor : ScalarClearCursor source map cx runtime) {term : Term}
    (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : False := by
  cases cursor with
  | atFrame frame progress =>
    cases progress with
    | inl effect =>
      obtain ⟨effect, instruction⟩ := effect
      cases instruction.symm.trans terminal
    | inr step =>
      obtain ⟨next, step⟩ := step
      exact maximal next (step fuel)

theorem ScalarClearPrefixCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env} {cx : FnCtx}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
    {runtime : DemandRuntimePoint} (cursor : ScalarClearPrefixCursor cx source before built initial start map required runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : False := by
  cases cursor with
  | clear cursor => exact cursor.excludes_maximal_terminal terminal maximal

theorem GeneratedControlProgressCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env} {cx : FnCtx}
    {expression : Expr} {state : St} {source : ExprSource cfg env expression state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
    {runtime : DemandRuntimePoint} (cursor : GeneratedControlProgressCursor cx source before built initial start map required runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : False := by
  cases cursor.progress with
  | inl instruction =>
    obtain ⟨id, op, instruction⟩ := instruction
    cases instruction.symm.trans terminal
  | inr step =>
    obtain ⟨next, step⟩ := step
    exact maximal next (step fuel)

theorem GeneratedExpressionStatementPrefixCursor.control_excludes_maximal_terminal
    {cfg : Cfg} {env : Env} {cx : FnCtx} {statement : Stmt} {state : St}
    {source : StmtSource cfg env statement state} {before built : LS} {initial : GIR.Frame} {start : Pt}
    {map required : RetainedSsaMap} {runtime : DemandRuntimePoint}
    (cursor : GeneratedExpressionStatementPrefixCursor (@GeneratedControlProgressCursor cfg env cx)
      source before built initial start map required runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : False := by
  cases cursor with
  | expression canonical cursor => exact cursor.excludes_maximal_terminal terminal maximal

theorem GeneratedGlobalClearPrefixCursor.excludes_terminal {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
    {runtime : DemandRuntimePoint} (cursor : GeneratedGlobalClearPrefixCursor cx results source before built initial start map required runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) : False := by
  cases cursor with
  | clear demanded instruction =>
    cases instruction with
    | inl definition =>
      obtain ⟨id, op, instruction⟩ := definition
      cases instruction.symm.trans terminal
    | inr effect =>
      obtain ⟨effect, instruction⟩ := effect
      cases instruction.symm.trans terminal

theorem ControlStatementPrefixCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {statement : Stmt} {state : St} {source : StmtSource cfg env statement state}
    {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap}
    {runtime : DemandRuntimePoint} (cursor : ControlStatementPrefixCursor cx results source before built initial start map required runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : False := by
  cases cursor with
  | clear cursor => exact cursor.excludes_terminal terminal
  | expression cursor => exact cursor.control_excludes_maximal_terminal terminal maximal

theorem GeneratedSequencePrefixCursor.excludes_maximal_terminal {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {map required : RetainedSsaMap} {before : LS} {loop : Option LoopCtx}
    {bindings : List (SlotId × ValueId × OriginId)} {block : Core.Block} {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {cursor : ∀ {statement : Stmt} {state : St}, StmtSource cfg env statement state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop}
    (excludes : ∀ {statement : Stmt} {state : St} (source : StmtSource cfg env statement state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      cursor source before built initial start map required runtime → ∀ {term : Term},
      instAt cx.fn runtime.point = some (.term term) → ∀ {fuel : Nat},
      (∀ next, ¬ DemandInstructionStep cx fuel runtime next) → False)
    {statements : List Stmt} {state : St} {source : StmtsSource cfg env statements state}
    {initial runtime : DemandRuntimePoint}
    (demanded : GeneratedSequencePrefixCursor cursor map required cx results before loop bindings block selected source initial runtime)
    {term : Term} (terminal : instAt cx.fn runtime.point = some (.term term)) {fuel : Nat}
    (maximal : ∀ next, ¬ DemandInstructionStep cx fuel runtime next) : False := by
  induction demanded with
  | head canonical owned occurrence rows coverage demanded => exact excludes _ demanded terminal maximal
  | tail canonical evaluated prefixSteps post demanded ih => exact ih terminal maximal

#print axioms ScalarClearCursor.excludes_maximal_terminal
#print axioms ScalarClearPrefixCursor.excludes_maximal_terminal
#print axioms GeneratedControlProgressCursor.excludes_maximal_terminal
#print axioms GeneratedExpressionStatementPrefixCursor.control_excludes_maximal_terminal
#print axioms GeneratedGlobalClearPrefixCursor.excludes_terminal
#print axioms ControlStatementPrefixCursor.excludes_maximal_terminal
#print axioms GeneratedSequencePrefixCursor.excludes_maximal_terminal
end Goose.Lower
