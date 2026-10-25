import Goose.Lower.Validation.ReplacementContentFlowSourceReadyTypedCall
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyCurrentReferenceArguments
import Goose.Lower.Validation.SourceRootShapeReads
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyReadDispatch
import Goose.GIR.ReplacementContentFlowProofsCanonicalFacts

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR
open Goose.Core.Sound Goose.GIR.ReplacementContentFlow.Model

inductive SourceReadyCaller (env : PEnv) : Prop
  | context (index : ContextId)
      (contextRow : env.mod.contexts[index]? = some env.ctx)
      (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl) : SourceReadyCaller env
  | global (implementation : env.impl = initImpl) (context : env.ctx = initContext) : SourceReadyCaller env

structure SourceReadyFunction where
  source : PEnv
  root : DemandNode
  func : Func
  types : Array (Option VTy)
  provenance : Prov
  upper : Prov
  state : State
  completed : LS
  moduleTypes : Array (Array (Option VTy))
  moduleProvenances : Array Prov
  resultRoots : Array (List RootRef)
  callees : Array State
  accepted : Core.validate source.mod = .ok ()
  caller : SourceReadyCaller source
  closed : close (lower source.mod) moduleTypes = some callees
  moduleFacts : ModuleCanonicalFacts (lower source.mod) moduleTypes moduleProvenances resultRoots
  moduleBounds : ModuleCanonicalWithin (lower source.mod) moduleTypes moduleProvenances callees
  frame : SourceReadyFrame (lower source.mod) callees func types state completed
  native : FunctionCanonicalFacts (lower source.mod) func types provenance resultRoots
  canonical : state.CanonicalWithin func types provenance
  growth : (start func types).Extends state
  occurrences : ∀ block ∈ func.blocks.toList, ∀ instruction ∈ block.insts,
    InstructionOccurrences source root func types upper instruction
  below : ∀ value, rootsAt provenance.vals value ⊆ rootsAt upper.vals value
  slotCount : func.slots.size = source.impl.vars.size
  slotSeeds : ∀ variableId localVar, source.impl.vars[variableId]? = some localVar →
    localVar.ty.isRefSlice = true → RootRef.param variableId ∈ rootsAt provenance.slots variableId

theorem SourceReadyFunction.readable (facts : SourceReadyFunction) {typingEnv : TEnv}
    (tables : SourceRootTables typingEnv facts.source) : SourceReadableEnvironment typingEnv := by
  cases facts.caller with
  | context index contextRow implementationRow =>
    apply SourceReadableEnvironment.implementation
    · simpa only [← tables.moduleEq] using facts.accepted
    · simpa only [← tables.moduleEq] using implementationRow
    · exact tables.variablesEq.symm
  | global implementation context =>
    apply SourceReadableEnvironment.empty
    · simpa only [← tables.moduleEq] using facts.accepted
    · rw [← tables.variablesEq, implementation]
      rfl

theorem SourceReadyFunction.sourceSlotCount (facts : SourceReadyFunction) {typingEnv : TEnv}
    (tables : SourceRootTables typingEnv facts.source) : facts.func.slots.size = typingEnv.vars.size := by
  rw [facts.slotCount, tables.variablesEq]

theorem SourceReadyFunction.sourceSlotSeeds (facts : SourceReadyFunction) {typingEnv : TEnv}
    (tables : SourceRootTables typingEnv facts.source) :
    ∀ variableId localVar, typingEnv.vars[variableId]? = some localVar →
      localVar.ty.isRefSlice = true → RootRef.param variableId ∈ rootsAt facts.provenance.slots variableId := by
  intro variableId localVar row reference
  exact facts.slotSeeds variableId localVar (by simpa only [tables.variablesEq] using row) reference

theorem SourceReadyFunction.read (facts : SourceReadyFunction) {typingEnv : TEnv}
    {place : Place} {type : Ty} {startOffset finishOffset : Nat} {results : List Ty} {before : LS}
    (tables : SourceRootTables typingEnv facts.source)
    (typed : Core.tyExpr typingEnv (.read place) startOffset = .ok (type, finishOffset))
    (generated : GeneratedBuilderState before)
    (native : SummaryPreservation.NativeRows facts.types
      (lowerExpr (.read place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2)
    (visible : VisibleSlotsReady typingEnv facts.state)
    (extension : (lowerExpr (.read place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext facts.completed)
    (allocated : (lowerExpr (.read place) (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ facts.completed.vals.size)
    (child : ∀ info finish, Core.tyPlace typingEnv place startOffset = .ok (info, finish) →
      GeneratedBuilderState before →
      SummaryPreservation.NativeRows facts.types
        (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2 →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2.Ext facts.completed →
      (lowerPlace place (lowerEnv typingEnv.mod typingEnv.vars results) before).2.vals.size ≤ facts.completed.vals.size →
      VisibleSlotsReady typingEnv facts.state →
      ValueReadyAt facts.state (lowerPlace place) (lowerEnv typingEnv.mod typingEnv.vars results) before) :
    ValueReadyAt facts.state (lowerExpr (.read place)) (lowerEnv typingEnv.mod typingEnv.vars results) before := by
  let env := lowerEnv typingEnv.mod typingEnv.vars results
  let address := lowerPlace place env before
  let loaded := Lower.emitDef (.load address.1) env address.2
  have actual : lowerExpr (.read place) env before = loaded := typedRead_run typed results before
  have advance : address.2.Adv loaded.2 := adv_emitDef
    (show Lower.emitDef (.load address.1) env address.2 = loaded from rfl)
  have childNative : SummaryPreservation.NativeRows facts.types address.2 := by
    apply native.of_prefix
    rw [actual]
    exact types_emitDef (.load address.1) env address.2 _ _ rfl
  have childExtension : address.2.Ext facts.completed := advance.ext.trans (by
    change loaded.2.Ext facts.completed
    rw [← actual]
    exact extension)
  have childAllocated : address.2.vals.size ≤ facts.completed.vals.size := Nat.le_trans advance.vals (by
    change loaded.2.vals.size ≤ facts.completed.vals.size
    rw [← actual]
    exact allocated)
  exact facts.frame.sourceRead facts.canonical facts.native.valuesSize facts.native.definitions facts.native.quiet
    facts.growth facts.occurrences facts.below (facts.sourceSlotSeeds tables) (facts.readable tables)
    typed generated native visible extension allocated
    (fun info finish source => child info finish source generated childNative childExtension childAllocated visible)

theorem SourceReadyFunction.emittedCall (facts : SourceReadyFunction)
    {env : LEnv} {before after : LS} {value : ValueId} {callee : FnId}
    {arguments : List ValueId} {origin : Option OriginId}
    (run : Lower.emitDef (.call callee arguments origin) env before = (value, after))
    (bounded : LiveBound before) (live : before.cur.isSome = true)
    (extension : after.Ext facts.completed) :
    CallOccurrence facts.source facts.root facts.func facts.upper value callee arguments origin := by
  cases current : before.cur with
  | none => simp [current] at live
  | some block =>
    obtain ⟨body, member, instruction⟩ := emitted_definition_retained current
      (bounded block current) run extension facts.frame.blocks
    exact (facts.occurrences body member _ instruction).2.2.1 value callee arguments origin rfl

#print axioms SourceReadyFunction.readable
#print axioms SourceReadyFunction.sourceSlotCount
#print axioms SourceReadyFunction.sourceSlotSeeds
#print axioms SourceReadyFunction.read
#print axioms SourceReadyFunction.emittedCall

end Goose.Lower.Validation.ReplacementContentFlowSource
