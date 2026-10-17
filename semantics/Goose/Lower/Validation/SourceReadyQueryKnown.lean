import Goose.Lower.Validation.SourceReadyFactory
import Goose.GIR.ReplacementContentFlowProofsCallKnown
import Goose.Lower.Validation.ReplacementContentFlowSourceReadyCallees
import Goose.GIR.ReplacementContentFlowProofsSteps

namespace Goose.Lower.Validation.ReplacementContentFlowSource

open Goose.Core Goose.GIR SummaryPreservation
open Goose.GIR.ReplacementContentFlow.Model

theorem SourceReadyFunction.call_query_known (facts : SourceReadyFunction)
    (model : ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types).model =
      some facts.state)
    (observed : ∀ instruction ∈ facts.completed.insts,
      ReadyCallObservations (lower facts.source.mod) facts.func facts.state instruction)
    {block : GIR.Block} (blockMember : block ∈ facts.func.blocks.toList)
    {value calleeId : ValueId} {arguments : List ValueId} {origin : Option OriginId}
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts) :
    ∃ roots, ReplacementFunctionFlow.call
      ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types)
      calleeId arguments = some roots := by
  obtain ⟨typesEq, states, statesAt, _, checked⟩ :=
    ReplacementContentFlow.forFunction_model_checked model
  obtain ⟨moduleStates, moduleBuilt⟩ := accepted_factory_model facts.accepted
  have closure := (replacementContentFlow_model_checked moduleBuilt).2.1
  have sameStates : states = moduleStates := Option.some.inj (statesAt.symm.trans moduleBuilt)
  subst states
  obtain ⟨finiteStates, finiteClosed, finite, _⟩ := accepted_module_close_finite facts.accepted
  have finiteSame : finiteStates = moduleStates := Option.some.inj (finiteClosed.symm.trans closure)
  have supported : ModuleSupported (lower facts.source.mod) moduleStates := by
    rw [← finiteSame]
    exact finite.1
  obtain ⟨annotations, entries, addresses⟩ :=
    lower_canonical_factory_structure_of_accepted facts.accepted
  let moduleFacts := lower_canonical_facts_of_accepted facts.accepted
  have canonical := close_canonicalWithin moduleFacts annotations entries addresses closure
  obtain ⟨site⟩ := facts.native.calls block blockMember value calleeId arguments origin called
  obtain ⟨effects, effectsAt, _⟩ := canonical.1.2 calleeId site.callee site.calleeAt
  obtain ⟨touched, touchedKnown⟩ := close_touched_known moduleFacts annotations entries addresses
    closure site.calleeAt effectsAt
  have effectsSupported : effects.touched.Supported
      (atomUniverse (lower facts.source.mod) site.callee) :=
    (supported calleeId site.callee effects site.calleeAt effectsAt).touched
  have sourceEq : (replacementContentFlow (lower facts.source.mod)).source = lower facts.source.mod :=
    replacementContentFlow_source _
  have canonicalTypes : facts.types = facts.func.valueTypes (lower facts.source.mod) := by
    simpa only [sourceEq] using typesEq
  have check : check (lower facts.source.mod) facts.func facts.types facts.state = true := by
    rw [sourceEq] at checked
    rw [canonicalTypes]
    exact checked
  have checkedCall := Goose.GIR.ReplacementContentFlow.Model.check_instruction check blockMember called
  have arity : arguments.length = site.callee.params.length := by
    obtain ⟨callee, calleeAt, arity⟩ := facts.call_arity blockMember called
    have same : callee = site.callee := Option.some.inj (calleeAt.symm.trans site.calleeAt)
    simpa only [same] using arity
  have emitted := finishBlocks_instruction_member (facts.frame.blocks ▸ blockMember) called
  have available := observed (.def value (.call calleeId arguments origin)) emitted value calleeId
    arguments origin rfl site.callee site.calleeAt
  exact ReplacementContentFlow.forFunction_call_known model moduleBuilt blockMember called
    site.calleeAt effectsAt arity touchedKnown effectsSupported available

theorem SourceReadyFunction.call_value_known (facts : SourceReadyFunction)
    (model : ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types).model =
      some facts.state)
    (observed : ∀ instruction ∈ facts.completed.insts,
      ReadyCallObservations (lower facts.source.mod) facts.func facts.state instruction)
    {block : GIR.Block} (blockMember : block ∈ facts.func.blocks.toList)
    {value calleeId : ValueId} {arguments : List ValueId} {origin : Option OriginId}
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts) :
    ∃ roots, ReplacementFunctionFlow.value
      ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types) value = some roots := by
  obtain ⟨site⟩ := facts.native.calls block blockMember value calleeId arguments origin called
  have emitted := finishBlocks_instruction_member (facts.frame.blocks ▸ blockMember) called
  have available := observed _ emitted value calleeId arguments origin rfl site.callee site.calleeAt
  have arity : arguments.length = site.callee.params.length := by
    obtain ⟨callee, calleeAt, arity⟩ := facts.call_arity blockMember called
    have same : callee = site.callee := Option.some.inj (calleeAt.symm.trans site.calleeAt)
    simpa only [same] using arity
  have argumentsReady : ∀ (index : Nat) (argument : ValueId),
      arguments[index]? = some argument → flowAt facts.state.values argument ≠ .pending := by
    intro index argument row
    have indexBound : index < site.callee.params.length := by
      have argumentBound := (List.getElem?_eq_some_iff.mp row).1
      omega
    obtain ⟨selected, roots, selectedAt, normalized⟩ := available.arguments index indexBound
    have same : selected = argument := Option.some.inj (selectedAt.symm.trans row)
    rw [same] at normalized
    intro pending
    simp [pending, normalize] at normalized
  have contentsReady : ∀ (index : Nat) (argument : ValueId),
      (site.callee.roots.contents.find? (·.1 == index)).isSome = true →
      arguments[index]? = some argument →
      content facts.func facts.state (flowAt facts.state.values argument) ≠ .pending := by
    intro index argument declared row
    exact facts.observed_contents observed blockMember called site.calleeAt declared row
  obtain ⟨effects, effectsAt, effectsCanonical⟩ :=
    facts.moduleBounds.2 calleeId site.callee site.calleeAt
  have rootFacts := facts.moduleFacts.functions calleeId site.callee site.calleeAt
  have fixed := facts.frame.fixed_instruction (LS.Ext.refl facts.completed) emitted
  have bounded := facts.native.definitions block blockMember value (.call calleeId arguments origin) called
  have produced : (if valRefLike facts.types value then
      (callState (lower facts.source.mod) facts.callees facts.func
        (touchValues facts.types facts.state (accessOperands (.def value (.call calleeId arguments origin))))
        calleeId arguments).1
      else .known []) ≠ .pending := by
    by_cases reference : valRefLike facts.types value = true
    · have callResults := facts.native.callResults block blockMember value calleeId arguments origin
        called site.callee site.calleeAt
      rcases callResults with ⟨empty, unit⟩ | ⟨type, results, typed⟩
      · have scalar : valRefLike facts.types value = false := by
          simp [valRefLike, unit, VTy.refLike, Ty.isRefLike]
        rw [scalar] at reference
        cases reference
      · have typeReference : type.isRefLike = true := by
          simpa only [valRefLike, typed, Option.some.injEq, VTy.refLike] using reference
        have callReady := call_result_ready_of_closed_callee facts.closed site.calleeAt effectsAt
          effectsCanonical rootFacts.roots.closed results typeReference argumentsReady contentsReady
        simp only [reference]
        rw [callState_result_touchValues]
        exact callReady
    · simp [reference]
  have stateBound : value < facts.state.values.size := by
    rw [facts.canonical.shape.values]
    exact bounded
  have valueReady := fixed_step_def_value_ready fixed stateBound produced
  obtain ⟨roots, normalized, _⟩ :=
    (facts.canonical.values value stateBound).actual facts.native.roots.closed valueReady
  rw [ReplacementFunctionFlow.value_model]
  simp only [model, Option.bind_some]
  exact ⟨roots, normalized⟩

theorem SourceReadyFunction.load_value_known (facts : SourceReadyFunction)
    (model : ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types).model =
      some facts.state)
    (ready : SourceReadyBuilder facts.state facts.completed)
    {block : GIR.Block} (blockMember : block ∈ facts.func.blocks.toList)
    {value address : ValueId}
    (loaded : Inst.def value (.load address) ∈ block.insts) :
    ∃ roots, ReplacementFunctionFlow.value
      ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types) value = some roots := by
  have emitted := finishBlocks_instruction_member (facts.frame.blocks ▸ blockMember) loaded
  have bounded := facts.native.definitions block blockMember value (.load address) loaded
  have valueBound : value < facts.state.values.size := by
    rw [facts.canonical.shape.values]
    exact bounded
  have valueReady : flowAt facts.state.values value ≠ .pending :=
    (ready _ emitted).2 value (by simp [loadedResults])
  obtain ⟨roots, normalized, _⟩ :=
    (facts.canonical.values value valueBound).actual facts.native.roots.closed valueReady
  rw [ReplacementFunctionFlow.value_model]
  simp only [model, Option.bind_some]
  exact ⟨roots, normalized⟩

theorem accepted_context_factory_call_query_known {module : Core.Module} {context : Context} {impl : Impl}
    {index : Nat} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {block : GIR.Block} (member : block ∈ (lowerContextAt module context impl).blocks.toList)
    {value calleeId : ValueId} {arguments : List ValueId} {origin : Option OriginId}
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts) :
    ∃ roots, (replacementQueries (lower module) (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))).callRoots calleeId arguments =
        some roots := by
  obtain ⟨facts, sourceEq, functionEq, typesEq, _, model, _, observed⟩ :=
    accepted_context_factory_ready_inputs accepted contextAt implAt
  have actualModel : ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types).model =
      some facts.state := by simpa only [sourceEq] using model
  obtain ⟨roots, known⟩ := facts.call_query_known actualModel observed (functionEq ▸ member) called
  refine ⟨roots, ?_⟩
  change ReplacementFunctionFlow.call
    ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))) calleeId arguments = some roots
  simpa only [sourceEq, functionEq, typesEq] using known

theorem accepted_context_factory_call_value_known {module : Core.Module} {context : Context} {impl : Impl}
    {index : Nat} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {block : GIR.Block} (member : block ∈ (lowerContextAt module context impl).blocks.toList)
    {value calleeId : ValueId} {arguments : List ValueId} {origin : Option OriginId}
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts) :
    ∃ roots, (replacementQueries (lower module) (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))).value value = some roots := by
  obtain ⟨facts, sourceEq, functionEq, typesEq, _, model, _, observed⟩ :=
    accepted_context_factory_ready_inputs accepted contextAt implAt
  have actualModel : ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types).model =
      some facts.state := by simpa only [sourceEq] using model
  obtain ⟨roots, known⟩ := facts.call_value_known actualModel observed (functionEq ▸ member) called
  have bounded : value < facts.func.numValues := facts.native.definitions _ (functionEq ▸ member)
    value (.call calleeId arguments origin) called
  have actualBound : value < (lowerContextAt module context impl).numValues := by
    simpa only [functionEq] using bounded
  refine ⟨roots, ?_⟩
  rw [replacementQueries_value (lower module) (lowerContextAt module context impl)
    ((lowerContextAt module context impl).valueTypes (lower module)) value actualBound]
  simpa only [sourceEq, functionEq, typesEq] using known

theorem accepted_context_factory_load_value_known {module : Core.Module} {context : Context} {impl : Impl}
    {index : Nat} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {block : GIR.Block} (member : block ∈ (lowerContextAt module context impl).blocks.toList)
    {value address : ValueId}
    (loaded : Inst.def value (.load address) ∈ block.insts) :
    ∃ roots, (replacementQueries (lower module) (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))).value value = some roots := by
  obtain ⟨facts, sourceEq, functionEq, typesEq, _, model, ready, _⟩ :=
    accepted_context_factory_ready_inputs accepted contextAt implAt
  have actualModel : ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types).model =
      some facts.state := by simpa only [sourceEq] using model
  obtain ⟨roots, known⟩ := facts.load_value_known actualModel ready (functionEq ▸ member) loaded
  have bounded := facts.native.definitions _ (functionEq ▸ member) value (.load address) loaded
  have actualBound : value < (lowerContextAt module context impl).numValues := by
    simpa only [functionEq] using bounded
  refine ⟨roots, ?_⟩
  rw [replacementQueries_value (lower module) (lowerContextAt module context impl)
    ((lowerContextAt module context impl).valueTypes (lower module)) value actualBound]
  simpa only [sourceEq, functionEq, typesEq] using known

theorem accepted_global_factory_call_query_known {module : Core.Module} {global : Core.Global}
    {index : Nat} (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[index]? = some global)
    {block : GIR.Block} (member : block ∈ (lowerGlobal module global).init.blocks.toList)
    {value calleeId : ValueId} {arguments : List ValueId} {origin : Option OriginId}
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts) :
    ∃ roots, (replacementQueries (lower module) (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))).callRoots calleeId arguments =
        some roots := by
  obtain ⟨facts, sourceEq, functionEq, typesEq, _, model, _, observed⟩ :=
    accepted_global_factory_ready_inputs accepted globalAt
  have actualModel : ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types).model =
      some facts.state := by simpa only [sourceEq] using model
  obtain ⟨roots, known⟩ := facts.call_query_known actualModel observed (functionEq ▸ member) called
  refine ⟨roots, ?_⟩
  change ReplacementFunctionFlow.call
    ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))) calleeId arguments = some roots
  simpa only [sourceEq, functionEq, typesEq] using known

theorem accepted_global_factory_call_value_known {module : Core.Module} {global : Core.Global}
    {index : Nat} (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[index]? = some global)
    {block : GIR.Block} (member : block ∈ (lowerGlobal module global).init.blocks.toList)
    {value calleeId : ValueId} {arguments : List ValueId} {origin : Option OriginId}
    (called : Inst.def value (.call calleeId arguments origin) ∈ block.insts) :
    ∃ roots, (replacementQueries (lower module) (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))).value value = some roots := by
  obtain ⟨facts, sourceEq, functionEq, typesEq, _, model, _, observed⟩ :=
    accepted_global_factory_ready_inputs accepted globalAt
  have actualModel : ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types).model =
      some facts.state := by simpa only [sourceEq] using model
  obtain ⟨roots, known⟩ := facts.call_value_known actualModel observed (functionEq ▸ member) called
  have bounded : value < facts.func.numValues := facts.native.definitions _ (functionEq ▸ member)
    value (.call calleeId arguments origin) called
  have actualBound : value < (lowerGlobal module global).init.numValues := by
    simpa only [functionEq] using bounded
  refine ⟨roots, ?_⟩
  rw [replacementQueries_value (lower module) (lowerGlobal module global).init
    ((lowerGlobal module global).init.valueTypes (lower module)) value actualBound]
  simpa only [sourceEq, functionEq, typesEq] using known

theorem accepted_global_factory_load_value_known {module : Core.Module} {global : Core.Global}
    {index : Nat} (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[index]? = some global)
    {block : GIR.Block} (member : block ∈ (lowerGlobal module global).init.blocks.toList)
    {value address : ValueId}
    (loaded : Inst.def value (.load address) ∈ block.insts) :
    ∃ roots, (replacementQueries (lower module) (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))).value value = some roots := by
  obtain ⟨facts, sourceEq, functionEq, typesEq, _, model, ready, _⟩ :=
    accepted_global_factory_ready_inputs accepted globalAt
  have actualModel : ((replacementContentFlow (lower facts.source.mod)).forFunction facts.func facts.types).model =
      some facts.state := by simpa only [sourceEq] using model
  obtain ⟨roots, known⟩ := facts.load_value_known actualModel ready (functionEq ▸ member) loaded
  have bounded := facts.native.definitions _ (functionEq ▸ member) value (.load address) loaded
  have actualBound : value < (lowerGlobal module global).init.numValues := by
    simpa only [functionEq] using bounded
  refine ⟨roots, ?_⟩
  rw [replacementQueries_value (lower module) (lowerGlobal module global).init
    ((lowerGlobal module global).init.valueTypes (lower module)) value actualBound]
  simpa only [sourceEq, functionEq, typesEq] using known

theorem accepted_context_factory_operand_value {module : Core.Module} {context : Context} {impl : Impl}
    {index : Nat} (accepted : Core.validate module = .ok ())
    (contextAt : module.contexts[index]? = some context)
    (implAt : module.impls[context.impl]? = some impl)
    {block : GIR.Block} (member : block ∈ (lowerContextAt module context impl).blocks.toList)
    {instruction : Inst} (instructionMember : instruction ∈ block.insts)
    {value : ValueId} (use : value ∈ instruction.uses) :
    ∃ roots, ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))).value value = some roots := by
  obtain ⟨facts, sourceEq, functionEq, typesEq, completedEq, model, ready, observed⟩ :=
    accepted_context_factory_ready_inputs accepted contextAt implAt
  obtain ⟨roots, known⟩ := facts.normalized_operands ready (functionEq ▸ member) instructionMember use
  refine ⟨roots, ?_⟩
  have actualModel : ((replacementContentFlow (lower module)).forFunction (lowerContextAt module context impl)
      ((lowerContextAt module context impl).valueTypes (lower module))).model = some facts.state := by
    simpa only [functionEq, typesEq] using model
  rw [ReplacementFunctionFlow.value_model, actualModel]
  change normalize (lowerContextAt module context impl) (flowAt facts.state.values value) = some roots
  simpa only [functionEq] using known

theorem accepted_global_factory_operand_value {module : Core.Module} {global : Core.Global}
    {index : Nat} (accepted : Core.validate module = .ok ())
    (globalAt : module.globals[index]? = some global)
    {block : GIR.Block} (member : block ∈ (lowerGlobal module global).init.blocks.toList)
    {instruction : Inst} (instructionMember : instruction ∈ block.insts)
    {value : ValueId} (use : value ∈ instruction.uses) :
    ∃ roots, ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))).value value = some roots := by
  obtain ⟨facts, sourceEq, functionEq, typesEq, completedEq, model, ready, observed⟩ :=
    accepted_global_factory_ready_inputs accepted globalAt
  obtain ⟨roots, known⟩ := facts.normalized_operands ready (functionEq ▸ member) instructionMember use
  refine ⟨roots, ?_⟩
  have actualModel : ((replacementContentFlow (lower module)).forFunction (lowerGlobal module global).init
      ((lowerGlobal module global).init.valueTypes (lower module))).model = some facts.state := by
    simpa only [functionEq, typesEq] using model
  rw [ReplacementFunctionFlow.value_model, actualModel]
  change normalize (lowerGlobal module global).init (flowAt facts.state.values value) = some roots
  simpa only [functionEq] using known

#print axioms accepted_context_factory_operand_value
#print axioms accepted_global_factory_operand_value
#print axioms SourceReadyFunction.call_query_known
#print axioms accepted_context_factory_call_query_known
#print axioms accepted_global_factory_call_query_known
#print axioms SourceReadyFunction.call_value_known
#print axioms accepted_context_factory_call_value_known
#print axioms accepted_global_factory_call_value_known

end Goose.Lower.Validation.ReplacementContentFlowSource
