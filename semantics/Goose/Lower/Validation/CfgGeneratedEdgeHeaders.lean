import Goose.Lower.Validation.CfgGeneratedEdgeLoops

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem generated_edge_emptyHeader (env : LEnv) (context : Option LoopCtx) {body : BlockId → B Unit}
    (bodyEdges : ∀ header before result after, body header env before = (result, after) →
      GeneratedBuilderState before → LoopEdgeArguments context before → BuilderEdgeArguments before →
      EdgeArguments before header [] →
      GeneratedBuilderState after ∧ EdgeExtension before after ∧ BuilderEdgeArguments after) :
    GeneratedEdgeRun env context (do
      let (header, _) ← newBlock []
      emitTerm (.br header [])
      setCur (some header)
      body header) := by
  intro before result after run generated loop checked
  simp only [bind_eq] at run
  obtain ⟨⟨header, parameters⟩, allocated, allocateRun, ignored, closed, closeRun,
    ignored', selected, selectRun, bodyRun⟩ := run
  obtain ⟨allocatedGenerated, allocateExtension, allocatedChecked⟩ :=
    generated_edge_newBlock0 env context before _ allocated allocateRun generated loop checked
  have headerEdge := edge_newBlock0_target allocateRun
  obtain ⟨closedGenerated, closeExtension, closedChecked⟩ :=
    generated_edge_emitTerm_at (.br header []) env allocated closed ignored closeRun allocatedGenerated allocatedChecked headerEdge
  have closedHeader := headerEdge.extend closeExtension
  obtain ⟨selectedGenerated, selectExtension, selectedChecked⟩ :=
    generated_edge_setCur_at (some header) env closed selected ignored' selectRun closedGenerated closedChecked
      (by intro target same; have equal := Option.some.inj same; simpa [← equal] using closedHeader.bound)
  have beforeBody := allocateExtension.trans (closeExtension.trans selectExtension)
  obtain ⟨afterGenerated, bodyExtension, afterChecked⟩ :=
    bodyEdges header selected result after bodyRun selectedGenerated (loop.extend beforeBody) selectedChecked
      (closedHeader.extend selectExtension)
  exact ⟨afterGenerated, beforeBody.trans bodyExtension, afterChecked⟩

theorem generated_edge_counterHeader_at (env : LEnv) (context : Option LoopCtx)
    (ty : IntTy) (initial : ValueId) {body : BlockId → ValueId → B Unit}
    (bodyEdges : ∀ header counter before result after, body header counter env before = (result, after) →
      GeneratedBuilderState before → LoopEdgeArguments context before → BuilderEdgeArguments before →
      before.cur.isSome = true → CounterHeader before header ty counter →
      before.vals[counter]? = some (some (.data (.int ty))) →
      GeneratedBuilderState after ∧ EdgeExtension before after ∧ BuilderEdgeArguments after)
    (before after : LS) (result : Unit)
    (run : (do
      let (header, parameters) ← newBlock [.data (.int ty)]
      let counter := parameters.headD 0
      emitTerm (.br header [initial])
      setCur (some header)
      body header counter) env before = (result, after))
    (generated : GeneratedBuilderState before) (loop : LoopEdgeArguments context before)
    (checked : BuilderEdgeArguments before)
    (initialTyped : before.vals[initial]? = some (some (.data (.int ty)))) :
    GeneratedBuilderState after ∧ EdgeExtension before after ∧ BuilderEdgeArguments after := by
  simp only [bind_eq] at run
  obtain ⟨⟨header, parameters⟩, allocated, allocateRun, ignored, closed, closeRun,
    ignored', selected, selectRun, bodyRun⟩ := run
  obtain ⟨allocatedGenerated, allocateExtension, allocatedChecked⟩ :=
    generated_edge_newBlock1 env context (.data (.int ty)) before _ allocated allocateRun generated loop checked
  have initialEdge := edge_newBlock1_target allocateRun initialTyped
  have headerFrame := edge_newBlock1_counterHeader allocateRun
  have parameterTyped := edge_newBlock1_parameter allocateRun
  obtain ⟨closedGenerated, closeExtension, closedChecked⟩ :=
    generated_edge_emitTerm_at (.br header [initial]) env allocated closed ignored closeRun allocatedGenerated allocatedChecked initialEdge
  have closedFrame := headerFrame.extend closeExtension
  obtain ⟨selectedGenerated, selectExtension, selectedChecked⟩ :=
    generated_edge_setCur_at (some header) env closed selected ignored' selectRun closedGenerated closedChecked
      (by intro target same; have equal := Option.some.inj same; simpa [← equal] using closedFrame.bound)
  have beforeBody := allocateExtension.trans (closeExtension.trans selectExtension)
  have current : selected.cur.isSome = true := by
    rw [setCur_run] at selectRun
    obtain ⟨_, rfl⟩ := Prod.mk.inj selectRun
    rfl
  obtain ⟨afterGenerated, bodyExtension, afterChecked⟩ :=
    bodyEdges header (parameters.headD 0) selected result after bodyRun selectedGenerated (loop.extend beforeBody) selectedChecked
      current (closedFrame.extend selectExtension)
      (selectExtension.types _ _ (closeExtension.types _ _ parameterTyped))
  exact ⟨afterGenerated, beforeBody.trans bodyExtension, afterChecked⟩

end Goose.Lower.Validation
