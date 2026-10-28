import Goose.Proofs.ConstructionGhostSourceMutual

namespace Goose.Proofs.ConstructionGhostArgumentModule
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual

private def sourceContext : Context := ⟨1, "source", [], [], []⟩
private def targetContext : Context := ⟨2, "target", [], [], []⟩
private def entryContext : Context := ⟨0, "entry", [], [], []⟩
private def sourceImplementation : Impl := ⟨"source", #[], #[], #[], .mk 1 [.print [.text "x"] 0] none, .unknown⟩
private def targetImplementation : Impl := ⟨"target", #[⟨0, .byValue⟩, ⟨1, .byValue⟩], #[], #[],
  .mk 2 [.print [.text "y"] 0] none, .unknown⟩
private def arguments : List Arg := [.byVal (.call 1 [] 0), .byVal (.lit .i64 9)]
private def entryImplementation : Impl := ⟨"entry", #[], #[], #[], .mk 0 [.expr (.call 2 arguments 0) 0] none, .unknown⟩
private def config : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[entryImplementation, sourceImplementation, targetImplementation],
    #[entryContext, sourceContext, targetContext], 0, #[], #[], #[]⟩⟩
private def entryEnvironment : RuntimeActivation := ⟨0, 0, #[], [], []⟩
private def stepState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem sourceSupported (environment : RuntimeActivation) : SupportedOperation config (.call environment 1 0) := by
  have body : ∀ bodyEnvironment, SupportedOperation config (.statements bodyEnvironment [.print [.text "x"] 0]) := by
    intro bodyEnvironment
    exact .sequence bodyEnvironment (.printText bodyEnvironment "x" 0) (.empty bodyEnvironment)
  apply SupportedOperation.call environment 1 0 sourceContext sourceImplementation
  · rfl
  · rfl
  · rfl
  · rfl
  · intro act
    exact .activation _ 1 _ 0 body

private theorem targetSupported (environment : RuntimeActivation) : SupportedOperation config (.callWith environment 2 arguments 0) := by
  have args : SupportedOperation config (.arguments environment targetImplementation.vars targetImplementation.params.toList arguments) := by
    unfold targetImplementation arguments
    exact .argumentValue _ _ _ _ _ _
      (.valueCall environment 1 0 sourceContext sourceImplementation rfl rfl rfl (sourceSupported environment))
      (.argumentValue _ _ _ _ _ _ (.value _ (.integer .i64 9)) (.argumentsDone _ _))
  have body : ∀ bodyEnvironment, SupportedOperation config (.statements bodyEnvironment [.print [.text "y"] 0]) := by
    intro bodyEnvironment
    exact .sequence bodyEnvironment (.printText bodyEnvironment "y" 0) (.empty bodyEnvironment)
  apply SupportedOperation.callWith environment 2 arguments 0 targetContext targetImplementation
  · rfl
  · rfl
  · rfl
  · exact args
  · intro act pre
    exact .boundActivation _ pre 2 _ 0 body

private theorem entrySupported : SupportedOperation config (.call entryEnvironment 0 0) := by
  have body : ∀ bodyEnvironment, SupportedOperation config (.statements bodyEnvironment [.expr (.call 2 arguments 0) 0]) := by
    intro bodyEnvironment
    exact .sequence bodyEnvironment (.expression bodyEnvironment 0
      (.valueCallWith bodyEnvironment 2 arguments 0 targetContext targetImplementation rfl rfl rfl (targetSupported bodyEnvironment)))
      (.empty bodyEnvironment)
  apply SupportedOperation.call entryEnvironment 0 0 entryContext entryImplementation
  · rfl
  · rfl
  · rfl
  · rfl
  · intro act
    exact .activation _ 0 _ 0 body

def moduleCallResult : ExecutionStep (List Carrier) → ExecutionStep Unit
  | .ok carriers state => publishCarriers 0 carriers state
  | .stop reason state => .stop reason state
  | .escape address carriers state => .escape address carriers state
  | .jump target kind state => .jump target kind state

theorem moduleHistory (fuel : Nat) : ∃ outcome,
    SourceHistory config fuel [] (.call entryEnvironment 0 0) .initial outcome ∧
    runModule fuel config .initial = moduleCallResult outcome := by
  have history := history_exists fuel config (.call entryEnvironment 0 0) [] .initial entrySupported
  refine ⟨_, history, ?_⟩
  simp only [runModule, config, entryContext, entryImplementation, Array.size_empty, List.range_zero,
    initGlobals, getImplementation, Array.getElem?_singleton, channelsFor, Array.toList_empty, List.mapM_nil, bind, pure]
  change (invokeCall fuel config entryEnvironment 0 [] [] 0 >>= fun carriers => publishCarriers 0 carriers) .initial =
    moduleCallResult (invokeCall fuel config entryEnvironment 0 [] [] 0 .initial)
  simp only [bind, moduleCallResult]
  cases invokeCall fuel config entryEnvironment 0 [] [] 0 .initial <;> rfl

theorem moduleWitness : ∃ after,
    runModule 50 config .initial = .ok () after ∧ after.construction.stdout.data.toList = [120, 10, 121, 10] ∧
    after.nextAct = 3 ∧ ∃ outcome, SourceHistory config 50 [] (.call entryEnvironment 0 0) .initial outcome ∧
      runModule 50 config .initial = moduleCallResult outcome := by
  obtain ⟨outcome, history, execution⟩ := moduleHistory 50
  refine ⟨stepState (runModule 50 config .initial), ?_, ?_, ?_, outcome, history, execution⟩ <;>
    unfold stepState config entryContext sourceContext targetContext entryImplementation sourceImplementation targetImplementation arguments <;> cbv

#print axioms moduleHistory
#print axioms moduleWitness
end Goose.Proofs.ConstructionGhostArgumentModule
