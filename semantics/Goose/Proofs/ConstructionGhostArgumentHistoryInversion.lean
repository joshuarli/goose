import Goose.Proofs.ConstructionGhostCallArgumentEvents
import Goose.Proofs.ConstructionGhostStatementPaths

namespace Goose.Proofs.ConstructionGhostArgumentHistoryInversion
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual
open Goose.Proofs.ConstructionGhostCallArgumentEvents Goose.Proofs.ConstructionGhostCallArguments
open Goose.Proofs.ConstructionGhostArguments Goose.Proofs.ConstructionExecution
open Goose.Proofs.ConstructionGhostStatementPaths

def argumentsSyntax : SourceOperation α → Option (RuntimeActivation × Array LocalVar × List Param × List Arg)
  | .arguments environment vars parameters arguments => some (environment, vars, parameters, arguments)
  | _ => none

theorem byValue_head_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (vars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (operand : Expr) (arguments : List Arg)
    (fuelEq : fuel = sourceFuel + 1)
    (operationEq : argumentsSyntax operation = some (environment, vars, parameter :: parameters, .byVal operand :: arguments)) :
    SourceHistory config sourceFuel (path ++ [0]) (.value environment operand) before
      (evalValue sourceFuel config environment operand before) := by
  cases history <;> simp_all [argumentsSyntax]
  case argumentValue =>
    rename_i child
    have actual := child.sound
    simp only [execute] at actual
    rw [actual]
    exact child

theorem arguments_tail_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (vars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (argument : Arg) (arguments : List Arg) (value : Value) (middle : ExecutionState)
    (fuelEq : fuel = sourceFuel + 1)
    (operationEq : argumentsSyntax operation = some (environment, vars, parameter :: parameters, argument :: arguments))
    (head : argumentValue sourceFuel config environment vars parameter argument before = .ok value middle) :
    SourceHistory config sourceFuel (path ++ [1]) (.arguments environment vars parameters arguments) middle
      (evalArguments sourceFuel config environment vars parameters arguments middle) := by
  cases history <;> simp_all [argumentsSyntax]
  case argumentValue =>
    rename_i operand args out tail child
    have same : argument = .byVal operand := by simp_all
    subst argument
    have actual := child.sound
    simp only [execute] at actual
    simp only [argumentValue] at head
    exact tail value middle (actual.symm.trans head)
  case argumentReference =>
    rename_i mutability place args child tail
    have same : argument = .byRef mutability place := by simp_all
    subst argument
    simp only [argumentValue, bind, pure] at head
    cases placed : evalPlace sourceFuel config environment place before <;> simp_all

theorem byValue_head_source (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (vars : Array LocalVar) (parameter : Param) (parameters : List Param)
    (operand : Expr) (arguments : List Arg) (before : ExecutionState) (outcome : ExecutionStep (List Value))
    (visits : List ArgumentInvocation) (callResult : ExecutionStep (List Carrier))
    (history : SourceHistory config (fuel + 1) path (.arguments environment vars (parameter :: parameters) (.byVal operand :: arguments)) before outcome)
    (replay : ArgumentReplay config environment vars (fuel + 1) 0 (parameter :: parameters) (.byVal operand :: arguments) before outcome visits)
    (callPrefix : ∀ visit ∈ visits, EventPrefix (Goose.Proofs.Exit.stepState visit.outcome).construction.events
      (Goose.Proofs.Exit.stepState callResult).construction.events) :
    SourceHistory config fuel (path ++ [0]) (.value environment operand) before (evalValue fuel config environment operand before) ∧
    EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment operand before)).construction.events
      (Goose.Proofs.Exit.stepState callResult).construction.events := by
  refine ⟨byValue_head_history history fuel environment vars parameter parameters operand arguments rfl rfl, ?_⟩
  cases replay with
  | next head tail =>
      have kept := callPrefix _ (List.mem_cons_self)
      simp only [argumentValue] at head
      rw [head]
      exact kept
  | stopped head | escaped head | jumped head =>
      have kept := callPrefix _ (List.mem_singleton_self _)
      simp only [argumentValue] at head
      rw [head]
      exact kept

theorem byValue_head_invokeCall (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (context : Goose.Core.ContextId) (parameter : Param) (parameters : List Param)
    (operand : Expr) (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
    (callBefore before : ExecutionState) (id : Goose.Core.ImplId) (implementation : Impl)
    (callableChannels : List Channel) (outcome : ExecutionStep (List Value)) (visits : List ArgumentInvocation)
    (params : implementation.params.toList = parameter :: parameters)
    (history : SourceHistory config (fuel + 1) path (.arguments environment implementation.vars (parameter :: parameters) (.byVal operand :: arguments)) before outcome)
    (replay : ArgumentReplay config environment implementation.vars (fuel + 1) 0 (parameter :: parameters) (.byVal operand :: arguments) before outcome visits)
    (execution : invokeCall (fuel + 2) config environment context (.byVal operand :: arguments) channels origin callBefore =
      callArgumentsContinuation (fuel + 1) config id implementation channels callableChannels origin outcome) :
    SourceHistory config fuel (path ++ [0]) (.value environment operand) before (evalValue fuel config environment operand before) ∧
    EventPrefix (Goose.Proofs.Exit.stepState (evalValue fuel config environment operand before)).construction.events
      (Goose.Proofs.Exit.stepState (invokeCall (fuel + 2) config environment context (.byVal operand :: arguments) channels origin callBefore)).construction.events := by
  apply byValue_head_source fuel config environment path implementation.vars parameter parameters operand arguments before outcome visits _ history replay
  intro visit member
  apply invokeCall_argumentVisitPrefix (fuel + 1) config environment context (.byVal operand :: arguments) channels origin
    callBefore before id implementation callableChannels outcome visits visit
  · simpa [params] using replay
  · exact member
  · exact execution

theorem argumentReplay_byValuePaths {config : EvalConfig} {environment : RuntimeActivation} {vars : Array LocalVar}
    {fuel offset : Nat} {parameters : List Param} {arguments : List Arg} {before : ExecutionState}
    {outcome : ExecutionStep (List Value)} {visits : List ArgumentInvocation}
    (replay : ArgumentReplay config environment vars fuel offset parameters arguments before outcome visits) :
    ∀ path, SourceHistory config fuel path (.arguments environment vars parameters arguments) before outcome →
      ∀ visit ∈ visits, ∀ operand, visit.argument = .byVal operand →
        ∃ suffix, StatementPath offset suffix visit.ordinal ∧
          SourceHistory config visit.fuel (path ++ suffix) (.value environment operand) visit.before
            (evalValue visit.fuel config environment operand visit.before) := by
  induction replay with
  | timeout | done | arityLeft | arityRight => intros; simp_all
  | @next fuel offset parameter parameters argument arguments before middle value outcome visits head tail ih =>
      intro path history visit member operand byValue
      simp only [List.mem_cons] at member
      rcases member with same | later
      · subst visit
        simp only at byValue
        subst argument
        exact ⟨[0], .here offset, byValue_head_history history fuel environment vars parameter parameters operand arguments rfl rfl⟩
      · have tailHistory := arguments_tail_history history fuel environment vars parameter parameters argument arguments value middle rfl rfl head
        rw [tail.sound] at tailHistory
        obtain ⟨suffix, suffixPath, child⟩ := ih (path ++ [1]) tailHistory visit later operand byValue
        exact ⟨1 :: suffix, .next offset visit.ordinal suffix suffixPath, by simpa [List.append_assoc] using child⟩
  | @stopped fuel offset parameter parameters argument arguments before after reason head =>
      intro path history visit member operand byValue
      simp only [List.mem_singleton] at member
      subst visit
      simp only at byValue
      subst argument
      exact ⟨[0], .here offset, byValue_head_history history fuel environment vars parameter parameters operand arguments rfl rfl⟩
  | @escaped fuel offset parameter parameters argument arguments before after address carriers head =>
      intro path history visit member operand byValue
      simp only [List.mem_singleton] at member
      subst visit
      simp only at byValue
      subst argument
      exact ⟨[0], .here offset, byValue_head_history history fuel environment vars parameter parameters operand arguments rfl rfl⟩
  | @jumped fuel offset parameter parameters argument arguments before after target kind head =>
      intro path history visit member operand byValue
      simp only [List.mem_singleton] at member
      subst visit
      simp only at byValue
      subst argument
      exact ⟨[0], .here offset, byValue_head_history history fuel environment vars parameter parameters operand arguments rfl rfl⟩

theorem argumentReplay_visitExecutes {config : EvalConfig} {environment : RuntimeActivation} {vars : Array LocalVar}
    {fuel offset : Nat} {parameters : List Param} {arguments : List Arg} {before : ExecutionState}
    {outcome : ExecutionStep (List Value)} {visits : List ArgumentInvocation}
    (replay : ArgumentReplay config environment vars fuel offset parameters arguments before outcome visits)
    (visit : ArgumentInvocation) (member : visit ∈ visits) :
    argumentValue visit.fuel config environment vars visit.parameter visit.argument visit.before = visit.outcome := by
  induction replay with
  | timeout | done | arityLeft | arityRight => simp at member
  | next head tail ih =>
      simp only [List.mem_cons] at member
      rcases member with same | later
      · subst visit; exact head
      · exact ih later
  | stopped head | escaped head | jumped head =>
      simp only [List.mem_singleton] at member
      subst visit
      exact head

theorem argumentReplay_byValueSources {config : EvalConfig} {environment : RuntimeActivation} {vars : Array LocalVar}
    {fuel offset : Nat} {parameters : List Param} {arguments : List Arg} {before : ExecutionState}
    {outcome : ExecutionStep (List Value)} {visits : List ArgumentInvocation}
    (replay : ArgumentReplay config environment vars fuel offset parameters arguments before outcome visits)
    (path : List Nat) (history : SourceHistory config fuel path (.arguments environment vars parameters arguments) before outcome)
    (visit : ArgumentInvocation) (member : visit ∈ visits) (operand : Expr) (byValue : visit.argument = .byVal operand) :
    ∃ suffix, StatementPath offset suffix visit.ordinal ∧
      SourceHistory config visit.fuel (path ++ suffix) (.value environment operand) visit.before
        (evalValue visit.fuel config environment operand visit.before) ∧
      EventPrefix (Goose.Proofs.Exit.stepState (evalValue visit.fuel config environment operand visit.before)).construction.events
        (Goose.Proofs.Exit.stepState outcome).construction.events := by
  obtain ⟨suffix, suffixPath, child⟩ := argumentReplay_byValuePaths replay path history visit member operand byValue
  have actual := argumentReplay_visitExecutes replay visit member
  rw [byValue] at actual
  simp only [argumentValue] at actual
  have kept := argumentReplay_visitPrefix replay visit member
  refine ⟨suffix, suffixPath, child, ?_⟩
  rw [actual]
  exact kept

theorem invokeCall_byValueSource (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (path : List Nat) (context : Goose.Core.ContextId) (arguments : List Arg) (channels : List Channel)
    (origin : Goose.Core.OriginId) (callBefore before : ExecutionState) (id : Goose.Core.ImplId)
    (implementation : Impl) (callableChannels : List Channel) (outcome : ExecutionStep (List Value))
    (visits : List ArgumentInvocation) (visit : ArgumentInvocation) (operand : Expr)
    (history : SourceHistory config fuel path (.arguments environment implementation.vars implementation.params.toList arguments) before outcome)
    (replay : ArgumentReplay config environment implementation.vars fuel 0 implementation.params.toList arguments before outcome visits)
    (member : visit ∈ visits) (byValue : visit.argument = .byVal operand)
    (execution : invokeCall (fuel + 1) config environment context arguments channels origin callBefore =
      callArgumentsContinuation fuel config id implementation channels callableChannels origin outcome) :
    ∃ suffix, StatementPath 0 suffix visit.ordinal ∧
      SourceHistory config visit.fuel (path ++ suffix) (.value environment operand) visit.before
        (evalValue visit.fuel config environment operand visit.before) ∧
      EventPrefix (Goose.Proofs.Exit.stepState (evalValue visit.fuel config environment operand visit.before)).construction.events
        (Goose.Proofs.Exit.stepState (invokeCall (fuel + 1) config environment context arguments channels origin callBefore)).construction.events := by
  obtain ⟨suffix, suffixPath, child, kept⟩ := argumentReplay_byValueSources replay path history visit member operand byValue
  refine ⟨suffix, suffixPath, child, ?_⟩
  rw [execution]
  exact eventPrefix_trans _ _ _ kept (callArgumentsContinuation_resultPrefix fuel config id implementation channels callableChannels origin outcome)

#print axioms invokeCall_byValueSource
#print axioms argumentReplay_visitExecutes
#print axioms argumentReplay_byValueSources
#print axioms argumentReplay_byValuePaths
#print axioms arguments_tail_history
#print axioms byValue_head_invokeCall
#print axioms byValue_head_source
#print axioms byValue_head_history
end Goose.Proofs.ConstructionGhostArgumentHistoryInversion
