import Goose.Proofs.ConstructionGhostSourceFuel

namespace Goose.Proofs.ConstructionGhostSyntaxFuel
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostSourceFuel

mutual
inductive ValueSyntax (config : EvalConfig) : Expr → Prop
  | base {expression : Expr} (supported : Goose.Proofs.ConstructionGhostSourceTransition.SupportedValue expression) :
      ValueSyntax config expression
  | fill (element : Ty) (count : Nat) (operand : Expr) (origin : Goose.Core.OriginId)
      (fixed : (Ty.arr element count).nonfixed = false) (child : ValueSyntax config operand) :
      ValueSyntax config (.fill (.arr element count) operand origin)
  | call (contextId : Goose.Core.ContextId) (arguments : List Arg) (origin : Goose.Core.OriginId)
      (context : Context) (implementation : Impl)
      (contextFound : config.module.contexts[contextId]? = some context)
      (implementationFound : config.module.impls[context.impl]? = some implementation)
      (resultsEmpty : implementation.results = #[])
      (argumentsSyntax : ArgumentSyntax config implementation.params.toList arguments) :
      ValueSyntax config (.call contextId arguments origin)

inductive ArgumentSyntax (config : EvalConfig) : List Param → List Arg → Prop
  | nil : ArgumentSyntax config [] []
  | value (parameter : Goose.Core.VarId) (parameters : List Param) (operand : Expr) (arguments : List Arg)
      (child : ValueSyntax config operand) (tail : ArgumentSyntax config parameters arguments) :
      ArgumentSyntax config (⟨parameter, .byValue⟩ :: parameters) (.byVal operand :: arguments)
end

inductive StatementSyntax (config : EvalConfig) : Stmt → Prop
  | expression (operand : Expr) (origin : Goose.Core.OriginId) (child : ValueSyntax config operand) :
      StatementSyntax config (.expr operand origin)
  | printText (text : String) (origin : Goose.Core.OriginId) : StatementSyntax config (.print [.text text] origin)

def ClosedModule (config : EvalConfig) : Prop :=
  ∀ (contextId : Goose.Core.ContextId) (context : Context) (implementation : Impl),
    config.module.contexts[contextId]? = some context → config.module.impls[context.impl]? = some implementation →
    ∃ scope statements, implementation.body = .mk scope statements none ∧
      ∀ statement ∈ statements, StatementSyntax config statement

structure SyntaxFuel (config : EvalConfig) (fuel : Nat) : Prop where
  value : ∀ environment expression, ValueSyntax config expression → FuelSupport config fuel (.value environment expression)
  arguments : ∀ environment vars parameters arguments, ArgumentSyntax config parameters arguments →
    FuelSupport config fuel (.arguments environment vars parameters arguments)
  statement : ∀ environment statement, StatementSyntax config statement → FuelSupport config fuel (.statement environment statement)
  statements : ∀ environment statements, (∀ statement ∈ statements, StatementSyntax config statement) →
    FuelSupport config fuel (.statements environment statements)
  activationBody : ∀ activation pre scope statements, (∀ statement ∈ statements, StatementSyntax config statement) →
    FuelSupport config fuel (.boundActivationBody activation pre (.mk scope statements none))
  activation : ∀ activation pre scope statements origin, (∀ statement ∈ statements, StatementSyntax config statement) →
    FuelSupport config fuel (.boundActivation activation pre (.mk scope statements none) origin)
  call : ∀ environment contextId arguments origin context implementation,
    config.module.contexts[contextId]? = some context → config.module.impls[context.impl]? = some implementation →
    implementation.results = #[] → ArgumentSyntax config implementation.params.toList arguments →
    FuelSupport config fuel (.callWith environment contextId arguments origin)

theorem syntaxFuel_exists (fuel : Nat) (config : EvalConfig) (closed : ClosedModule config) : SyntaxFuel config fuel := by
  induction fuel with
  | zero =>
      constructor <;> intros <;> exact .timeout _
  | succ fuel previous =>
      constructor
      · intro environment expression derivation
        cases derivation with
        | base supported => exact .legacy (fuel + 1) (.value environment supported)
        | fill element count operand origin fixed child =>
            exact .fill fuel environment element count origin operand fixed (previous.value environment operand child)
        | call contextId arguments origin context implementation contextFound implementationFound resultsEmpty argumentsSyntax =>
            exact .valueCallWith fuel environment contextId arguments origin context implementation contextFound implementationFound
              resultsEmpty (previous.call environment contextId arguments origin context implementation contextFound implementationFound
                resultsEmpty argumentsSyntax)
      · intro environment vars parameters arguments derivation
        cases derivation with
        | nil => exact .legacy (fuel + 1) (.argumentsDone environment vars)
        | value parameter parameters operand arguments child tail =>
            exact .argumentValue fuel environment vars ⟨parameter, .byValue⟩ parameters operand arguments
              (previous.value environment operand child) (previous.arguments environment vars parameters arguments tail)
      · intro environment statement derivation
        cases derivation with
        | expression operand origin child =>
            exact .expression fuel environment operand origin (previous.value environment operand child)
        | printText text origin => exact .legacy (fuel + 1) (.printText environment text origin)
      · intro environment statements derivation
        cases statements with
        | nil => exact .legacy (fuel + 1) (.empty environment)
        | cons statement rest =>
            have head : StatementSyntax config statement := derivation statement (by simp)
            have tail : ∀ statement ∈ rest, StatementSyntax config statement := by
              intro statement member
              exact derivation statement (by simp [member])
            have headSupported := previous.statement environment statement head
            exact .sequence fuel environment statement rest headSupported (previous.statements environment rest tail)
      · intro activation pre scope statements derivation
        exact .boundActivationBody fuel activation pre scope statements (fun environment => previous.statements environment statements derivation)
      · intro activation pre scope statements origin derivation
        exact .boundActivation fuel activation pre scope statements origin (previous.activationBody activation pre scope statements derivation)
      · intro environment contextId arguments origin context implementation contextFound implementationFound resultsEmpty argumentsSyntax
        obtain ⟨scope, statements, body, derivation⟩ := closed contextId context implementation contextFound implementationFound
        apply FuelSupport.callWith fuel environment contextId arguments origin context implementation contextFound implementationFound
          resultsEmpty (previous.arguments environment implementation.vars implementation.params.toList arguments argumentsSyntax)
        intro act pre
        rw [body]
        exact previous.activation ⟨context.impl, act, implementation.vars, [], []⟩ pre scope statements origin derivation

theorem syntaxModule_history (fuel : Nat) (config : EvalConfig) (closed : ClosedModule config)
    (entryContext : Context) (entryImplementation : Impl) (noGlobals : config.module.globals.size = 0)
    (entryFound : config.module.contexts[config.module.entry]? = some entryContext)
    (entryImplementationFound : config.module.impls[entryContext.impl]? = some entryImplementation)
    (entryResults : entryImplementation.results = #[]) (entryParameters : entryImplementation.params = #[]) :
    ∃ outcome, SourceHistory config fuel [] (.callWith ⟨0, 0, #[], [], []⟩ config.module.entry [] 0) .initial outcome ∧
      runModule fuel config .initial = moduleCallResult outcome := by
  have args : ArgumentSyntax config entryImplementation.params.toList [] := by
    simpa [entryParameters] using (ArgumentSyntax.nil : ArgumentSyntax config [] [])
  have support := (syntaxFuel_exists fuel config closed).call ⟨0, 0, #[], [], []⟩ config.module.entry [] 0
    entryContext entryImplementation entryFound entryImplementationFound entryResults args
  have history := fuelHistory_exists fuel config _ [] .initial support
  change SourceHistory config fuel [] (.callWith ⟨0, 0, #[], [], []⟩ config.module.entry [] 0) .initial
    (invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 .initial) at history
  refine ⟨_, history, ?_⟩
  simp only [runModule, noGlobals, List.range_zero, initGlobals, getImplementation, entryFound,
    entryImplementationFound, entryResults, Array.toList_empty, channelsFor, List.mapM_nil, bind, pure, moduleCallResult]
  cases invokeCall fuel config ⟨0, 0, #[], [], []⟩ config.module.entry [] [] 0 .initial <;> rfl

private def firstContext : Context := ⟨0, "first", [], [], []⟩
private def secondContext : Context := ⟨1, "second", [], [], []⟩
private def firstStatements : List Stmt := [.print [.text "a"] 0,
  .expr (.fill (.arr (.int .i64) 3) (.lit .i64 7) 0) 0, .expr (.call 1 [.byVal (.lit .i64 1)] 0) 0]
private def secondStatements : List Stmt := [.print [.text "b"] 0, .expr (.call 0 [] 0) 0]
private def firstImplementation : Impl := ⟨"first", #[], #[], #[], .mk 0 firstStatements none, .unknown⟩
private def secondImplementation : Impl := ⟨"second", #[⟨0, .byValue⟩], #[],
  #[⟨"n", .int .i64, .immutable, 0, 0⟩], .mk 1 secondStatements none, .unknown⟩
private def witnessConfig : EvalConfig := ⟨.release,
  ⟨#[], #[], #[], #[firstImplementation, secondImplementation], #[firstContext, secondContext], 0, #[], #[], #[]⟩⟩
private def witnessState : ExecutionStep α → ExecutionState
  | .ok _ state | .stop _ state | .escape _ _ state | .jump _ _ state => state

private theorem firstStatements_syntax : ∀ statement ∈ firstStatements, StatementSyntax witnessConfig statement := by
  intro statement member
  simp only [firstStatements, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .printText "a" 0
  · exact .expression _ 0 (.base (.fill (.int .i64) 3 0 rfl (.integer .i64 7)))
  · exact .expression _ 0 (.call 1 _ 0 secondContext secondImplementation rfl rfl rfl
      (.value 0 [] (.lit .i64 1) [] (.base (.integer .i64 1)) .nil))

private theorem secondStatements_syntax : ∀ statement ∈ secondStatements, StatementSyntax witnessConfig statement := by
  intro statement member
  simp only [secondStatements, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .printText "b" 0
  · exact .expression _ 0 (.call 0 [] 0 firstContext firstImplementation rfl rfl rfl .nil)

private theorem witness_closed : ClosedModule witnessConfig := by
  intro contextId context implementation contextFound implementationFound
  cases contextId with
  | zero =>
      have contextEq : context = firstContext := by simpa [witnessConfig] using contextFound.symm
      subst context
      have implementationEq : implementation = firstImplementation := by
        simpa [witnessConfig, firstContext] using implementationFound.symm
      subst implementation
      exact ⟨0, firstStatements, rfl, firstStatements_syntax⟩
  | succ contextId =>
      cases contextId with
      | zero =>
          have contextEq : context = secondContext := by simpa [witnessConfig] using contextFound.symm
          subst context
          have implementationEq : implementation = secondImplementation := by
            simpa [witnessConfig, secondContext] using implementationFound.symm
          subst implementation
          exact ⟨1, secondStatements, rfl, secondStatements_syntax⟩
      | succ contextId => simp [witnessConfig] at contextFound

theorem mutualModule_history (fuel : Nat) : ∃ outcome,
    SourceHistory witnessConfig fuel [] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) .initial outcome ∧
      runModule fuel witnessConfig .initial = moduleCallResult outcome :=
  syntaxModule_history fuel witnessConfig witness_closed firstContext firstImplementation rfl rfl rfl rfl rfl

theorem mutualModule_terminal : ∃ state,
    runModule 20 witnessConfig .initial = .stop .timeout state ∧ 1 < state.nextAct ∧
    0 < state.construction.stdout.data.size ∧
    ∃ outcome, SourceHistory witnessConfig 20 [] (.callWith ⟨0, 0, #[], [], []⟩ 0 [] 0) .initial outcome ∧
      runModule 20 witnessConfig .initial = moduleCallResult outcome := by
  obtain ⟨outcome, history, execution⟩ := mutualModule_history 20
  refine ⟨witnessState (runModule 20 witnessConfig .initial), ?_, ?_, ?_, outcome, history, execution⟩ <;>
    unfold witnessState witnessConfig firstContext secondContext firstImplementation secondImplementation firstStatements secondStatements <;> cbv

#print axioms mutualModule_history
#print axioms mutualModule_terminal

#print axioms syntaxModule_history

#print axioms syntaxFuel_exists
end Goose.Proofs.ConstructionGhostSyntaxFuel
