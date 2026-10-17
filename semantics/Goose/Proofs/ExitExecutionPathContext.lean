import Goose.Proofs.ExitExecutionInvocationStatementsDefinitions
import Goose.Proofs.ExitExecutionInvocationProducers
import Goose.Proofs.ExitExecutionInvocationValues

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

def CompletionPreparation (channels : List Channel) (origin : Goose.Core.OriginId)
    (initial : ExecutionState) (planned : List (Channel × Option Nat)) (prepared : ExecutionState) : Prop :=
  ((channels.mapM fun channel => match channel with
    | .construct incoming => do
        let token ← liftConstruction origin (waitExitDestination incoming)
        pure (Channel.completion token, some token)
    | .register ty => pure (Channel.register ty, none)
    | .completion _ => fault .flow) : EvalM (List (Channel × Option Nat))) initial = .ok planned prepared

inductive ArgumentValuePrefix (fuel : Nat) (config : EvalConfig) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameter : Param) : Arg → ExecutionState → Value → ExecutionState → Prop
  | reference (mutability : Goose.Core.Mutability) (place : Place) (initial final : ExecutionState)
      (location : Goose.Core.Loc)
      (normal : evalPlace fuel config environment place initial = .ok location final) :
      ArgumentValuePrefix fuel config environment vars parameter (.byRef mutability place) initial (.ref location) final
  | value (operand : Expr) (initial final : ExecutionState) (value : Value)
      (normal : evalValue fuel config environment operand initial = .ok value final) :
      ArgumentValuePrefix fuel config environment vars parameter (.byVal operand) initial value final
  | materialized (operand : Expr) (descriptor : LocalVar) (values : Array Value) (destination : Nat) (value : Value)
      (initial evaluated stored published final : ExecutionState)
      (lookup : vars[parameter.var]? = some descriptor)
      (evaluatedNormally : materializeProducer fuel ⟨config.module, environment.vars⟩ operand
        (evalValue fuel config environment operand) initial = .ok (some values) evaluated)
      (storedNormally : materializedDestination fuel config.layout environment.act descriptor.ty
        (expressionOrigin operand) values.size (.fixed values) evaluated = .ok destination stored)
      (publishedNormally : publishCarriers (expressionOrigin operand) [.completed destination] stored = .ok () published)
      (normal : carrierValue (.completed destination) published = .ok value final) :
      ArgumentValuePrefix fuel config environment vars parameter (.construct operand) initial value final
  | constructed (operand : Expr) (descriptor : LocalVar) (carrier : Carrier) (value : Value)
      (initial evaluated constructed final : ExecutionState)
      (lookup : vars[parameter.var]? = some descriptor)
      (evaluatedNormally : materializeProducer fuel ⟨config.module, environment.vars⟩ operand
        (evalValue fuel config environment operand) initial = .ok none evaluated)
      (constructedNormally : constructLocal ⟨config.module, environment.vars⟩ environment.act descriptor.ty
        (expressionOrigin operand) operand (fun destination => buildExpr fuel config environment destination operand)
        evaluated = .ok carrier constructed)
      (normal : carrierValue carrier constructed = .ok value final) :
      ArgumentValuePrefix fuel config environment vars parameter (.construct operand) initial value final

inductive ExitCallSite (config : EvalConfig) :
    {α β : Type} → ExitInvocation α → ExecutionState → ExitInvocation β → ExecutionState → Prop
  | values {α β : Type} {caller : ExitInvocation α} {child : ExitInvocation β}
      {initial prepared : ExecutionState}
      (site : ValueInvocationEdge config caller initial child prepared) :
      ExitCallSite config caller initial child prepared
  | producer {α β : Type} {caller : ExitInvocation α} {child : ExitInvocation β}
      {initial prepared : ExecutionState}
      (site : ProducerInvocationChild config caller initial child prepared) :
      ExitCallSite config caller initial child prepared
  | statements {α β : Type} {caller : ExitInvocation α} {child : ExitInvocation β}
      {initial prepared : ExecutionState}
      (site : StatementInvocationEdge config caller initial child prepared) :
      ExitCallSite config caller initial child prepared
  | moduleGlobals (fuel : Nat) (initial : ExecutionState) :
      ExitCallSite config (.module fuel) initial
        (.globals fuel (List.range config.module.globals.size)) initial
  | moduleEntry (fuel : Nat) (initial globalsState implementationState entryState : ExecutionState)
      (id : Goose.Core.ImplId) (implementation : Impl) (channels : List Channel)
      (globals : initGlobals fuel config (List.range config.module.globals.size) initial = .ok () globalsState)
      (lookup : getImplementation config config.module.entry globalsState = .ok (id, implementation) implementationState)
      (receiving : channelsFor config.layout 0 implementation.results.toList 0 implementationState = .ok channels entryState) :
      ExitCallSite config (.module fuel) initial
        (.call fuel ⟨0, 0, #[], [], []⟩ config.module.entry [] channels 0) entryState
  | activationBody (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (body : Block) (origin : Goose.Core.OriginId) (initial : ExecutionState) (implementation : Impl)
      (lookup : config.module.impls[environment.implementation]? = some implementation) :
      ExitCallSite config (.activation (fuel + 1) environment pre body origin) initial
        (.activationBody fuel environment pre body) initial
  | callActivation (fuel : Nat) (environment : RuntimeActivation) (context : Goose.Core.ContextId)
      (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
      (initial entered : ExecutionState) (activation : RuntimeActivation)
      (pre : List (Goose.Core.VarId × Value)) (body : Block)
      (prepared : CallActivationPrefix fuel config environment context arguments channels origin initial activation pre body entered) :
      ExitCallSite config (.call (fuel + 1) environment context arguments channels origin) initial
        (.activation fuel activation pre body origin) entered
  | callArguments (fuel : Nat) (environment : RuntimeActivation) (context : Goose.Core.ContextId)
      (arguments : List Arg) (channels : List Channel) (origin : Goose.Core.OriginId)
      (initial prepared : ExecutionState) (id : Goose.Core.ImplId) (implementation : Impl) (firstChannels : List Channel)
      (receiving : CallArgumentPrefix config context channels origin initial id implementation firstChannels prepared) :
      ExitCallSite config (.call (fuel + 1) environment context arguments channels origin) initial
        (.arguments fuel environment implementation.vars implementation.params.toList arguments) prepared
  | argumentReference (fuel : Nat) (environment : RuntimeActivation) (vars : Array LocalVar)
      (parameter : Param) (parameters : List Param) (referenceKind : Goose.Core.Mutability) (place : Place)
      (arguments : List Arg) (initial : ExecutionState) :
      ExitCallSite config (.arguments (fuel + 1) environment vars (parameter :: parameters) (.byRef referenceKind place :: arguments)) initial
        (.place fuel environment place) initial
  | argumentValue (fuel : Nat) (environment : RuntimeActivation) (vars : Array LocalVar)
      (parameter : Param) (parameters : List Param) (operand : Expr) (arguments : List Arg) (initial : ExecutionState) :
      ExitCallSite config (.arguments (fuel + 1) environment vars (parameter :: parameters) (.byVal operand :: arguments)) initial
        (.value fuel environment operand) initial
  | argumentMaterialize (fuel : Nat) (environment : RuntimeActivation) (vars : Array LocalVar)
      (parameter : Param) (parameters : List Param) (operand : Expr) (arguments : List Arg)
      (initial : ExecutionState) (descriptor : LocalVar) (count : Nat)
      (lookup : vars[parameter.var]? = some descriptor)
      (materialized : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = some count) :
      ExitCallSite config (.arguments (fuel + 1) environment vars (parameter :: parameters) (.construct operand :: arguments)) initial
        (.value fuel environment operand) initial
  | argumentBuild (fuel : Nat) (environment : RuntimeActivation) (vars : Array LocalVar)
      (parameter : Param) (parameters : List Param) (operand : Expr) (arguments : List Arg)
      (initial prepared : ExecutionState) (descriptor : LocalVar) (destination : Nat)
      (lookup : vars[parameter.var]? = some descriptor)
      (materialized : ordinaryProducerCount? fuel ⟨config.module, environment.vars⟩ operand = none)
      (allocated : newDestination config.layout environment.act descriptor.ty .value (expressionOrigin operand) none
        (producerCount? ⟨config.module, environment.vars⟩ operand) initial = .ok destination prepared) :
      ExitCallSite config (.arguments (fuel + 1) environment vars (parameter :: parameters) (.construct operand :: arguments)) initial
        (.build fuel environment destination operand) prepared
  | argumentsTail (fuel : Nat) (environment : RuntimeActivation) (vars : Array LocalVar)
      (parameter : Param) (parameters : List Param) (argument : Arg) (arguments : List Arg)
      (initial middle : ExecutionState) (value : Value)
      (normal : ArgumentValuePrefix fuel config environment vars parameter argument initial value middle) :
      ExitCallSite config (.arguments (fuel + 1) environment vars (parameter :: parameters) (argument :: arguments)) initial
        (.arguments fuel environment vars parameters arguments) middle
  | operandsHead (fuel : Nat) (environment : RuntimeActivation) (channel : Channel) (channels : List Channel)
      (operand : Expr) (operands : List Expr) (initial : ExecutionState) :
      ExitCallSite config (.operands (fuel + 1) environment (channel :: channels) (operand :: operands)) initial
        (.produce fuel environment [channel] operand) initial
  | operandsTail (fuel : Nat) (environment : RuntimeActivation) (channel : Channel) (channels : List Channel)
      (operand : Expr) (operands : List Expr) (initial produced middle : ExecutionState)
      (carriers : List Carrier) (carrier : Carrier)
      (producedNormally : evalProduce fuel config environment [channel] operand initial = .ok carriers produced)
      (selected : singleCarrier carriers produced = .ok carrier middle) :
      ExitCallSite config (.operands (fuel + 1) environment (channel :: channels) (operand :: operands)) initial
        (.operands fuel environment channels operands) middle
  | completionProduce (fuel : Nat) (environment : RuntimeActivation) (channels : List Channel)
      (expression : Expr) (initial prepared : ExecutionState) (planned : List (Channel × Option Nat))
      (setup : CompletionPreparation channels (expressionOrigin expression) initial planned prepared) :
      ExitCallSite config (.completionTail fuel environment channels expression) initial
        (.produce fuel environment (planned.map Prod.fst) expression) prepared
  | activationScope (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (body : Block) (initial : ExecutionState) :
      ExitCallSite config (.activationBody (fuel + 1) environment pre body) initial
        (.activationScope fuel environment pre body) initial
  | resultBlockWith (fuel : Nat) (environment : RuntimeActivation) (channels : List Channel)
      (body : Block) (initial : ExecutionState) :
      ExitCallSite config (.resultBlock (fuel + 1) environment channels body) initial
        (.resultBlockWith fuel environment [] channels body) initial
  | resultScope (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (channels : List Channel) (body : Block) (initial : ExecutionState) :
      ExitCallSite config (.resultBlockWith (fuel + 1) environment pre channels body) initial
        (.resultScope fuel environment pre channels body) initial
  | statementsHead (fuel : Nat) (environment : RuntimeActivation) (statement : Stmt)
      (rest : List Stmt) (initial : ExecutionState) :
      ExitCallSite config (.statements (fuel + 1) environment (statement :: rest)) initial
        (.statement fuel environment statement) initial
  | statementsTail (fuel : Nat) (environment : RuntimeActivation) (statement : Stmt)
      (rest : List Stmt) (initial middle : ExecutionState) (value : Value)
      (normal : execStmt fuel config environment statement initial = .ok (.normal value) middle) :
      ExitCallSite config (.statements (fuel + 1) environment (statement :: rest)) initial
        (.statements fuel environment rest) middle
  | blockStatements (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (channels : List Channel) (scope : Nat) (statements : List Stmt) (tail : Option Expr)
      (initial bound : ExecutionState)
      (binding : bindAll environment.act initial.nextScope pre
        { initial with nextScope := initial.nextScope + 1 } = .ok () bound) :
      ExitCallSite config (.block (fuel + 1) environment pre channels (.mk scope statements tail)) initial
        (.statements fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements) bound
  | blockValueTail (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (channels : List Channel) (scope : Nat) (statements : List Stmt) (expression : Expr)
      (initial bound middle : ExecutionState) (value : Value)
      (binding : bindAll environment.act initial.nextScope pre
        { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
      (normal : execStmts fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
        statements bound = .ok (.normal value) middle)
      (empty : channels.isEmpty = true) :
      ExitCallSite config (.block (fuel + 1) environment pre channels (.mk scope statements (some expression))) initial
        (.value fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } expression) middle
  | blockProduceTail (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (channels : List Channel) (scope : Nat) (statements : List Stmt) (expression : Expr)
      (initial bound middle : ExecutionState) (value : Value)
      (binding : bindAll environment.act initial.nextScope pre
        { initial with nextScope := initial.nextScope + 1 } = .ok () bound)
      (normal : execStmts fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
        statements bound = .ok (.normal value) middle)
      (nonempty : channels.isEmpty = false) :
      ExitCallSite config (.block (fuel + 1) environment pre channels (.mk scope statements (some expression))) initial
        (.produce fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } channels expression) middle
  | activationStatements (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (scope : Nat) (statements : List Stmt) (tail : Option Expr) (initial bound : ExecutionState)
      (binding : bindAll environment.act initial.nextScope pre { initial with
        nextScope := initial.nextScope + 1
        activations := initial.activations.map (fun current => if current.act == environment.act then
          { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound) :
      ExitCallSite config (.activationScope fuel environment pre (.mk scope statements tail)) initial
        (.statements fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements) bound
  | activationTail (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (scope : Nat) (statements : List Stmt) (expression : Expr)
      (initial bound middle : ExecutionState) (value : Value)
      (binding : bindAll environment.act initial.nextScope pre { initial with
        nextScope := initial.nextScope + 1
        activations := initial.activations.map (fun current => if current.act == environment.act then
          { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound)
      (normal : execStmts fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
        statements bound = .ok (.normal value) middle) :
      ExitCallSite config (.activationScope fuel environment pre (.mk scope statements (some expression))) initial
        (.completionTail fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
          environment.channels expression) middle
  | resultStatements (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (channels : List Channel) (scope : Nat) (statements : List Stmt) (tail : Option Expr) (initial bound : ExecutionState)
      (binding : bindAll environment.act initial.nextScope pre { initial with
        nextScope := initial.nextScope + 1
        activations := initial.activations.map (fun current => if current.act == environment.act then
          { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound) :
      ExitCallSite config (.resultScope fuel environment pre channels (.mk scope statements tail)) initial
        (.statements fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } statements) bound
  | resultTail (fuel : Nat) (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value))
      (channels : List Channel) (scope : Nat) (statements : List Stmt) (expression : Expr)
      (initial bound middle : ExecutionState) (value : Value)
      (binding : bindAll environment.act initial.nextScope pre { initial with
        nextScope := initial.nextScope + 1
        activations := initial.activations.map (fun current => if current.act == environment.act then
          { current with scopes := (scope, initial.nextScope) :: environment.scopes } else current) } = .ok () bound)
      (normal : execStmts fuel config { environment with scopes := (scope, initial.nextScope) :: environment.scopes }
        statements bound = .ok (.normal value) middle) :
      ExitCallSite config (.resultScope fuel environment pre channels (.mk scope statements (some expression))) initial
        (.produce fuel { environment with scopes := (scope, initial.nextScope) :: environment.scopes } channels expression) middle
  | returnOperands (fuel : Nat) (environment activation : RuntimeActivation)
      (operands : List Expr) (origin : Goose.Core.OriginId)
      (initial prepared : ExecutionState) (channels : List Channel)
      (selected : enclosingActivation environment initial = .ok activation initial)
      (setup : exitChannels environment activation operands origin initial = .ok channels prepared) :
      ExitCallSite config (.statement (fuel + 1) environment (.retValues operands origin)) initial
        (.operands fuel environment channels operands) prepared
  | returnForwardProduce (fuel : Nat) (environment activation : RuntimeActivation)
      (producer : Expr) (origin : Goose.Core.OriginId)
      (initial prepared : ExecutionState) (channels : List Channel)
      (selected : enclosingActivation environment initial = .ok activation initial)
      (setup : exitChannels environment activation (List.replicate activation.channels.length producer) origin initial = .ok channels prepared) :
      ExitCallSite config (.statement (fuel + 1) environment (.retForward producer origin)) initial
        (.produce fuel environment channels producer) prepared
  | returnProduce (fuel : Nat) (environment activation : RuntimeActivation)
      (producer : Expr) (origin : Goose.Core.OriginId)
      (initial prepared : ExecutionState) (channels : List Channel)
      (selected : enclosingActivation environment initial = .ok activation initial)
      (setup : exitChannels environment activation
        (match producer with | .values operands => operands | _ => List.replicate activation.channels.length producer)
        origin initial = .ok channels prepared) :
      ExitCallSite config (.statement (fuel + 1) environment (.ret (some producer) origin)) initial
        (.produce fuel environment channels producer) prepared
  | breakProduce (fuel : Nat) (environment : RuntimeActivation) (target : BreakTarget)
      (producer : Expr) (origin : Goose.Core.OriginId)
      (initial prepared : ExecutionState) (channels : List Channel)
      (selected : currentBreak environment.act (some .block) initial = .ok target initial)
      (setup : exitChannels environment { environment with channels := target.channels }
        (match producer with | .values operands => operands | _ => List.replicate target.channels.length producer)
        origin initial = .ok channels prepared) :
      ExitCallSite config (.statement (fuel + 1) environment (.breakValue producer origin)) initial
        (.produce fuel environment channels producer) prepared
  | returnFromOperands (fuel : Nat) (environment activation : RuntimeActivation)
      (target : Nat) (operands : List Expr) (origin : Goose.Core.OriginId)
      (initial prepared : ExecutionState) (channels : List Channel)
      (selected : targetActivation config target initial = .ok activation initial)
      (setup : exitChannels environment activation operands origin initial = .ok channels prepared) :
      ExitCallSite config (.statement (fuel + 1) environment (.returnFrom target operands origin)) initial
        (.operands fuel environment channels operands) prepared
  | returnFromForwardProduce (fuel : Nat) (environment activation : RuntimeActivation)
      (target : Nat) (producer : Expr) (origin : Goose.Core.OriginId)
      (initial prepared : ExecutionState) (channels : List Channel)
      (selected : targetActivation config target initial = .ok activation initial)
      (setup : exitChannels environment activation (List.replicate activation.channels.length producer) origin initial = .ok channels prepared) :
      ExitCallSite config (.statement (fuel + 1) environment (.returnFromForward target producer origin)) initial
        (.produce fuel environment channels producer) prepared

inductive ExitReached (fuel : Nat) (config : EvalConfig) :
    {α : Type} → ExitInvocation α → ExecutionState → Prop
  | initial : ExitReached fuel config (.module fuel) .initial
  | call {α β : Type} {caller : ExitInvocation α} {callee : ExitInvocation β}
      {initial middle : ExecutionState}
      (callerReached : ExitReached fuel config caller initial)
      (site : ExitCallSite config caller initial callee middle) :
      ExitReached fuel config callee middle

inductive ExitLexicalFrame
  | breakTarget (target : BreakTarget)
  | receivingDestination (origin : Goose.Core.OriginId) (destination : Nat)
  | scope (environment : RuntimeActivation) (scope scopeInst : Nat)
  | handler (activation : RuntimeActivation) (resultTypes : List Ty) (origin : Goose.Core.OriginId)
  | exitChannels (origin : Goose.Core.OriginId) (borrowed : List BorrowedWaitingExitReservation) (tokens : List Nat)

def ExitInvocation.frames (config : EvalConfig) (caller : ExitInvocation α)
    (initial middle : ExecutionState) (outer inner : List ExitLexicalFrame) : Prop :=
  match caller with
  | .activation _ environment _ _ origin =>
      ∃ implementation, config.module.impls[environment.implementation]? = some implementation ∧
        inner = .handler environment (implementation.results.toList.map (·.ty)) origin :: outer
  | .block _ environment _ _ (.mk scope _ _)
  | .activationScope _ environment _ (.mk scope _ _)
  | .resultScope _ environment _ _ (.mk scope _ _) =>
      inner = .scope environment scope initial.nextScope :: outer
  | .produce _ environment incoming expression =>
      match expression with
      | .blockE _ origin =>
          ∃ planned channels prepared,
            ProducerReceivingPrefix environment incoming expression initial planned channels prepared ∧
            inner = .breakTarget ⟨prepared.nextScope, environment.act, .block, channels⟩ :: outer
      | _ => inner = outer
  | .build _ environment incoming expression =>
      ∃ destination prepared,
        liftConstruction (expressionOrigin expression) (renewReceivingDestination incoming) initial = .ok destination prepared ∧
        inner = (match expression with
          | .blockE _ _ => [.breakTarget ⟨prepared.nextScope, environment.act, .block, [.construct destination]⟩]
          | _ => []) ++ .receivingDestination (expressionOrigin expression) destination :: outer
  | .loop _ environment _ _ =>
      inner = .breakTarget ⟨initial.nextScope, environment.act, .loop, []⟩ :: outer
  | .completionTail _ _ channels expression =>
      ∃ planned, CompletionPreparation channels (expressionOrigin expression) initial planned middle ∧
        inner = .exitChannels (expressionOrigin expression) [] (planned.filterMap Prod.snd) :: outer
  | .statement _ _ (.returnFrom targetId _ origin)
  | .statement _ _ (.returnFromForward targetId _ origin) =>
      ∃ activation, targetActivation config targetId initial = .ok activation initial ∧
        inner = .exitChannels origin (borrowedExitChannelReceipts activation initial)
          (exitChannelReservationTokens initial.construction.exitReservations.size middle) :: outer
  | .statement _ environment (.retValues _ origin)
  | .statement _ environment (.retForward _ origin)
  | .statement _ environment (.ret (some _) origin) =>
      ∃ activation, enclosingActivation environment initial = .ok activation initial ∧
        inner = .exitChannels origin (borrowedExitChannelReceipts activation initial)
          (exitChannelReservationTokens initial.construction.exitReservations.size middle) :: outer
  | .statement _ environment (.breakValue _ origin) =>
      ∃ target, currentBreak environment.act (some .block) initial = .ok target initial ∧
        inner = .exitChannels origin (borrowedExitChannelReceipts { environment with channels := target.channels } initial)
          (exitChannelReservationTokens initial.construction.exitReservations.size middle) :: outer
  | _ => inner = outer

def ExitCallSite.frames {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {callee : ExitInvocation β} {initial middle : ExecutionState}
    (_site : ExitCallSite config caller initial callee middle) (outer inner : List ExitLexicalFrame) : Prop :=
  caller.frames config initial middle outer inner

private theorem producerReceiving_has_frames {fuel : Nat} {config : EvalConfig}
    {environment : RuntimeActivation} {incoming planned channels : List Channel} {expression : Expr}
    {initial prepared middle : ExecutionState}
    (receiving : ProducerReceivingPrefix environment incoming expression initial planned channels prepared)
    (outer : List ExitLexicalFrame) :
    ∃ inner, (ExitInvocation.produce fuel environment incoming expression).frames config initial middle outer inner := by
  cases expression <;> first | exact ⟨_, rfl⟩ | skip
  exact ⟨_, _, _, _, receiving, rfl⟩

theorem ExitCallSite.has_frames {config : EvalConfig} {α β : Type}
    {caller : ExitInvocation α} {callee : ExitInvocation β} {initial middle : ExecutionState}
    (site : ExitCallSite config caller initial callee middle) (outer : List ExitLexicalFrame) :
    ∃ inner, site.frames outer inner := by
  cases site
  all_goals first | exact ⟨_, rfl⟩ | skip
  case values site => cases site <;> exact ⟨_, rfl⟩
  case statements site => cases site <;> exact ⟨_, rfl⟩
  case producer site =>
    cases site
    all_goals first | exact ⟨_, rfl⟩ | skip
    case produce receiving body => exact producerReceiving_has_frames receiving outer
    case build renewed body => exact ⟨_, _, _, renewed, rfl⟩
  case activationBody =>
    rename_i implementation lookup
    exact ⟨_, implementation, lookup, rfl⟩
  case completionProduce =>
    rename_i planned setup
    exact ⟨_, planned, setup, rfl⟩
  case returnFromOperands | returnFromForwardProduce | returnOperands | returnForwardProduce | returnProduce | breakProduce =>
    rename_i selected setup
    exact ⟨_, _, selected, rfl⟩

inductive ExitContextReached (fuel : Nat) (config : EvalConfig) :
    {α : Type} → List ExitLexicalFrame → ExitInvocation α → ExecutionState → Prop
  | initial : ExitContextReached fuel config [] (.module fuel) .initial
  | call {α β : Type} {caller : ExitInvocation α} {callee : ExitInvocation β}
      {initial middle : ExecutionState} {outer inner : List ExitLexicalFrame}
      (callerReached : ExitContextReached fuel config outer caller initial)
      (site : ExitCallSite config caller initial callee middle) (frames : site.frames outer inner) :
      ExitContextReached fuel config inner callee middle

theorem ExitReached.context {fuel : Nat} {config : EvalConfig} {α : Type}
    {invocation : ExitInvocation α} {state : ExecutionState}
    (reached : ExitReached fuel config invocation state) :
    ∃ context, ExitContextReached fuel config context invocation state := by
  induction reached with
  | initial => exact ⟨[], .initial⟩
  | call callerReached site previous =>
      obtain ⟨outer, callerContext⟩ := previous
      obtain ⟨inner, frames⟩ := site.has_frames outer
      exact ⟨inner, .call callerContext site frames⟩

end Goose.Proofs.ExitExecution
