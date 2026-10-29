import Goose.Proofs.ConstructionGhostSyntaxFuel

namespace Goose.Proofs.ConstructionGhostBlockValueHistory
open Goose.Construct Goose.Proofs.ConstructionGhostSourceMutual Goose.Proofs.ConstructionGhostResultScope
open Goose.Proofs.ConstructionGhostBlockProducerTransition

def blockValueSyntax : SourceOperation α → Option (RuntimeActivation × Block × Goose.Core.OriginId)
  | .value environment (.blockE block origin) => some (environment, block, origin)
  | _ => none

def blockProducerSyntax : SourceOperation α → Option (RuntimeActivation × List Channel × Block × Goose.Core.OriginId)
  | .producerWith environment channels (.blockE block origin) => some (environment, channels, block, origin)
  | _ => none

def resultBlockSyntax : SourceOperation α → Option (RuntimeActivation × List Channel × Block)
  | .resultBlock environment channels block => some (environment, channels, block)
  | _ => none

def resultBlockWithSyntax : SourceOperation α → Option (RuntimeActivation × List (Goose.Core.VarId × Value) × List Channel × Block)
  | .resultBlockWith environment pre channels block => some (environment, pre, channels, block)
  | _ => none

theorem blockValue_producer_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (block : Block) (origin : Goose.Core.OriginId) (types : List Ty) (channels : List Channel) (ready : ExecutionState)
    (fuelEq : fuel = sourceFuel + 1) (operationEq : blockValueSyntax operation = some (environment, block, origin))
    (typesFound : blockResultTypes? (max sourceFuel (blockQueryBudget block)) ⟨config.module, environment.vars⟩ block = some types)
    (prepared : channelsFor config.layout environment.act
      (types.map fun ty => ⟨ty, if ty.nonfixed then .value else .register, none⟩) origin before = .ok channels ready) :
    SourceHistory config sourceFuel (path ++ [0]) (.producerWith environment channels (.blockE block origin)) ready
      (evalProduce sourceFuel config environment channels (.blockE block origin) ready) := by
  cases history <;> simp_all [blockValueSyntax]
  case aggregate =>
    rename_i shape children
    cases shape <;> simp_all [blockValueSyntax]
  case logical =>
    rename_i isAnd first second left right
    cases isAnd <;> simp_all [blockValueSyntax, logicalExpression]

theorem blockProducer_resultBlock_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (channels planned : List Channel) (block : Block) (origin : Goose.Core.OriginId) (ready : ExecutionState)
    (fuelEq : fuel = sourceFuel + 1) (operationEq : blockProducerSyntax operation = some (environment, channels, block, origin))
    (prepared : prepareBlockProducerChannels channels origin before = .ok planned ready) :
    SourceHistory config sourceFuel (path ++ [0]) (.resultBlock environment planned block) (blockProducerStart environment planned ready)
      (execResultBlock sourceFuel config environment planned block (blockProducerStart environment planned ready)) := by
  cases history <;> simp_all [blockProducerSyntax]
  case valueProducer =>
    rename_i shape valueChild builderChild
    cases shape <;> try simp_all [blockProducerSyntax]
    case supported supported => cases supported <;> simp_all [blockProducerSyntax]
    case scalar scalar => cases scalar <;> simp_all [blockProducerSyntax]
    case default shape => cases shape <;> simp_all [blockProducerSyntax]

theorem resultBlock_with_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (channels : List Channel) (block : Block)
    (fuelEq : fuel = sourceFuel + 1) (operationEq : resultBlockSyntax operation = some (environment, channels, block)) :
    SourceHistory config sourceFuel (path ++ [0]) (.resultBlockWith environment [] channels block) before
      (execResultBlockWith sourceFuel config environment [] channels block before) := by
  cases history <;> simp_all [resultBlockSyntax]

theorem resultBlock_body_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Option Expr) (ready : ExecutionState)
    (fuelEq : fuel = sourceFuel + 1) (operationEq : resultBlockWithSyntax operation = some (environment, pre, channels, .mk scope statements tail))
    (bound : bindAll environment.act before.nextScope pre (resultScopeStart environment scope before) = .ok () ready) :
    SourceHistory config sourceFuel (path ++ [0])
      (.statements { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements) ready
      (execStmts sourceFuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements ready) := by
  cases history <;> simp_all [resultBlockWithSyntax]

theorem resultBlock_tail_history {config : EvalConfig} {α : Type} {fuel : Nat} {path : List Nat}
    {operation : SourceOperation α} {before : ExecutionState} {outcome : ExecutionStep α}
    (history : SourceHistory config fuel path operation before outcome) (sourceFuel : Nat)
    (environment : RuntimeActivation) (pre : List (Goose.Core.VarId × Value)) (channels : List Channel)
    (scope : Nat) (statements : List Stmt) (tail : Expr) (ready after : ExecutionState) (value : Value)
    (fuelEq : fuel = sourceFuel + 1) (operationEq : resultBlockWithSyntax operation = some (environment, pre, channels, .mk scope statements (some tail)))
    (bound : bindAll environment.act before.nextScope pre (resultScopeStart environment scope before) = .ok () ready)
    (body : execStmts sourceFuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } statements ready = .ok (.normal value) after) :
    SourceHistory config sourceFuel (path ++ [1])
      (.producerWith { environment with scopes := (scope, before.nextScope) :: environment.scopes } channels tail) after
      (evalProduce sourceFuel config { environment with scopes := (scope, before.nextScope) :: environment.scopes } channels tail after) := by
  cases history <;> simp only [resultBlockWithSyntax, reduceCtorEq] at operationEq
  case timeout => cases fuelEq
  case resultBlockWith =>
    rename_i actualFuel actualEnvironment actualPre actualChannels actualScope actualStatements actualTail bodyChild tailChild
    simp only [Option.some.injEq, Prod.mk.injEq, Block.mk.injEq] at operationEq
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := operationEq
    cases fuelEq
    exact tailChild tail ready value after rfl bound body

#print axioms blockValue_producer_history
#print axioms blockProducer_resultBlock_history
#print axioms resultBlock_with_history
#print axioms resultBlock_body_history
#print axioms resultBlock_tail_history
end Goose.Proofs.ConstructionGhostBlockValueHistory
