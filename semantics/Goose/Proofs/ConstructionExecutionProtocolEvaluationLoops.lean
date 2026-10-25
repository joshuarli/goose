import Goose.Proofs.ConstructionExecutionProtocolEvaluationContext

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionProtocol
open Goose.Construct

variable {predicate : ConstructionState → Prop} [primitives : ConstructionProtocolPrimitives predicate]
  [reservations : ConstructionReservationPrimitives predicate]
include primitives reservations

theorem buildElement_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (element : Ty) (expression : Expr) :
    (PreservesConstructionInvariant predicate) (buildElement (fuel + 1) config environment destination element expression) := by
  simp only [buildElement]
  protocol_eval previous

theorem execWhile_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (condition : Expr) (body : Block) :
    (PreservesConstructionInvariant predicate) (execWhile (fuel + 1) config environment condition body) := by
  simp only [execWhile]
  protocol_eval previous

theorem execRange_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (var : Goose.Core.VarId) (ty : Goose.Core.IntTy) (first last : Int) (body : Block) :
    (PreservesConstructionInvariant predicate) (execRange (fuel + 1) config environment var ty first last body) := by
  simp only [execRange]
  protocol_eval previous

theorem execEach_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (var : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool) (body : Block)
    (view : RuntimeView) (current : Nat) :
    (PreservesConstructionInvariant predicate) (execEach (fuel + 1) config environment var index byRef body view current) := by
  simp only [execEach]
  protocol_eval previous

theorem loopBody_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) :
    (PreservesConstructionInvariant predicate) (loopBody (fuel + 1) config environment pre body) := by
  simp only [loopBody]
  protocol_eval previous

theorem pushValue_preservesConstructionInvariant_succ (fuel : Nat) (config : EvalConfig)
    (previous : (EvaluationPreservesConstructionInvariant (predicate := predicate)) fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) :
    (PreservesConstructionInvariant predicate) (pushValue (fuel + 1) config environment owner expression origin) := by
  simp only [pushValue]
  protocol_eval previous


end Goose.Proofs.ConstructionExecutionProtocol
