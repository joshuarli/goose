import Goose.Proofs.ConstructionAcceptedRecursiveRegisterArithmetic

namespace Goose.Proofs.ConstructionAcceptedExecution
open Goose.Construct
open Goose.Proofs.ConstructionExecutionOwnership
open Goose.Proofs.ConstructionRootCorrespondence
open Goose.Proofs.ConstructionRepresentation

theorem evalValue_binary_unaryRegister (fuel : Nat) (config : EvalConfig) (integer : Goose.Core.IntTy)
    (accepted : AcceptedModule config) (frame : ConstructionSourceFrame) (before : ExecutionState)
    (ambient : OwnershipAmbient) (types : RootTypes) (live : Goose.Core.RootInst → Prop)
    (regions : List ReceivingRegion) (pending : List PendingCarrierFrame)
    (operation : Goose.Core.BinOp) (left right : Expr) (origin : Nat)
    (leftForm : UnaryRegisterExpression config integer left) (rightForm : UnaryRegisterExpression config integer right)
    (graph : RegisterCallGraphWithCallLocals config (.int integer))
    (world : AcceptedWorld config frame.initialized before ambient types live regions pending)
    (source : AcceptedFrame config accepted frame before types)
    (roots : List RootRef) (typingAfter : Nat) (rootsAfter : RState)
    (checked : CheckedValue frame (.bin operation left right origin) (.int integer) roots typingAfter rootsAfter) :
    EarlierScalarOutcome config accepted frame before ambient types regions pending (.int integer)
      (evalValue fuel config frame.interpretation.environment (.bin operation left right origin) before) := by
  exact evalValue_registerArithmetic config integer (.binary operation origin (.operand leftForm) (.operand rightForm)) fuel
    accepted frame before ambient types live regions pending graph world source roots typingAfter rootsAfter checked

#print axioms evalValue_binary_unaryRegister
end Goose.Proofs.ConstructionAcceptedExecution
