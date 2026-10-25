import Goose.Proofs.ConstructionDeliveryFlowSoundnessEvaluationProduceControl

set_option Elab.async false

namespace Goose.Proofs.ConstructionDelivery
open Goose.Construct

private theorem produce_lit_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (t : Goose.Core.IntTy) (n : Int) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.lit t n) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.lit t n)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.lit t n)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.lit t n)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.lit t n) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.lit t n) selected _
        (previous.value environment (Expr.lit t n) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.lit t n) staticFuel enough)

private theorem produce_bool_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (b : Bool) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.bool b) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.bool b)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.bool b)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.bool b)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.bool b) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.bool b) selected _
        (previous.value environment (Expr.bool b) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.bool b) staticFuel enough)

private theorem produce_read_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (p : Place) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.read p) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.read p)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.read p)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.read p)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.read p) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.read p) selected _
        (previous.value environment (Expr.read p) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.read p) staticFuel enough)

private theorem produce_ref_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (m : Goose.Core.Mutability) (p : Place) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.ref m p) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.ref m p)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.ref m p)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.ref m p)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.ref m p) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.ref m p) selected _
        (previous.value environment (Expr.ref m p) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.ref m p) staticFuel enough)

private theorem produce_slice_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (m : Goose.Core.Mutability) (v : View) (lo hi : Bound) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.slice m v lo hi org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.slice m v lo hi org)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.slice m v lo hi org)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.slice m v lo hi org)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.slice m v lo hi org) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.slice m v lo hi org) selected _
        (previous.value environment (Expr.slice m v lo hi org) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.slice m v lo hi org) staticFuel enough)

private theorem produce_len_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (v : View) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.len v) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.len v)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.len v)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.len v)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.len v) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.len v) selected _
        (previous.value environment (Expr.len v) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.len v) staticFuel enough)

private theorem produce_un_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (op : Goose.Core.UnOp) (e : Expr) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.un op e org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.un op e org)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.un op e org)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.un op e org)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.un op e org) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.un op e org) selected _
        (previous.value environment (Expr.un op e org) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.un op e org) staticFuel enough)

private theorem produce_bin_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (op : Goose.Core.BinOp) (a b : Expr) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.bin op a b org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.bin op a b org)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.bin op a b org)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.bin op a b org)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.bin op a b org) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.bin op a b org) selected _
        (previous.value environment (Expr.bin op a b org) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.bin op a b org) staticFuel enough)

private theorem produce_cmp_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (op : Goose.Core.CmpOp) (a b : Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.cmp op a b) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.cmp op a b)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.cmp op a b)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.cmp op a b)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.cmp op a b) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.cmp op a b) selected _
        (previous.value environment (Expr.cmp op a b) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.cmp op a b) staticFuel enough)

private theorem produce_and_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (a b : Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.and a b) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.and a b)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.and a b)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.and a b)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.and a b) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.and a b) selected _
        (previous.value environment (Expr.and a b) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.and a b) staticFuel enough)

private theorem produce_or_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (a b : Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.or a b) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.or a b)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.or a b)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.or a b)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.or a b) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.or a b) selected _
        (previous.value environment (Expr.or a b) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.or a b) staticFuel enough)

private theorem produce_not_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (e : Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.not e) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.not e)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.not e)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.not e)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.not e) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.not e) selected _
        (previous.value environment (Expr.not e) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.not e) staticFuel enough)

private theorem produce_conv_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (k : Goose.Core.ConvKind) (target : Ty) (e : Expr) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.conv k target e org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.conv k target e org)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.conv k target e org)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.conv k target e org)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.conv k target e org) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.conv k target e org) selected _
        (previous.value environment (Expr.conv k target e org) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.conv k target e org) staticFuel enough)

private theorem produce_call_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (c : Goose.Core.ContextId) (args : List Arg) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.call c args org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.call c args org)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.call c args org)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    simp only [evalProduce]
    apply controlFlow_prefix
    · exact controlFlow_renewProducerChannels channels (Expr.call c args org)
    · intro planned
      apply controlFlow_prefix
      · exact controlFlow_selectProducerChannels environment (Expr.call c args org) planned
      · intro selected
        have argumentsEnough : argumentsQueryBudget args ≤ staticFuel := by
          change argumentsQueryBudget args + 1 ≤ staticFuel + 1 at enough
          omega
        exact previous.call environment c args selected org staticFuel argumentsEnough

private theorem produce_push_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (owner : Place) (e : Expr) (org : Option Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.push owner e org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.push owner e org)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.push owner e org)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.push owner e org)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.push owner e org) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.push owner e org) selected _
        (previous.value environment (Expr.push owner e org) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.push owner e org) staticFuel enough)

private theorem produce_pop_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (owner : Place) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.pop owner org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.pop owner org)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.pop owner org)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.pop owner org)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.pop owner org) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.pop owner org) selected _
        (previous.value environment (Expr.pop owner org) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.pop owner org) staticFuel enough)

private theorem produce_ifE_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (c : Expr) (thenB elseB : Block) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.ifE c thenB elseB org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.ifE c thenB elseB org)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.ifE c thenB elseB org)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.ifE c thenB elseB org)
  · intro planned
    apply controlFlow_prefix
    · evaluation_produce_normal
    · intro selected
      exact evaluationControl_ifResultBlock fuel config previous environment selected c thenB elseB org staticFuel enough id

private theorem produce_blockE_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (b : Block) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.blockE b org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.blockE b org)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.blockE b org)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.blockE b org)
  · intro planned
    apply controlFlow_prefix
    · evaluation_produce_normal
    · intro selected
      exact evaluationControl_producerBlock fuel config previous environment selected b org staticFuel enough

private theorem produce_arrLit_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (es : List Expr) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.arrLit t es org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.arrLit t es org)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.arrLit t es org)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.arrLit t es org)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.arrLit t es org) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.arrLit t es org) selected _
        (previous.value environment (Expr.arrLit t es org) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.arrLit t es org) staticFuel enough)

private theorem produce_fill_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (e : Expr) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.fill t e org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.fill t e org)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.fill t e org)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.fill t e org)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.fill t e org) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.fill t e org) selected _
        (previous.value environment (Expr.fill t e org) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.fill t e org) staticFuel enough)

private theorem produce_structLit_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (es : List Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.structLit t es) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.structLit t es)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.structLit t es)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.structLit t es)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.structLit t es) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.structLit t es) selected _
        (previous.value environment (Expr.structLit t es) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.structLit t es) staticFuel enough)

private theorem produce_bytes_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (data : List UInt8) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.bytes t data org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.bytes t data org)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.bytes t data org)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.bytes t data org)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.bytes t data org) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.bytes t data org) selected _
        (previous.value environment (Expr.bytes t data org) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.bytes t data org) staticFuel enough)

private theorem produce_str_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (args : List PrintArg) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.str t args org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.str t args org)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.str t args org)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.str t args org)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.str t args org) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.str t args org) selected _
        (previous.value environment (Expr.str t args org) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.str t args org) staticFuel enough)

private theorem produce_copy_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (t : Ty) (source : Place) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.copy t source org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.copy t source org)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.copy t source org)) := by
  simp only [evalProduce]
  apply controlFlow_prefix
  · exact controlFlow_renewProducerChannels channels (Expr.copy t source org)
  · intro planned
    apply controlFlow_prefix
    · exact controlFlow_selectProducerChannels environment (Expr.copy t source org) planned
    · intro selected
      exact controlFlow_producerDefault fuel config environment (Expr.copy t source org) selected _
        (previous.value environment (Expr.copy t source org) staticFuel enough)
        (fun destination => previous.build environment destination (Expr.copy t source org) staticFuel enough)

private theorem produce_resultLocal_selected (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (selected planned : List Channel) (var : Goose.Core.VarId) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (.resultLocal var org) ≤ staticFuel + 1) :
    ControlFlowAction environment.act [normalFlow] (fun _ => normalFlow)
      (match selected with
        | [.construct destination] => do
          let .stored stored ← readLoc fuel config.layout ⟨← rootOf environment var, []⟩ | fault .shape
          let named ← match planned with
            | [.completion token] => prepareNamedCarrierAt org token destination stored
            | _ => prepareNamedCarrier org destination stored
          match named with
          | some carrier => pure [carrier]
          | none =>
            buildExpr fuel config environment destination (.resultLocal var org)
            pure [.completed (← completedReceivingDestination destination)]
        | [] => do let _ ← evalValue fuel config environment (.resultLocal var org); pure []
        | [.register _] => do pure [Carrier.register (← evalValue fuel config environment (.resultLocal var org))]
        | _ => fault .arity) := by
  split
  · apply controlFlow_prefix
    · evaluation_produce_normal
    · intro root
      apply controlFlow_prefix
      · evaluation_produce_normal
      · intro value
        cases value <;> try exact controlFlow_stop _ _ _
        case stored stored =>
          have finish (destination : Goose.Core.DestinationId) (named : Option Carrier) :
              ControlFlowAction environment.act [normalFlow] (fun _ => normalFlow)
                (match named with
                  | some carrier => pure [carrier]
                  | none => do
                    buildExpr fuel config environment destination (.resultLocal var org)
                    pure [.completed (← completedReceivingDestination destination)]) := by
            cases named with
            | some carrier => exact controlFlow_pure _ _ _ (List.mem_singleton_self _)
            | none =>
              apply controlFlow_prefix
              · exact previous.build environment _ (.resultLocal var org) (staticFuel + 1) enough
              · intro ignored
                evaluation_produce_normal
          dsimp only
          split
          all_goals apply controlFlow_prefix
          all_goals first
            | (solve | evaluation_produce_normal)
            | (intro named; exact finish _ named)

  · apply controlFlow_map
    exact previous.value environment (.resultLocal var org) (staticFuel + 1) enough
  · apply controlFlow_map
    exact previous.value environment (.resultLocal var org) (staticFuel + 1) enough
  · exact controlFlow_stop _ _ _

private theorem produce_resultLocal_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (var : Goose.Core.VarId) (org : Goose.Core.OriginId) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.resultLocal var org) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.resultLocal var org)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.resultLocal var org)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    simp only [evalProduce]
    apply controlFlow_prefix
    · exact controlFlow_renewProducerChannels channels (Expr.resultLocal var org)
    · intro planned
      apply controlFlow_prefix
      · exact controlFlow_selectProducerChannels environment (Expr.resultLocal var org) planned
      · intro selected
        exact produce_resultLocal_selected fuel config previous environment selected planned var org staticFuel enough

private theorem produce_values_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (operands : List Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget (Expr.values operands) ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel (Expr.values operands)) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels (Expr.values operands)) := by
  cases staticFuel with
  | zero => exact False.elim (Nat.not_le_of_gt (expressionQueryBudget_positive _) enough)
  | succ staticFuel =>
    simp only [evalProduce]
    apply controlFlow_prefix
    · exact controlFlow_renewProducerChannels channels (Expr.values operands)
    · intro planned
      apply controlFlow_prefix
      · evaluation_produce_normal
      · intro selected
        have operandsEnough : expressionListQueryBudget operands ≤ staticFuel := by
          change expressionListQueryBudget operands + 1 ≤ staticFuel + 1 at enough
          omega
        exact previous.operands environment selected operands staticFuel operandsEnough

theorem evaluationControl_produce_succ (fuel : Nat) (config : EvalConfig)
    (previous : EvaluationControlFlows fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (expression : Expr) (staticFuel : Nat)
    (enough : expressionQueryBudget expression ≤ staticFuel) :
    ControlFlowAction environment.act (expressionFlows staticFuel expression) (fun _ => normalFlow)
      (evalProduce (fuel + 1) config environment channels expression) := by
  cases expression with
  | lit t n => exact produce_lit_succ fuel config previous environment channels t n staticFuel enough
  | bool b => exact produce_bool_succ fuel config previous environment channels b staticFuel enough
  | read p => exact produce_read_succ fuel config previous environment channels p staticFuel enough
  | ref m p => exact produce_ref_succ fuel config previous environment channels m p staticFuel enough
  | slice m v lo hi org => exact produce_slice_succ fuel config previous environment channels m v lo hi org staticFuel enough
  | len v => exact produce_len_succ fuel config previous environment channels v staticFuel enough
  | un op e org => exact produce_un_succ fuel config previous environment channels op e org staticFuel enough
  | bin op a b org => exact produce_bin_succ fuel config previous environment channels op a b org staticFuel enough
  | cmp op a b => exact produce_cmp_succ fuel config previous environment channels op a b staticFuel enough
  | and a b => exact produce_and_succ fuel config previous environment channels a b staticFuel enough
  | or a b => exact produce_or_succ fuel config previous environment channels a b staticFuel enough
  | not e => exact produce_not_succ fuel config previous environment channels e staticFuel enough
  | conv k target e org => exact produce_conv_succ fuel config previous environment channels k target e org staticFuel enough
  | call c args org => exact produce_call_succ fuel config previous environment channels c args org staticFuel enough
  | push owner e org => exact produce_push_succ fuel config previous environment channels owner e org staticFuel enough
  | pop owner org => exact produce_pop_succ fuel config previous environment channels owner org staticFuel enough
  | ifE c thenB elseB org => exact produce_ifE_succ fuel config previous environment channels c thenB elseB org staticFuel enough
  | blockE b org => exact produce_blockE_succ fuel config previous environment channels b org staticFuel enough
  | arrLit t es org => exact produce_arrLit_succ fuel config previous environment channels t es org staticFuel enough
  | fill t e org => exact produce_fill_succ fuel config previous environment channels t e org staticFuel enough
  | structLit t es => exact produce_structLit_succ fuel config previous environment channels t es staticFuel enough
  | bytes t data org => exact produce_bytes_succ fuel config previous environment channels t data org staticFuel enough
  | str t args org => exact produce_str_succ fuel config previous environment channels t args org staticFuel enough
  | copy t source org => exact produce_copy_succ fuel config previous environment channels t source org staticFuel enough
  | resultLocal var org => exact produce_resultLocal_succ fuel config previous environment channels var org staticFuel enough
  | values operands => exact produce_values_succ fuel config previous environment channels operands staticFuel enough

#print axioms evaluationControl_produce_succ

end Goose.Proofs.ConstructionDelivery
