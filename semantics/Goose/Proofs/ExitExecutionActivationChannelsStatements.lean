import Goose.Proofs.ExitExecutionActivationChannelsConstructionHelpers

set_option Elab.async false

namespace Goose.Proofs.ExitExecution
open Goose.Construct

local macro "projection_bind " fresh:ident : tactic => `(tactic|
  (apply preservesActivationChannels_bind
   case firstFresh => fresh_eval $fresh))

theorem execStmts_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (statements : List Stmt) :
    PreservesActivationChannels (execStmts (fuel + 1) config environment statements) := by
  cases statements with
  | nil =>
    simp only [execStmts]
    exact preservesActivationChannels_pure _
  | cons statement statements =>
    simp only [execStmts]
    apply preservesActivationChannels_bind _ _ (previous.statement _ _) (previousFresh.statement _ _)
    intro flow
    cases flow with
    | normal value => exact previous.statements _ _
    | breaking value | continuing => exact preservesActivationChannels_pure _

theorem execResultBlock_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (_previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (channels : List Channel) (body : Block) :
    PreservesActivationChannels (execResultBlock (fuel + 1) config environment channels body) := by
  simp only [execResultBlock]
  exact previous.resultBlockWith _ _ _ _

theorem execWhile_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (condition : Expr) (body : Block) :
    PreservesActivationChannels (execWhile (fuel + 1) config environment condition body) := by
  simp only [execWhile]
  activation_channels_helper_eval previousFresh previous config

theorem execRange_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (ty : Goose.Core.IntTy) (first last : Int) (body : Block) :
    PreservesActivationChannels (execRange (fuel + 1) config environment localVar ty first last body) := by
  simp only [execRange]
  activation_channels_helper_eval previousFresh previous config

theorem execEach_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (localVar : Goose.Core.VarId) (index : Option Goose.Core.VarId) (byRef : Bool)
    (body : Block) (view : RuntimeView) (current : Nat) :
    PreservesActivationChannels (execEach (fuel + 1) config environment localVar index byRef body view current) := by
  simp only [execEach]
  activation_channels_helper_eval previousFresh previous config

theorem execBlock_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    PreservesActivationChannels (execBlock (fuel + 1) config environment pre channels body) := by
  cases body
  simp only [execBlock]
  activation_channels_helper_eval previousFresh previous config
  exact preservesActivationChannels_bindAll config _ _ _

theorem loopBody_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) :
    PreservesActivationChannels (loopBody (fuel + 1) config environment pre body) := by
  simp only [loopBody]
  activation_channels_construction_eval previousFresh previous config

theorem execResultBlockWith_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (channels : List Channel) (body : Block) :
    PreservesActivationChannels (execResultBlockWith (fuel + 1) config environment pre channels body) := by
  cases body
  simp only [execResultBlockWith, execResultScope]
  projection_bind previousFresh
  · exact preservesActivationChannels_freshScope
  · intro scopeInst
    apply preservesActivationChannels_mapActivations
    · intro activation
      split <;> rfl
    · activation_channels_construction_eval previousFresh previous config

theorem evalArguments_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (vars : Array LocalVar) (parameters : List Param) (arguments : List Arg) :
    PreservesActivationChannels (evalArguments (fuel + 1) config environment vars parameters arguments) := by
  cases parameters with
  | nil =>
      cases arguments <;> simp only [evalArguments]
      · exact preservesActivationChannels_pure _
      · exact preservesActivationChannels_stop _
  | cons parameter parameters =>
      cases arguments with
      | nil => simpa only [evalArguments, fault] using preservesActivationChannels_stop (Goose.Core.Stop.fault .arity)
      | cons argument arguments =>
          have finish (value : Value) : PreservesActivationChannels (do
              let values ← evalArguments fuel config environment vars parameters arguments
              pure (value :: values)) := by
            projection_bind previousFresh
            · exact previous.arguments _ _ _ _
            · intro _; exact preservesActivationChannels_pure _
          cases argument with
          | byVal expression =>
              simp only [evalArguments]
              projection_bind previousFresh
              · exact previous.value _ _
              · intro value; exact finish value
          | byRef mutability place =>
              simp only [evalArguments]
              projection_bind previousFresh
              · exact previous.place _ _
              · intro location
                projection_bind previousFresh
                · exact preservesActivationChannels_pure _
                · intro value; exact finish value
          | construct expression =>
              simp only [evalArguments]
              split
              · projection_bind previousFresh
                · apply preservesActivationChannels_materializeProducer config
                  case freshAction => exact previousFresh.value _ _
                  exact previous.value _ _
                · intro materialized
                  have finishCarrier (carrier : Carrier) : PreservesActivationChannels (do
                      let value ← carrierValue carrier
                      let values ← evalArguments fuel config environment vars parameters arguments
                      pure (value :: values)) := by
                    projection_bind previousFresh
                    · exact preservesActivationChannels_of_stateQuery _ (stateQuery_carrierValue carrier)
                    · intro value; exact finish value
                  cases materialized with
                  | none =>
                      projection_bind previousFresh
                      · apply preservesActivationChannels_constructLocal
                        case fresh => intro destination; exact previousFresh.build _ _ _
                        intro destination; exact previous.build _ _ _
                      · exact finishCarrier
                  | some source =>
                      projection_bind previousFresh
                      · exact preservesActivationChannels_materializedDestination config _ _ _ _ _ _ _
                      · intro destination
                        projection_bind previousFresh
                        · exact preservesActivationChannels_publishCarriers _ _
                        · intro ignored
                          projection_bind previousFresh
                          · exact preservesActivationChannels_pure _
                          · exact finishCarrier
              · projection_bind previousFresh
                · exact preservesActivationChannels_stop _
                · intro value; exact finish value

private theorem buildExpr_lit_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (t : Goose.Core.IntTy) (n : Int) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«lit» t n)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_bool_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (b : Bool) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«bool» b)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_read_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (p : Place) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«read» p)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_ref_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (m : Goose.Core.Mutability) (p : Place) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«ref» m p)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_slice_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (m : Goose.Core.Mutability) (v : View) (lo hi : Bound) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«slice» m v lo hi org)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_len_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (v : View) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«len» v)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_un_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (op : Goose.Core.UnOp) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«un» op e org)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_bin_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (op : Goose.Core.BinOp) (a b : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«bin» op a b org)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_cmp_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (op : Goose.Core.CmpOp) (a b : Expr) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«cmp» op a b)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_and_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (a b : Expr) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«and» a b)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_or_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (a b : Expr) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«or» a b)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_not_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (e : Expr) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«not» e)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_conv_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (k : Goose.Core.ConvKind) (target : Ty) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«conv» k target e org)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_call_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (c : Goose.Core.ContextId) (args : List Arg) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«call» c args org)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_push_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (owner : Place) (e : Expr) (org : Option Goose.Core.OriginId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«push» owner e org)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_pop_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (owner : Place) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«pop» owner org)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_ifE_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (c : Expr) (thenB elseB : Block) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«ifE» c thenB elseB org)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_blockE_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (b : Block) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«blockE» b org)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_arrLit_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (t : Ty) (es : List Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«arrLit» t es org)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_fill_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (t : Ty) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«fill» t e org)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_structLit_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (t : Ty) (es : List Expr) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«structLit» t es)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_bytes_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (_previousFresh : EvaluationPreservesFresh fuel config)
    (_previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (t : Ty) (data : List UInt8) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«bytes» t data org)) := by
  simp only [buildExpr]
  activation_channels_construction_eval _previousFresh _previous config

private theorem buildExpr_str_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (t : Ty) (args : List PrintArg) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«str» t args org)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_copy_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (t : Ty) (source : Place) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«copy» t source org)) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_resultLocal_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (_previousFresh : EvaluationPreservesFresh fuel config)
    (_previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (var : Goose.Core.VarId) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«resultLocal» var org)) := by
  simp only [buildExpr]
  activation_channels_construction_eval _previousFresh _previous config

private theorem buildExpr_values_nil_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (.values [])) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_values_single_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (operand : Expr) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (.values [operand])) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config

private theorem buildExpr_values_multiple_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (first second : Expr) (rest : List Expr) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (.values (first :: second :: rest))) := by
  simp only [buildExpr]
  activation_channels_construction_eval previousFresh previous config
private theorem buildExpr_values_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId)
    (operands : List Expr) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination (Expr.«values» operands)) := by
  cases operands with
  | nil => exact buildExpr_values_nil_activationChannels_case fuel config previousFresh previous environment destination
  | cons first rest =>
    cases rest with
    | nil => exact buildExpr_values_single_activationChannels_case fuel config previousFresh previous environment destination first
    | cons second rest => exact buildExpr_values_multiple_activationChannels_case fuel config previousFresh previous environment destination first second rest

theorem buildExpr_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (destination : Goose.Core.DestinationId) (expression : Expr) :
    PreservesActivationChannels (buildExpr (fuel + 1) config environment destination expression) := by
  cases expression with
  | «lit» t n =>
    exact buildExpr_lit_activationChannels_case fuel config previousFresh previous environment destination t n
  | «bool» b =>
    exact buildExpr_bool_activationChannels_case fuel config previousFresh previous environment destination b
  | «read» p =>
    exact buildExpr_read_activationChannels_case fuel config previousFresh previous environment destination p
  | «ref» m p =>
    exact buildExpr_ref_activationChannels_case fuel config previousFresh previous environment destination m p
  | «slice» m v lo hi org =>
    exact buildExpr_slice_activationChannels_case fuel config previousFresh previous environment destination m v lo hi org
  | «len» v =>
    exact buildExpr_len_activationChannels_case fuel config previousFresh previous environment destination v
  | «un» op e org =>
    exact buildExpr_un_activationChannels_case fuel config previousFresh previous environment destination op e org
  | «bin» op a b org =>
    exact buildExpr_bin_activationChannels_case fuel config previousFresh previous environment destination op a b org
  | «cmp» op a b =>
    exact buildExpr_cmp_activationChannels_case fuel config previousFresh previous environment destination op a b
  | «and» a b =>
    exact buildExpr_and_activationChannels_case fuel config previousFresh previous environment destination a b
  | «or» a b =>
    exact buildExpr_or_activationChannels_case fuel config previousFresh previous environment destination a b
  | «not» e =>
    exact buildExpr_not_activationChannels_case fuel config previousFresh previous environment destination e
  | «conv» k target e org =>
    exact buildExpr_conv_activationChannels_case fuel config previousFresh previous environment destination k target e org
  | «call» c args org =>
    exact buildExpr_call_activationChannels_case fuel config previousFresh previous environment destination c args org
  | «push» owner e org =>
    exact buildExpr_push_activationChannels_case fuel config previousFresh previous environment destination owner e org
  | «pop» owner org =>
    exact buildExpr_pop_activationChannels_case fuel config previousFresh previous environment destination owner org
  | «ifE» c thenB elseB org =>
    exact buildExpr_ifE_activationChannels_case fuel config previousFresh previous environment destination c thenB elseB org
  | «blockE» b org =>
    exact buildExpr_blockE_activationChannels_case fuel config previousFresh previous environment destination b org
  | «arrLit» t es org =>
    exact buildExpr_arrLit_activationChannels_case fuel config previousFresh previous environment destination t es org
  | «fill» t e org =>
    exact buildExpr_fill_activationChannels_case fuel config previousFresh previous environment destination t e org
  | «structLit» t es =>
    exact buildExpr_structLit_activationChannels_case fuel config previousFresh previous environment destination t es
  | «bytes» t data org =>
    exact buildExpr_bytes_activationChannels_case fuel config previousFresh previous environment destination t data org
  | «str» t args org =>
    exact buildExpr_str_activationChannels_case fuel config previousFresh previous environment destination t args org
  | «copy» t source org =>
    exact buildExpr_copy_activationChannels_case fuel config previousFresh previous environment destination t source org
  | «resultLocal» var org =>
    exact buildExpr_resultLocal_activationChannels_case fuel config previousFresh previous environment destination var org
  | «values» operands =>
    exact buildExpr_values_activationChannels_case fuel config previousFresh previous environment destination operands

theorem execActivationBody_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (pre : List (Goose.Core.VarId × Value)) (body : Block) :
    PreservesActivationChannels (execActivationBody (fuel + 1) config environment pre body) := by
  cases body
  simp only [execActivationBody, execResultScope]
  projection_bind previousFresh
  · projection_bind previousFresh
    · exact preservesActivationChannels_freshScope
    · intro scopeInst
      apply preservesActivationChannels_mapActivations
      · intro activation
        split <;> rfl
      · activation_channels_construction_eval previousFresh previous config
  · intro result
    rcases result with ⟨flow, carriers⟩
    cases flow <;> activation_channels_construction_eval previousFresh previous config

private theorem activationLetPure_bind (value : α) (next : α → EvalM β) :
    ((pure value : EvalM α) >>= next) = next value := rfl

local elab "activation_let_step" fresh:ident previous:ident config:ident environment:ident expression:ident : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  if target.isForall then
    Lean.Elab.Tactic.evalTactic (← `(tactic| intro))
    return
  if target.getAppFn.isConstOf ``PreservesFresh then
    Lean.Elab.Tactic.evalTactic (← `(tactic| solve | fresh_eval $fresh))
    return
  let args := target.getAppArgs
  let some action := args[args.size - 1]? | throwError "expected action"
  if action.isLet then
    Lean.Elab.Tactic.evalTactic (← `(tactic| dsimp only))
    return
  let name := action.getAppFn.constName?
  if name == some ``Bind.bind then
    let args := action.getAppArgs
    let some head := args[args.size - 2]? | throwError "expected head"
    let headName := head.getAppFn.constName?
    if headName == some ``Pure.pure then
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [activationLetPure_bind]))
    else if headName == some ``fault || headName == some ``EvalM.stop then
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_stop _))
    else
      Lean.Elab.Tactic.evalTactic (← `(tactic| projection_bind $fresh))
  else if name == some ``ite then
    Lean.Elab.Tactic.evalTactic (← `(tactic| activation_channels_conditional))
  else if name == some ``evalValue then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($previous).value $environment $expression))
  else if name == some ``buildExpr then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($previous).build $environment _ $expression))
  else if name == some ``materializeProducer then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_materializeProducer $config _ _ _ _
        (($previous).value $environment $expression) (($fresh).value $environment $expression)))
  else if name == some ``Pure.pure then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_pure _))
  else if name == some ``fault || name == some ``EvalM.stop then
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_stop _))
  else if name == some ``EvalM.get || (name.map (·.getPrefix) == some `Goose.Construct) then
    let some (.str _ suffix) := name | throwError "expected primitive name"
    let preservedName := `Goose.Proofs.ExitExecution ++ .str .anonymous ("preservesActivationChannels_" ++ suffix)
    if (← Lean.getEnv).contains preservedName then
      let preserved := Lean.mkIdent preservedName
      Lean.Elab.Tactic.evalTactic (← `(tactic| first | apply $preserved $config | apply $preserved))
    else
      let query := Lean.mkIdent (`Goose.Proofs.ExitExecution ++ .str .anonymous ("stateQuery_" ++ suffix))
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact preservesActivationChannels_of_stateQuery _ (by apply $query)))
  else
    Lean.Elab.Tactic.evalTactic (← `(tactic| split))

private theorem execStmt_letS_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (x : Goose.Core.VarId) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«letS» x e org)) := by
  simp only [execStmt]
  repeat' first
    | contradiction
    | activation_let_step previousFresh previous config environment e

private theorem execStmt_assign_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (p : Place) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«assign» p e org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_assignOp_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (op : Goose.Core.BinOp) (p : Place) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«assignOp» op p e org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_rebind_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (x : Goose.Core.VarId) (e : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«rebind» x e org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_expr_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (e : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«expr» e org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_append_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (owner : Place) (src : View) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«append» owner src org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_popN_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (owner : Place) (count : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«popN» owner count org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_resize_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (owner : Place) (size : Expr) (fill : Option Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«resize» owner size fill org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_clear_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (owner : Place) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«clear» owner org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_assignWhole_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (owner : Place) (replacement : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«assignWhole» owner replacement org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_ifS_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (c : Expr) (thenB : Block) (elseB : Option Block) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«ifS» c thenB elseB org)) := by
  cases elseB <;> simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_while_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (_previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (c : Expr) (body : Block) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«while» c body org)) := by
  simp only [execStmt]
  activation_channels_construction_eval _previousFresh previous config

private theorem execStmt_forRange_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (x : Goose.Core.VarId) (lo hi : Expr) (body : Block) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«forRange» x lo hi body org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_forEach_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (x : Goose.Core.VarId) (index : Option Goose.Core.VarId) (v : View) (byRef : Bool) (body : Block) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«forEach» x index v byRef body org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_receive_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (vars : List Goose.Core.VarId) (producer : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«receive» vars producer org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_appendValue_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (owner : Place) (producer : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«appendValue» owner producer org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_appendConstruct_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (owner : Place) (producer : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«appendConstruct» owner producer org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_retValues_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (operands : List Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«retValues» operands org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_retForward_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (call : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«retForward» call org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_returnFrom_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (target : Nat) (operands : List Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«returnFrom» target operands org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_returnFromForward_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (target : Nat) (call : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«returnFromForward» target call org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_breakValue_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (value : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«breakValue» value org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_ret_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (e : Option Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«ret» e org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_brk_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (_previousFresh : EvaluationPreservesFresh fuel config)
    (_previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«brk» org)) := by
  simp only [execStmt]
  activation_channels_construction_eval _previousFresh _previous config

private theorem execStmt_cont_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (_previousFresh : EvaluationPreservesFresh fuel config)
    (_previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«cont» org)) := by
  simp only [execStmt]
  activation_channels_construction_eval _previousFresh _previous config

private theorem execStmt_print_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (args : List PrintArg) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«print» args org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_assertS_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (e : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«assertS» e org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

private theorem execStmt_abort_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (_previousFresh : EvaluationPreservesFresh fuel config)
    (_previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (message : String) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«abort» message org)) := by
  simp only [execStmt]
  activation_channels_construction_eval _previousFresh _previous config

private theorem execStmt_exit_activationChannels_case (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (e : Expr) (org : Goose.Core.OriginId) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment (Stmt.«exit» e org)) := by
  simp only [execStmt]
  activation_channels_construction_eval previousFresh previous config

theorem execStmt_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (statement : Stmt) :
    PreservesActivationChannels (execStmt (fuel + 1) config environment statement) := by
  cases statement with
  | «letS» x e org =>
    exact execStmt_letS_activationChannels_case fuel config previousFresh previous environment x e org
  | «assign» p e org =>
    exact execStmt_assign_activationChannels_case fuel config previousFresh previous environment p e org
  | «assignOp» op p e org =>
    exact execStmt_assignOp_activationChannels_case fuel config previousFresh previous environment op p e org
  | «rebind» x e org =>
    exact execStmt_rebind_activationChannels_case fuel config previousFresh previous environment x e org
  | «expr» e org =>
    exact execStmt_expr_activationChannels_case fuel config previousFresh previous environment e org
  | «append» owner src org =>
    exact execStmt_append_activationChannels_case fuel config previousFresh previous environment owner src org
  | «popN» owner count org =>
    exact execStmt_popN_activationChannels_case fuel config previousFresh previous environment owner count org
  | «resize» owner size fill org =>
    exact execStmt_resize_activationChannels_case fuel config previousFresh previous environment owner size fill org
  | «clear» owner org =>
    exact execStmt_clear_activationChannels_case fuel config previousFresh previous environment owner org
  | «assignWhole» owner replacement org =>
    exact execStmt_assignWhole_activationChannels_case fuel config previousFresh previous environment owner replacement org
  | «ifS» c thenB elseB org =>
    exact execStmt_ifS_activationChannels_case fuel config previousFresh previous environment c thenB elseB org
  | «while» c body org =>
    exact execStmt_while_activationChannels_case fuel config previousFresh previous environment c body org
  | «forRange» x lo hi body org =>
    exact execStmt_forRange_activationChannels_case fuel config previousFresh previous environment x lo hi body org
  | «forEach» x index v byRef body org =>
    exact execStmt_forEach_activationChannels_case fuel config previousFresh previous environment x index v byRef body org
  | «receive» vars producer org =>
    exact execStmt_receive_activationChannels_case fuel config previousFresh previous environment vars producer org
  | «appendValue» owner producer org =>
    exact execStmt_appendValue_activationChannels_case fuel config previousFresh previous environment owner producer org
  | «appendConstruct» owner producer org =>
    exact execStmt_appendConstruct_activationChannels_case fuel config previousFresh previous environment owner producer org
  | «retValues» operands org =>
    exact execStmt_retValues_activationChannels_case fuel config previousFresh previous environment operands org
  | «retForward» call org =>
    exact execStmt_retForward_activationChannels_case fuel config previousFresh previous environment call org
  | «returnFrom» target operands org =>
    exact execStmt_returnFrom_activationChannels_case fuel config previousFresh previous environment target operands org
  | «returnFromForward» target call org =>
    exact execStmt_returnFromForward_activationChannels_case fuel config previousFresh previous environment target call org
  | «breakValue» value org =>
    exact execStmt_breakValue_activationChannels_case fuel config previousFresh previous environment value org
  | «ret» e org =>
    exact execStmt_ret_activationChannels_case fuel config previousFresh previous environment e org
  | «brk» org =>
    exact execStmt_brk_activationChannels_case fuel config previousFresh previous environment org
  | «cont» org =>
    exact execStmt_cont_activationChannels_case fuel config previousFresh previous environment org
  | «print» args org =>
    exact execStmt_print_activationChannels_case fuel config previousFresh previous environment args org
  | «assertS» e org =>
    exact execStmt_assertS_activationChannels_case fuel config previousFresh previous environment e org
  | «abort» message org =>
    exact execStmt_abort_activationChannels_case fuel config previousFresh previous environment message org
  | «exit» e org =>
    exact execStmt_exit_activationChannels_case fuel config previousFresh previous environment e org

theorem pushValue_activationChannels_succ (fuel : Nat) (config : EvalConfig)
    (previousFresh : EvaluationPreservesFresh fuel config)
    (previous : EvaluationActivationChannels fuel config) (environment : RuntimeActivation)
    (owner : Place) (expression : Expr) (origin : Goose.Core.OriginId) :
    PreservesActivationChannels (pushValue (fuel + 1) config environment owner expression origin) := by
  simp only [pushValue]
  activation_channels_construction_eval previousFresh previous config

end Goose.Proofs.ExitExecution
