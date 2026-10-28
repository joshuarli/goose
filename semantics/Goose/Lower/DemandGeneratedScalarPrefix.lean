import Goose.Lower.DemandGeneratedExpressionPrefixNot
import Goose.Lower.DemandGeneratedExpressionPrefixUnary
import Goose.Lower.DemandGeneratedExpressionPrefixConvert
import Goose.Lower.DemandGeneratedExpressionPrefixBinary
import Goose.Lower.DemandGeneratedExpressionPrefixCompare
import Goose.Lower.DemandGeneratedLoad
import Goose.Lower.DemandScalarReadCursor

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound

abbrev CanonicalExpressionPrefixCursor {cfg : Cfg} {env : Env} (cx : FnCtx)
    {expression : Expr} {state : St} (source : ExprSource cfg env expression state)
    (_before _built : LS) (_initial : GIR.Frame) (_start : Pt) (map _required : RetainedSsaMap)
    (runtime : DemandRuntimePoint) : Prop := CanonicalExpressionDemand map cx source runtime

theorem GeneratedExpressionPrefixFamily.mapCursor {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    {selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner}
    {loop : Option LoopCtx} {expression : Expr}
    {cursor next : ∀ {expression : Expr} {state : St}, ExprSource cfg env expression state →
      LS → LS → GIR.Frame → Pt → RetainedSsaMap → RetainedSsaMap → DemandRuntimePoint → Prop}
    (family : GeneratedExpressionPrefixFamily cx results selected loop expression cursor)
    (convert : ∀ {expression : Expr} {state : St} (source : ExprSource cfg env expression state)
      {before built : LS} {initial : GIR.Frame} {start : Pt} {map required : RetainedSsaMap} {runtime : DemandRuntimePoint},
      cursor source before built initial start map required runtime → next source before built initial start map required runtime) :
    GeneratedExpressionPrefixFamily cx results selected loop expression next := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  have decomposition := family source owned occurrence rows coverage admitted bounded realized input extended steps
  refine ⟨decomposition.sourceOwner, decomposition.coverage, ?_⟩
  cases decomposition.progress with
  | interior demanded => exact .interior (convert source demanded)
  | complete count prefixSteps residual evaluated post => exact .complete count prefixSteps residual evaluated post

theorem accepted_generated_read_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) {place : Place} (form : ScalarReadPlace place) :
    GeneratedExpressionPrefixFamily cx results selected loop (.read place)
      (@CanonicalExpressionPrefixCursor cfg env cx) := by
  apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_read_definition_prefix_family selected loop form)
  intro expression state source before built initial start map required runtime cursor
  exact cursor.demanded

theorem accepted_generated_global_read_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) (global : GlobalId) :
    GeneratedExpressionPrefixFamily cx results selected loop (.read (.global global))
      (@CanonicalExpressionPrefixCursor cfg env cx) :=
  accepted_generated_read_prefix_family selected loop (.global global)

inductive ScalarPrefixExpression : Expr → Prop
  | slotRead (slot : VarId) : ScalarPrefixExpression (.read (.var slot))
  | globalRead (global : GlobalId) : ScalarPrefixExpression (.read (.global global))
  | literal (type : IntTy) (number : Int) : ScalarPrefixExpression (.lit type number)
  | boolean (value : Bool) : ScalarPrefixExpression (.bool value)
  | not {expression : Expr} (child : ScalarPrefixExpression expression) : ScalarPrefixExpression (.not expression)
  | unary (operation : UnOp) {expression : Expr} (origin : OriginId) (child : ScalarPrefixExpression expression) :
      ScalarPrefixExpression (.un operation expression origin)
  | convert (kind : ConvKind) (target : IntTy) {expression : Expr} (origin : OriginId) (child : ScalarPrefixExpression expression) :
      ScalarPrefixExpression (.conv kind (.int target) expression origin)
  | binary (operation : BinOp) {left right : Expr} (origin : OriginId)
      (leftChild : ScalarPrefixExpression left) (rightChild : ScalarPrefixExpression right) :
      ScalarPrefixExpression (.bin operation left right origin)
  | compare (operation : CmpOp) {left right : Expr}
      (leftChild : ScalarPrefixExpression left) (rightChild : ScalarPrefixExpression right) :
      ScalarPrefixExpression (.cmp operation left right)

theorem accepted_generated_scalar_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) {expression : Expr} (form : ScalarPrefixExpression expression) :
    GeneratedExpressionPrefixFamily cx results selected loop expression (@CanonicalExpressionPrefixCursor cfg env cx) := by
  induction form with
  | slotRead slot =>
    exact accepted_generated_read_prefix_family selected loop (.slot slot)
  | globalRead global =>
    exact accepted_generated_read_prefix_family selected loop (.global global)
  | literal type number =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_literal_prefix_family selected loop type number)
    intro expression state source before built initial start map required runtime cursor
    exact .entry cursor.frame
  | boolean value =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_boolean_prefix_family selected loop value)
    intro expression state source before built initial start map required runtime cursor
    exact .entry cursor.frame
  | not child ih =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_not_prefix_family selected loop _ _ ih)
    intro expression state source before built initial start map required runtime cursor
    exact cursor.canonical (by intros; assumption)
  | unary operation origin child ih =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_unary_prefix_family selected loop operation _ origin _ ih)
    intro expression state source before built initial start map required runtime cursor
    exact cursor.canonical (by intros; assumption)
  | convert kind target origin child ih =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_convert_prefix_family selected loop kind target _ origin _ ih)
    intro expression state source before built initial start map required runtime cursor
    exact cursor.canonical (by intros; assumption)
  | binary operation origin left right leftIH rightIH =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_binary_prefix_family selected loop operation _ _ origin _ _ leftIH rightIH)
    intro expression state source before built initial start map required runtime cursor
    exact cursor.canonical (by intros; assumption) (by intros; assumption)
  | compare operation left right leftIH rightIH =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_compare_prefix_family selected loop operation _ _ _ _ leftIH rightIH)
    intro expression state source before built initial start map required runtime cursor
    exact cursor.canonical (by intros; assumption) (by intros; assumption)

#print axioms accepted_generated_read_prefix_family
#print axioms GeneratedExpressionPrefixFamily.mapCursor
#print axioms accepted_generated_scalar_prefix_family

end Goose.Lower
