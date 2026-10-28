import Goose.Lower.DemandGeneratedScalarPrefix

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

structure GeneratedScalarDefinitionCursor {cfg : Cfg} {env : Env} (cx : FnCtx)
    {expression : Expr} {state : St} (source : ExprSource cfg env expression state)
    (_before _built : LS) (_initial : GIR.Frame) (_start : Pt) (map _required : RetainedSsaMap)
    (runtime : DemandRuntimePoint) : Prop where
  demanded : CanonicalExpressionDemand map cx source runtime
  instruction : ∃ id op, instAt cx.fn runtime.point = some (.def id op)

theorem accepted_generated_scalar_definition_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) {expression : Expr} (form : ScalarPrefixExpression expression) :
    GeneratedExpressionPrefixFamily cx results selected loop expression (@GeneratedScalarDefinitionCursor cfg env cx) := by
  induction form with
  | slotRead slot =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_read_definition_prefix_family selected loop (.slot slot))
    intro expression state source before built initial start map required runtime cursor
    obtain ⟨label, id, op, site⟩ := cursor.instruction
    exact ⟨cursor.demanded, id, op, site.instruction⟩
  | globalRead global =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_read_definition_prefix_family selected loop (.global global))
    intro expression state source before built initial start map required runtime cursor
    obtain ⟨label, id, op, site⟩ := cursor.instruction
    exact ⟨cursor.demanded, id, op, site.instruction⟩
  | literal type number =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_literal_prefix_family selected loop type number)
    intro expression state source before built initial start map required runtime cursor
    obtain ⟨form, entry, site⟩ := cursor.site
    exact ⟨.entry cursor.demanded, _, _, site.instruction⟩
  | boolean value =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_boolean_prefix_family selected loop value)
    intro expression state source before built initial start map required runtime cursor
    obtain ⟨form, entry, site⟩ := cursor.site
    exact ⟨.entry cursor.demanded, _, _, site.instruction⟩
  | not child ih =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_not_prefix_family selected loop _ _ ih)
    intro expression state source before built initial start map required runtime cursor
    have demanded := cursor.canonical (by intro expression state child before built initial start map required runtime cursor; exact cursor.demanded)
    cases cursor with
    | child child metadata owned occurrence rows coverage cursor => exact ⟨demanded, cursor.instruction⟩
    | operation child metadata owned site coverage admitted bounded same carried => exact ⟨demanded, _, _, site.instruction⟩
  | unary operation origin child ih =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_unary_prefix_family selected loop operation _ origin _ ih)
    intro expression state source before built initial start map required runtime cursor
    have demanded := cursor.canonical (by intro expression state child before built initial start map required runtime cursor; exact cursor.demanded)
    cases cursor with
    | child child metadata owned occurrence rows coverage cursor => exact ⟨demanded, cursor.instruction⟩
    | operation child metadata owned site coverage admitted bounded same carried => exact ⟨demanded, _, _, site.instruction⟩
  | convert kind target origin child ih =>
    apply GeneratedExpressionPrefixFamily.mapCursor (accepted_generated_convert_prefix_family selected loop kind target _ origin _ ih)
    intro expression state source before built initial start map required runtime cursor
    have demanded := cursor.canonical (by intro expression state child before built initial start map required runtime cursor; exact cursor.demanded)
    cases cursor with
    | child child metadata owned occurrence rows coverage cursor => exact ⟨demanded, cursor.instruction⟩
    | operation child metadata owned site coverage admitted bounded same carried => exact ⟨demanded, _, _, site.instruction⟩
  | binary operation origin first second firstIH secondIH =>
    apply GeneratedExpressionPrefixFamily.mapCursor
      (accepted_generated_binary_prefix_family selected loop operation _ _ origin _ _ firstIH secondIH)
    intro expression state source before built initial start map required runtime cursor
    have demanded := cursor.canonical (by intro expression state child before built initial start map required runtime cursor; exact cursor.demanded) (by intro expression state child before built initial start map required runtime cursor; exact cursor.demanded)
    cases cursor with
    | left child metadata owned occurrence rows coverage cursor => exact ⟨demanded, cursor.instruction⟩
    | right child metadata owned occurrence rows coverage leftPost cursor => exact ⟨demanded, cursor.instruction⟩
    | operation child metadata owned site coverage admitted bounded same carried => exact ⟨demanded, _, _, site.instruction⟩
  | compare operation first second firstIH secondIH =>
    apply GeneratedExpressionPrefixFamily.mapCursor
      (accepted_generated_compare_prefix_family selected loop operation _ _ _ _ firstIH secondIH)
    intro expression state source before built initial start map required runtime cursor
    have demanded := cursor.canonical (by intro expression state child before built initial start map required runtime cursor; exact cursor.demanded) (by intro expression state child before built initial start map required runtime cursor; exact cursor.demanded)
    cases cursor with
    | left child metadata owned occurrence rows coverage cursor => exact ⟨demanded, cursor.instruction⟩
    | right child metadata owned occurrence rows coverage leftPost cursor => exact ⟨demanded, cursor.instruction⟩
    | operation child metadata owned site coverage admitted bounded same carried => exact ⟨demanded, _, _, site.instruction⟩

#print axioms accepted_generated_scalar_definition_prefix_family
end Goose.Lower
