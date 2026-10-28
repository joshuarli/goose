import Goose.Lower.DemandGeneratedExpressionPrefixNot
import Goose.Lower.DemandGeneratedExpressionPrefixUnary
import Goose.Lower.DemandGeneratedExpressionPrefixConvert
import Goose.Lower.DemandGeneratedExpressionPrefixBinary
import Goose.Lower.DemandGeneratedExpressionPrefixCompare
import Goose.Lower.DemandGeneratedLoad

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

inductive ScalarReadPlace : Place → Prop
  | global (global : GlobalId) : ScalarReadPlace (.global global)
  | slot (slot : VarId) : ScalarReadPlace (.var slot)

theorem accepted_generated_read_prefix_family {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {root : DemandNode} {owner : Nat}
    (selected : GeneratedDemandRootSelection cfg.mod cx.fn (lowerEnv cfg.mod env.vars results) root owner)
    (loop : Option LoopCtx) {place : Place} (form : ScalarReadPlace place) :
    GeneratedExpressionPrefixFamily cx results selected loop (.read place)
      (@CanonicalExpressionPrefixCursor cfg env cx) := by
  intro state source before owned occurrence required map rows coverage admitted bounded initial start realized input extended taken reached steps
  let le := lowerEnv cfg.mod env.vars results
  let addressed := lowerPlace place le before
  obtain ⟨child, typing, roots, metadata⟩ := source.readChild
  have childOccurrence : GeneratedDemandOccurrence cfg.mod cx.fn le root child.path (.place place) before := by
    rw [metadata.path]
    exact .first occurrence (.expressionPlace rfl)
  have childRows : GeneratedDemandRows cfg.mod child.rootsEnv.access childOccurrence required := by
    have inherited : GeneratedDemandRows cfg.mod source.rootsEnv.access (.first occurrence (.expressionPlace rfl)) required := .first (first := .expressionPlace rfl) rows
    simpa only [roots, metadata.path] using inherited
  obtain ⟨location, placed, post, firstStep⟩ : ∃ location : Loc,
      evalPlace 1 cfg env place state = .ok location state ∧
      Post cfg env cx before initial addressed.2 (initial.set addressed.1 (.val (.ref location)))
        (start.1, start.2 + 1) [(addressed.1, .val (.ref location))] ∧
      ∀ fuel, DemandInstructionStep cx fuel ⟨start, initial, state⟩
        ⟨(start.1, start.2 + 1), initial.set addressed.1 (.val (.ref location)), state⟩ := by
    cases form with
    | global global =>
      have site := GeneratedDemandInstruction.globalAddress_auto childOccurrence childRows input.atPoint
        (generated_read_place_extended extended)
      have post := (Post.def_leaf (Post.init input.related input.atPoint)
        (show emitDef (.globalAddr global) le before = (addressed.1, addressed.2) from rfl)
        (generated_read_place_extended extended) (.val (.ref ⟨.global global, []⟩))).1
      refine ⟨⟨.global global, []⟩, ?_, post, ?_⟩
      · simp only [evalPlace, pure_apply]
      · intro fuel
        apply DemandInstructionStep.definition site.instruction
        simp only [execOp, execPure, pure_apply]
    | slot slot =>
      have typed := child.typed
      simp only [tyPlace] at typed
      obtain ⟨binding, next, checked, resultType⟩ := (st_bind_ok _ _ _ _).1 typed
      have visible := ((varOf_ok child.typingEnv slot child.typingStart (binding, next)).1 checked).1
      obtain ⟨binding, scope, old, variableAt, scopeAt, parameter, stored, shape⟩ := child.frame.bindings slot visible
      let location : Loc := ⟨.local env.act scope slot, []⟩
      have site := GeneratedDemandInstruction.slotAddress_auto childOccurrence childRows input.atPoint
        (generated_read_place_extended extended)
      have post := (Post.def_leaf (Post.init input.related input.atPoint)
        (show emitDef (.slotAddr slot) le before = (addressed.1, addressed.2) from rfl)
        (generated_read_place_extended extended) (.val (.ref location))).1
      refine ⟨location, ?_, post, ?_⟩
      · simp [evalPlace, rootOf, variableAt, scopeAt, location, bind_apply, pure_apply]
      · intro fuel
        apply DemandInstructionStep.definition site.instruction
        simp only [execOp, execPure, slotRoot_eq input.related]
        simp [rootOf, variableAt, scopeAt, location, bind_apply, pure_apply]
  let middle : DemandRuntimePoint := ⟨(start.1, start.2 + 1), initial.set addressed.1 (.val (.ref location)), state⟩
  have carried := realized.retained post.same bounded.1 bounded.2 RetainsAliases.refl
  have atMiddle : DemandFrameAt cfg env cx source.world source.typingEnv source.rootsEnv source.context.outputFuture
      map.values map.runs middle := by
    have result := child.result 1 location placed
    have frame := result.frame
    rw [metadata.world, typing, roots, metadata.outputFuture] at frame
    exact ⟨⟨_, post.pp, post.rel⟩, frame, carried⟩
  refine ⟨owned, coverage, ?_⟩
  rcases steps.uncons with ⟨rfl, rfl⟩ | ⟨length, current, rfl, actual, tail⟩
  · exact .interior (.entry ⟨⟨_, input.atPoint, input.related⟩, source.frame, realized⟩)
  · obtain ⟨fuel, actualStep⟩ := runtimeStep_demandInstructionStep actual
    have same := actualStep.deterministic (firstStep fuel)
    have currentEq : current = middle := (show current = ⟨current.point, current.frame, current.state⟩ from by cases current; rfl).trans same
    subst current
    rcases tail.uncons with ⟨rfl, rfl⟩ | ⟨remaining, boundary, rfl, loaded, residual⟩
    · exact .interior (.exit atMiddle)
    · obtain ⟨_, _, _, _, value, _, _, evaluated, finalPost, _, _⟩ :=
        accepted_generated_load_runtime_step source occurrence rows coverage placed post (bounded.mono post.mono) carried extended loaded
      have result := source.result 2 value evaluated
      have final := ExpressionDemandBoundary.of_result result admitted bounded realized finalPost
      exact .complete (by omega) (.next actual (.next loaded (.zero _))) residual evaluated final

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
