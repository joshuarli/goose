import Goose.Lower.Validation.SummaryPreservationReplayTypedPlacesContracts
import Goose.Lower.Validation.SummaryPreservationReplayNativeBinary
import Goose.Lower.Validation.SummaryPreservationReplayNativeReference
import Goose.Lower.Validation.SummaryPreservationReplayNativeShortCircuit
import Goose.Lower.Validation.SummaryPreservationReplayTypedRead

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem expressionReplay_literal (integer : IntTy) (value : Int) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.lit integer value) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  have shape : type = .int integer := by
    simp only [Core.tyExpr] at typed
    split at typed
    · exact congrArg Prod.fst ((st_pure_ok _ _ _).mp typed)
    · exact ((rej_ok _ _ _ _).mp typed).elim
  subst type
  exact ready.literal integer value replay

theorem expressionReplay_boolean (value : Bool) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.bool value) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  have shape : type = .bool := congrArg Prod.fst ((st_pure_ok _ _ _).mp typed)
  subst type
  exact ready.boolean value replay

theorem expressionReplay_unary {operand : Expr} (op : UnOp) (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (child : ExpressionReplayAt typingEnv env results vt target scopeCount operand initial upper) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.un op operand origin) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  apply ready.typedUnaryNative typed replay ceiling
    (by simpa only [lowerEnv, ← tables.moduleEq] using Core.tyExpr_un_success_origin_bound typed) generated native
  intro childStart childFinish integer childRoots childAfter childTyped childReplay childEffect childGenerated childNative
  exact child (.int integer) childStart childFinish before childAfter childRoots childTyped childReplay childEffect ready childGenerated childNative

theorem expressionReplay_not {operand : Expr}
    (child : ExpressionReplayAt typingEnv env results vt target scopeCount operand initial upper) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.not operand) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  apply ready.typedNotNative typed replay ceiling generated native
  intro childFinish childRoots childAfter childTyped childReplay childEffect childGenerated childNative
  exact child .bool start childFinish before childAfter childRoots childTyped childReplay childEffect ready childGenerated childNative

theorem expressionReplay_binary {left right : Expr} (op : BinOp) (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (leftChild : ExpressionReplayAt typingEnv env results vt target scopeCount left initial upper)
    (rightChild : ∀ provenance, ExpressionReplayAt typingEnv env results vt target scopeCount right
      (lowerExpr left (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 provenance) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.bin op left right origin) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  apply ready.typedBinaryNative typed replay ceiling
    (by simpa only [lowerEnv, ← tables.moduleEq] using Core.tyExpr_bin_success_origin_bound typed) generated native
  · intro childStart childFinish integer childRoots childAfter childTyped childReplay childEffect childGenerated childNative
    exact leftChild (.int integer) childStart childFinish before childAfter childRoots childTyped childReplay childEffect ready childGenerated childNative
  · intro childStart childFinish integer childBefore childRoots childAfter provenance childTyped childReplay childEffect childReady childGenerated childNative
    exact rightChild provenance (.int integer) childStart childFinish childBefore childAfter childRoots
      childTyped childReplay childEffect childReady childGenerated childNative

theorem expressionReplay_reference {place : Place} (mutability : Mutability)
    (child : PlaceReplayAt typingEnv env results vt target scopeCount place initial upper) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.ref mutability place) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  apply ready.typedReferenceNative typed replay ceiling generated native
  intro info nextCounter childTyped childReplay childEffect childGenerated childNative
  exact child info start nextCounter before after roots childTyped childReplay childEffect ready childGenerated childNative

theorem expressionReplay_read {place : Place} {context : ContextId}
    (checked : SourceReadableEnvironment typingEnv) (tables : SourceRootTables typingEnv env)
    (contextRow : env.mod.contexts[context]? = some env.ctx)
    (implementationRow : env.mod.impls[env.ctx.impl]? = some env.impl)
    (child : PlaceReplayAt typingEnv env results vt target scopeCount place initial upper) :
    ExpressionReplayAt typingEnv env results vt target scopeCount (.read place) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  apply ReplayBuilder.typedRead checked tables contextRow implementationRow typed replay ceiling ready generated native
  intro info nextCounter childRoots childAfter childTyped childReplay childEffect
  have childNative := native.of_prefix (types_emitDef
    (.load (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).1)
    (lowerEnv env.mod env.impl.vars env.impl.results.toList)
    (lowerPlace place (lowerEnv env.mod env.impl.vars env.impl.results.toList) initial).2 _ _ rfl)
  exact child info start nextCounter before childAfter childRoots childTyped childReplay childEffect ready generated childNative

theorem expressionReplay_shortCircuit {left right : Expr} (isAnd : Bool)
    (leftChild : ExpressionReplayAt typingEnv env results vt target scopeCount left initial upper)
    (rightChild : ∀ provenance,
      let le := lowerEnv env.mod env.impl.vars env.impl.results.toList
      let lowered := lowerExpr left le initial
      let forked := scFork isAnd lowered.1 le lowered.2
      ExpressionReplayAt typingEnv env results vt target scopeCount right
        { forked.2 with cur := some forked.1.1 } provenance) :
    ExpressionReplayAt typingEnv env results vt target scopeCount
      (if isAnd then .and left right else .or left right) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  apply ready.typedShortCircuitNative isAnd typed replay ceiling generated native
  · intro nextCounter childRoots childAfter childTyped childReplay childEffect childGenerated childNative
    exact leftChild .bool start nextCounter before childAfter childRoots childTyped childReplay childEffect ready childGenerated childNative
  · intro nextCounter childRoots childBefore provenance
    dsimp only
    intro childTyped childReplay childReady childGenerated childNative
    exact rightChild provenance .bool nextCounter finish childBefore after childRoots
      childTyped childReplay ceiling childReady childGenerated childNative

#print axioms expressionReplay_literal
#print axioms expressionReplay_binary
#print axioms expressionReplay_reference
#print axioms expressionReplay_read
#print axioms expressionReplay_shortCircuit

end Goose.Lower.Validation.SummaryPreservation
