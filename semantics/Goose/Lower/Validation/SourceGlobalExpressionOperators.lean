import Goose.Lower.Validation.SourceGlobalReplayContracts
import Goose.Lower.Validation.SummaryPreservationReplayNativeBinary
import Goose.Lower.Validation.SummaryPreservationReplayNativeReference
import Goose.Lower.Validation.SummaryPreservationReplayNativeShortCircuit
import Goose.Lower.Validation.SummaryPreservationReplayTypedRead

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

variable {typingEnv : TEnv} {env : PEnv} {results : Array (List RootRef)}
  {vt : Array (Option VTy)} {func : Func} {returnTypes : List Ty} {slots : Array (List RootRef)} {target : Core.Eff} {scopeCount : Nat} {initial : LS} {upper : Prov}

theorem globalExpressionReplay_literal (integer : IntTy) (value : Int) :
    GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount (.lit integer value) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  have shape : type = .int integer := by
    simp only [Core.tyExpr] at typed
    split at typed
    · exact congrArg Prod.fst ((st_pure_ok _ _ _).mp typed)
    · exact ((rej_ok _ _ _ _).mp typed).elim
  subst type
  exact ready.literal integer value replay

theorem globalExpressionReplay_boolean (value : Bool) :
    GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount (.bool value) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  have shape : type = .bool := congrArg Prod.fst ((st_pure_ok _ _ _).mp typed)
  subst type
  exact ready.boolean value replay

theorem globalExpressionReplay_unary {operand : Expr} (op : UnOp) (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (child : GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount operand initial upper) :
    GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount (.un op operand origin) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  apply ready.typedUnaryNative typed replay ceiling
    (by simpa only [lowerEnv, ← tables.moduleEq] using Core.tyExpr_un_success_origin_bound typed) generated native
  intro childStart childFinish integer childRoots childAfter childTyped childReplay childEffect childGenerated childNative
  exact child (.int integer) childStart childFinish before childAfter childRoots childTyped childReplay childEffect ready childGenerated childNative

theorem globalExpressionReplay_not {operand : Expr}
    (child : GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount operand initial upper) :
    GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount (.not operand) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  apply ready.typedNotNative typed replay ceiling generated native
  intro childFinish childRoots childAfter childTyped childReplay childEffect childGenerated childNative
  exact child .bool start childFinish before childAfter childRoots childTyped childReplay childEffect ready childGenerated childNative

theorem globalExpressionReplay_binary {left right : Expr} (op : BinOp) (origin : OriginId)
    (tables : SourceRootTables typingEnv env)
    (leftChild : GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount left initial upper)
    (rightChild : ∀ provenance, GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount right
      (lowerExpr left (lowerEnv env.mod env.impl.vars returnTypes) initial).2 provenance) :
    GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount (.bin op left right origin) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  apply ready.typedBinaryNative typed replay ceiling
    (by simpa only [lowerEnv, ← tables.moduleEq] using Core.tyExpr_bin_success_origin_bound typed) generated native
  · intro childStart childFinish integer childRoots childAfter childTyped childReplay childEffect childGenerated childNative
    exact leftChild (.int integer) childStart childFinish before childAfter childRoots childTyped childReplay childEffect ready childGenerated childNative
  · intro childStart childFinish integer childBefore childRoots childAfter provenance childTyped childReplay childEffect childReady childGenerated childNative
    exact rightChild provenance (.int integer) childStart childFinish childBefore childAfter childRoots
      childTyped childReplay childEffect childReady childGenerated childNative

theorem globalExpressionReplay_reference {place : Place} (mutability : Mutability)
    (child : GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount place initial upper) :
    GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount (.ref mutability place) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  apply ready.typedReferenceNative typed replay ceiling generated native
  intro info nextCounter childTyped childReplay childEffect childGenerated childNative
  exact child info start nextCounter before after roots childTyped childReplay childEffect ready childGenerated childNative

theorem globalExpressionReplay_read {place : Place}
    (checked : SourceReadableEnvironment typingEnv) (tables : SourceRootTables typingEnv env)
    (variables : typingEnv.vars = #[]) (closed : ParameterRootsClosed func)
    (child : GlobalPlaceReplayAt typingEnv env results vt func returnTypes slots target scopeCount place initial upper) :
    GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount (.read place) initial upper := by
  intro type start finish before after roots typed replay ceiling ready generated native
  exact ReplayBuilder.typedGlobalRead checked variables tables closed typed replay ceiling ready generated native child

theorem globalExpressionReplay_shortCircuit {left right : Expr} (isAnd : Bool)
    (leftChild : GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount left initial upper)
    (rightChild : ∀ provenance,
      let le := lowerEnv env.mod env.impl.vars returnTypes
      let lowered := lowerExpr left le initial
      let forked := scFork isAnd lowered.1 le lowered.2
      GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount right
        { forked.2 with cur := some forked.1.1 } provenance) :
    GlobalExpressionReplayAt typingEnv env results vt func returnTypes slots target scopeCount
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

#print axioms globalExpressionReplay_literal
#print axioms globalExpressionReplay_binary
#print axioms globalExpressionReplay_reference
#print axioms globalExpressionReplay_read
#print axioms globalExpressionReplay_shortCircuit

end Goose.Lower.Validation.SummaryPreservation
