import Goose.Lower.GeneratedLoopFrames
import Goose.Lower.TypedBlocks
import Goose.Lower.ReflectionTyped

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

def TypedStatementReflection (fuel : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (statement : Stmt) : Prop :=
  ∀ (env : Env) (state : St) (source : StmtSource cfg env statement state),
    SourceResults source.typingEnv source.rootsEnv results → LoopSourceMatches source.typingEnv loop →
    ∀ (ls after : LS) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerStmt loop statement (lowerEnv cfg.mod env.vars results) ls = ((),after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → LoopDepthFits env loop →
    (match loop with | none => True | some context => LoopTargets cx.fn context) →
    LoopCounterAt loop ls fr → GeneratedBuilderState ls → LoopBuilderFrames loop ls →
    ReflectAtFuel fuel cx pt fr (fun n => execStmt n cfg env statement >>= prepareLoopFlow env loop)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state

def TypedStatementsReflection (fuel : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (statements : List Stmt) : Prop :=
  ∀ (env : Env) (state : St) (source : StmtsSource cfg env statements state),
    SourceResults source.typingEnv source.rootsEnv results → LoopSourceMatches source.typingEnv loop →
    ∀ (ls after : LS) (pt : Pt) (cx : FnCtx) (fr : GIR.Frame),
    lowerStmts loop statements (lowerEnv cfg.mod env.vars results) ls = ((),after) →
    ls.pp = some pt → ExtT after cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results → LoopDepthFits env loop →
    (match loop with | none => True | some context => LoopTargets cx.fn context) →
    LoopCounterAt loop ls fr → GeneratedBuilderState ls → LoopBuilderFrames loop ls →
    ReflectAtFuel fuel cx pt fr (fun n => execStmts n cfg env statements >>= prepareLoopFlow env loop)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state

theorem typedStatementReflection_expr {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {expression : Expr} (origin : OriginId)
    (child : TypedExprReflection fuel cfg results expression) :
    TypedStatementReflection fuel cfg results loop (.expr expression origin) := by
  intro env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq resultsEq depth
    targets counter generated frames
  obtain ⟨expressionSource,typing,roots,_⟩ := source.exprChild
  have expressionMetadata : SourceResults expressionSource.typingEnv expressionSource.rootsEnv results := by
    rw [typing,roots]
    exact metadata
  simp only [lowerStmt,bind_eq] at lowering
  obtain ⟨id,middle,expressionRun,finish⟩ := lowering
  rw [pure_run] at finish
  obtain ⟨_,rfl⟩ := Prod.mk.inj finish
  have first := child env state expressionSource expressionMetadata ls middle id pt cx fr expressionRun point
    extension rel moduleEq resultsEq generated
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => evalExpr n cfg env expression >>= fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr middle loop flow pt' fr') state := by
    refine first.bind ?_ (fun n k bound => (monoAll n k bound).expr cfg env expression)
      (fun _ _ _ _ => MonoM.refl _)
    intro n value next pt' fr' done post residual bound
    exact ReflectAtFuel.ret residual (Or.inl ⟨rfl,post.sub (by simp)⟩)
  refine composition.of_source (fun n => ⟨n + 1,?_⟩)
  cases loop <;> simp only [execStmt,bind_assoc,prepareLoopFlow,prepareReturn,prepareLoopExit,pure_bind]

theorem typedStatementsReflection_nil (fuel : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) : TypedStatementsReflection fuel cfg results loop [] := by
  intro env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq resultsEq depth
    targets counter generated frames
  simp only [lowerStmts,pure_run] at lowering
  obtain ⟨_,rfl⟩ := Prod.mk.inj lowering
  have reflection : ReflectAtFuel fuel cx pt fr (fun _ => pure (Flow.normal .unit))
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr ls loop flow pt' fr') state :=
    ReflectAtFuel.ret fuel (Or.inl ⟨rfl,Post.init rel point⟩)
  refine reflection.of_source (fun _ => ⟨1,?_⟩)
  cases loop <;> simp only [execStmts,prepareLoopFlow,prepareReturn,prepareLoopExit,pure_bind]

theorem typedStatementsReflection_cons {fuel : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {statement : Stmt} {rest : List Stmt}
    (head : TypedStatementReflection fuel cfg results loop statement)
    (tail : ∀ residual, residual ≤ fuel → TypedStatementsReflection residual cfg results loop rest) :
    TypedStatementsReflection fuel cfg results loop (statement :: rest) := by
  intro env state source metadata loops ls after pt cx fr lowering point extension rel moduleEq resultsEq depth
    targets counter generated frames
  obtain ⟨block,live,_,_⟩ := LS.pp_some point
  simp only [lowerStmts,bind_eq] at lowering
  obtain ⟨isLive,initial,test,lowering⟩ := lowering
  rw [isLive_run live] at test
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj test
  simp only [ite_true,bind_eq] at lowering
  obtain ⟨ignored,middle,headRun,tailRun⟩ := lowering
  cases ignored
  have middleExtension := extension.of_adv (advB_lowerStmts loop rest _ _ _ _ tailRun)
  obtain ⟨headSource,typing,roots,nextSource⟩ := source.split
  have headMetadata : SourceResults headSource.typingEnv headSource.rootsEnv results := by
    rw [typing,roots]
    exact metadata
  have headLoops : LoopSourceMatches headSource.typingEnv loop := by rw [typing]; exact loops
  have first := head env state headSource headMetadata headLoops ls middle pt cx fr headRun point middleExtension
    rel moduleEq resultsEq depth targets counter generated frames
  have middleGenerated := generated.lowerStmt loop statement frames.toTargets headRun
  have middleFrames := frames.mono (advB_lowerStmt loop statement _ _ _ _ headRun).ext
  have composition : ReflectAtFuel fuel cx pt fr
      (fun n => (execStmt n cfg env statement >>= prepareLoopFlow env loop) >>= loopStmtsTail n cfg env loop rest)
      (fun flow _ pt' fr' => StatementLoopPost cfg env cx ls fr after loop flow pt' fr') state := by
    refine first.bind ?_
      (fun n k bound => ((monoAll n k bound).stmt cfg env statement).bind (fun _ => MonoM.refl _)) ?_
    · intro n flow next pt' fr' done matched residual bound
      rcases matched with ⟨rfl,post⟩ | returned | ⟨context,loopEq,transfer⟩
      · have raw := preparedLoopFlow_normal_success done
        obtain ⟨tailSource,tailTyping,tailRoots,_⟩ := nextSource n .unit next raw
        have tailMetadata : SourceResults tailSource.typingEnv tailSource.rootsEnv results := by
          apply headMetadata.transport
          · rw [tailTyping]
            exact (headSource.result n (.normal .unit) raw).same.impl
          · rw [tailRoots,roots]
        have tailLoops : LoopSourceMatches tailSource.typingEnv loop := by
          apply headLoops.transport
          rw [tailTyping]
          exact (headSource.result n (.normal .unit) raw).same.loops
        exact (tail residual bound env next tailSource tailMetadata tailLoops middle after pt' cx fr' tailRun post.pp
          extension post.rel moduleEq resultsEq depth targets (counter.afterPost post) middleGenerated middleFrames).mono
          (fun _ _ _ _ matched => StatementLoopPost.prefix rel post counter matched)
      · obtain ⟨value,origin,rfl,site⟩ := returned
        exact ReflectAtFuel.ret residual (Or.inr (Or.inl ⟨value,origin,rfl,site⟩))
      · rcases transfer with ⟨rfl,exit⟩ | ⟨rfl,continued⟩
        · exact ReflectAtFuel.ret residual (Or.inr (Or.inr ⟨context,loopEq,Or.inl ⟨rfl,exit⟩⟩))
        · exact ReflectAtFuel.ret residual (Or.inr (Or.inr ⟨context,loopEq,Or.inr ⟨rfl,continued⟩⟩))
    · intro flow n k bound
      cases flow with
      | normal value => exact ((monoAll n k bound).stmts cfg env rest).bind (fun _ => MonoM.refl _)
      | _ => exact MonoM.refl _
  exact composition.of_source (fun n => ⟨n + 1,congrFun (prepareLoopFlow_execStmts n cfg env loop statement rest) state⟩)

end Goose.Lower
