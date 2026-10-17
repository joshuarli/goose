import Goose.Lower.WhileRuntime

namespace Goose.Lower

open Goose.Core Goose.GIR

def TypedWhileSimulation (n : Nat) (cfg : Cfg) (results : List Ty)
    (condition : Expr) (body : Core.Block) (org : OriginId) : Prop :=
  ∀ (env : Env) (state : St) (source : StmtSource cfg env (.while condition body org) state),
    SourceResults source.typingEnv source.rootsEnv results →
    ∀ (ls ls' : LS) (header : BlockId) (cx : FnCtx) (fr : GIR.Frame),
    lowerWhile header (lowerExpr condition)
      (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
      (lowerEnv cfg.mod env.vars results) ls = ((), ls') →
    ls.pp = some (header, 0) → ExtT ls' cx.fn.blocks →
    (∃ block, cx.fn.blocks[header]? = some block ∧ block.params = []) →
    Rel cfg env cx fr ls → cx.cfg.mod = lower cfg.mod → cx.fn.results = results →
    SimEAt cx (header, 0) fr (execWhile n cfg env condition body >>= prepareReturn env)
      (StmtFlowPost cfg env cx ls fr ls') state

theorem typedWhileSimulation_zero (cfg : Cfg) (results : List Ty)
    (condition : Expr) (body : Core.Block) (org : OriginId) :
    TypedWhileSimulation 0 cfg results condition body org := by
  intro env state source hmetadata ls ls' header cx fr hlow hpp hext hheader hrel hgir hresults
  simp only [execWhile]
  exact SimEAt.of_simG SimG.of_timeout_bind state

theorem typedWhileSimulation_succ {n : Nat} {cfg : Cfg} {results : List Ty}
    {condition : Expr} {body : Core.Block} {org : OriginId}
    (hcondition : TypedExprClaim n cfg results condition)
    (hbody : ∀ context, TypedBlockLoopSimulation n cfg results (some context) [] [] false body)
    (hrecur : TypedWhileSimulation n cfg results condition body org) :
    TypedWhileSimulation (n + 1) cfg results condition body org := by
  intro env state source hmetadata ls ls' header cx fr hlow hpp hext hheader hrel hgir hresults
  obtain ⟨conditionSource, conditionTyping, conditionRoots, _⟩ := source.whileConditionChild
  have conditionMetadata : SourceResults conditionSource.typingEnv conditionSource.rootsEnv results := by
    rw [conditionTyping, conditionRoots]
    exact hmetadata
  apply lowerWhile_loop_sim_at n condition body _ ls ls' header cfg env cx state fr
    hlow hpp hext hheader hrel
  · intro id middle lowered point extended related
    exact hcondition env state conditionSource conditionMetadata ls middle id (header, 0) cx fr
      lowered point extended related hgir hresults
  · intro after done depth exitBlock middle id final point frame lowered pointAt extended
      related depthEq targets
    obtain ⟨bodySource, bodyTyping, bodyRoots, _, _⟩ := source.whileBodyChild n done
    have bodyMetadata : SourceResults bodySource.typingEnv bodySource.rootsEnv results := by
      apply hmetadata.transport
      · rw [bodyTyping]
      · rw [bodyRoots]
    have bodyLoops : LoopSourceMatches bodySource.typingEnv (some ⟨depth, exitBlock, .jump header⟩) := by
      rw [LoopSourceMatches, bodyTyping]
      simp
    exact hbody ⟨depth, exitBlock, .jump header⟩ env after bodySource bodyMetadata bodyLoops
      middle final id point cx frame lowered pointAt extended related (by trivial) hgir hresults
      (by change depth ≤ env.scopes.length; exact depthEq ▸ Nat.le_refl _) targets (by trivial)
  · intro afterCondition conditionDone flow afterBody bodyDone reentry frame related
    have nonreturn : ∀ value, flow ≠ .ret value := by
      rcases reentry with ⟨value, rfl⟩ | rfl <;> intro value impossible <;> cases impossible
    have rawBody := preparedReturn_nonreturn_success bodyDone nonreturn
    obtain ⟨next, nextTyping, nextRoots, _, _⟩ := source.whileAfterBody n n flow
      conditionDone rawBody reentry
    have nextMetadata : SourceResults next.typingEnv next.rootsEnv results := by
      rw [nextTyping, nextRoots]
      exact hmetadata
    exact hrecur env afterBody next nextMetadata ls ls' header cx frame hlow hpp hext hheader
      related hgir hresults

theorem typedStatementLoopSimulation_while {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {condition : Expr} {body : Core.Block} {org : OriginId}
    (hwhile : TypedWhileSimulation n cfg results condition body org) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.while condition body org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter
  apply stmt_while_loop_sim_at n loop condition body org _ ls ls' result pt cfg env cx fr state
    hlow hpp hext hrel
  intro header headerState hwhileLower hheaderPP hextHeader hheader hheaderRel
  exact hwhile env state source hmetadata headerState ls' header cx fr hwhileLower hheaderPP
    hextHeader hheader hheaderRel hgir hresults

end Goose.Lower
