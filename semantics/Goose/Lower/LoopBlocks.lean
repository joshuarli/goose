import Goose.Lower.LoopPrepare

namespace Goose.Lower

open Goose.Core Goose.GIR

def BlockLoopPost (cfg : Cfg) (env : Env) (cx : FnCtx) (ls : LS) (fr : GIR.Frame)
    (ls' : LS) (loop : Option LoopCtx) (block : Core.Block) (want : Bool) (result : ValueId)
    (flow : Flow) (pt' : Pt) (fr' : GIR.Frame) : Prop :=
  (∃ value, flow = .normal value ∧ (block.value = none → value = .unit) ∧
    Post cfg env cx ls fr ls' fr' pt' (blockCells block want result value)) ∨
  ReturnedAt cx flow pt' fr' ∨
  (∃ context, loop = some context ∧
    ((flow = .brk ∧ ExitedAt context fr ls.vals.size
      (env.scopes.drop (env.scopes.length - context.depth)) pt' fr') ∨
    (flow = .cont ∧ ContinuedAt context fr ls.vals.size
      (env.scopes.drop (env.scopes.length - context.depth)) pt' fr')))

theorem loopScopeSuffix_entered (env : Env) (scope : ScopeId) (scopeInstance : ScopeInst)
    (depth : Nat) (hdepth : depth ≤ env.scopes.length) :
    (((scope, scopeInstance) :: env.scopes).drop
      (((scope, scopeInstance) :: env.scopes).length - depth)) =
    env.scopes.drop (env.scopes.length - depth) := by
  have hlength : ((scope, scopeInstance) :: env.scopes).length - depth =
      (env.scopes.length - depth) + 1 := by simp only [List.length_cons]; omega
  rw [hlength, List.drop_succ_cons]

theorem StatementLoopPost.rescope {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls inner out : LS} {before entered after : GIR.Frame} {loop : Option LoopCtx}
    {scope : ScopeId} {scopeInstance : ScopeInst} {flow : Flow} {pt : Pt}
    (hdepth : LoopDepthFits env loop) (hrel : Rel cfg env cx before ls)
    (hentered : Rel cfg { env with scopes := (scope, scopeInstance) :: env.scopes } cx entered inner)
    (hvalues : entered.vals = before.vals) (hsize : inner.vals.size = ls.vals.size)
    (h : StatementLoopPost cfg { env with scopes := (scope, scopeInstance) :: env.scopes }
      cx inner entered out loop flow pt after)
    (habnormal : ∀ value, flow ≠ .normal value) :
    ReturnedAt cx flow pt after ∨
      (∃ context, loop = some context ∧
        ((flow = .brk ∧ ExitedAt context before ls.vals.size
          (env.scopes.drop (env.scopes.length - context.depth)) pt after) ∨
        (flow = .cont ∧ ContinuedAt context before ls.vals.size
          (env.scopes.drop (env.scopes.length - context.depth)) pt after))) := by
  have hact : entered.act = before.act := hentered.act.trans hrel.act.symm
  have hframeDepth : entered.depth = before.depth := hentered.depth.trans hrel.depth.symm
  have hprefix : Same ls.vals.size before entered := fun id _ => by rw [hvalues]
  rcases h with ⟨hflow, P⟩ | hret | ⟨context, hloop, htransfer⟩
  · exact (habnormal .unit hflow).elim
  · exact Or.inl hret
  · have hfit : context.depth ≤ env.scopes.length := by
      rw [hloop] at hdepth
      exact hdepth
    have hsuffix := loopScopeSuffix_entered env scope scopeInstance context.depth hfit
    change ((scope, scopeInstance) :: env.scopes).drop
      (((scope, scopeInstance) :: env.scopes).length - context.depth) = _ at hsuffix
    refine Or.inr ⟨context, hloop, ?_⟩
    rcases htransfer with ⟨hflow, hpoint, hframe⟩ | ⟨hflow, hcontinue⟩
    · rw [hsuffix, hsize] at hframe
      exact Or.inl ⟨hflow, hpoint, hframe.prefix hprefix hact hframeDepth⟩
    · refine Or.inr ⟨hflow, ?_⟩
      cases hkind : context.cont with
      | jump header =>
        rw [ContinuedAt, hkind] at hcontinue ⊢
        obtain ⟨hpoint, hframe⟩ := hcontinue
        rw [hsuffix, hsize] at hframe
        exact ⟨hpoint, hframe.prefix hprefix hact hframeDepth⟩
      | next header hint counter =>
        rw [ContinuedAt, hkind] at hcontinue ⊢
        obtain ⟨runtimeTy, current, hcell, hnext⟩ := hcontinue
        rw [hsuffix] at hnext
        refine ⟨runtimeTy, current, ?_, ?_⟩
        · rw [← hvalues]
          exact hcell
        · exact ⟨hnext.point, fun id hid => by rw [← hvalues]; exact hnext.values id hid,
            hnext.counterValue, hnext.activation.trans hact, hnext.scopesEqual,
            hnext.depth.trans hframeDepth⟩

end Goose.Lower
