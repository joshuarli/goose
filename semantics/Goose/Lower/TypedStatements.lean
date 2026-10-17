import Goose.Lower.TypedExpressions
import Goose.Lower.DestinationSim
import Goose.Lower.TypedBlocks

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem stmt_let_typed_sim {n : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {results : List Ty} {loop : Option LoopCtx} {slot : SlotId} {expr : Expr} {org : OriginId}
    {ls ls' : LS} {pt : Pt} {fr : GIR.Frame} {state : St} {lv : LocalVar}
    (source : ExprSource cfg env expr state)
    (hmetadata : SourceResults source.typingEnv source.rootsEnv results)
    (hvar : env.vars[slot]? = some lv) (hpass : source.ty.passableTo lv.ty = true)
    (hexpr : TypedExprClaim n cfg results expr)
    (hlow : lowerStmt loop (.letS slot expr org) (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hgir : cx.cfg.mod = lower cfg.mod) (hresults : cx.fn.results = results)
    (hgenerated : GeneratedBuilderState ls) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.letS slot expr org))
      (fun flow pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) state := by
  have hslot : (lowerEnv cfg.mod env.vars results).slots[slot]? =
      some (⟨lv.ty, lv.kind, lv.scope, slot⟩ : Slot) := by
    simp [lowerEnv, Array.getElem?_mapIdx, hvar]
  refine stmt_let_coerced_sim hslot hlow hext ?_ ?_
  · intro id middle hvalue hextMiddle
    exact hexpr env state source hmetadata ls middle id pt cx fr hvalue hpp hextMiddle
      hrel hgir hresults hgenerated
  · intro value after hdone
    exact (source.result n value hdone).coercionValue hpass

theorem stmt_rebind_typed_sim {n : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {results : List Ty} {loop : Option LoopCtx} {slot : SlotId} {expr : Expr} {org : OriginId}
    {ls ls' : LS} {pt : Pt} {fr : GIR.Frame} {state : St} {lv : LocalVar}
    (source : ExprSource cfg env expr state)
    (hmetadata : SourceResults source.typingEnv source.rootsEnv results)
    (hvar : env.vars[slot]? = some lv) (hpass : source.ty.passableTo lv.ty = true)
    (hexpr : TypedExprClaim n cfg results expr)
    (hlow : lowerStmt loop (.rebind slot expr org) (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hgir : cx.cfg.mod = lower cfg.mod) (hresults : cx.fn.results = results)
    (hgenerated : GeneratedBuilderState ls) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.rebind slot expr org))
      (fun flow pt' fr' => flow = .normal .unit ∧ Post cfg env cx ls fr ls' fr' pt' []) state := by
  have hslot : (lowerEnv cfg.mod env.vars results).slots[slot]? =
      some (⟨lv.ty, lv.kind, lv.scope, slot⟩ : Slot) := by
    simp [lowerEnv, Array.getElem?_mapIdx, hvar]
  refine stmt_rebind_coerced_sim hslot hlow hext ?_ ?_
  · intro id middle hvalue hextMiddle
    exact hexpr env state source hmetadata ls middle id pt cx fr hvalue hpp hextMiddle
      hrel hgir hresults hgenerated
  · intro value after hdone
    exact (source.result n value hdone).coercionValue hpass

theorem stmt_ret_typed_sim {n : Nat} {cfg : Cfg} {env : Env} {cx : FnCtx}
    {results : List Ty} {loop : Option LoopCtx} {expr : Expr} {org : OriginId}
    {ls ls' : LS} {pt : Pt} {fr : GIR.Frame} {state : St} {impl : Impl} {target : Ty} {rest : List Ty}
    (source : ExprSource cfg env expr state)
    (hmetadata : SourceResults source.typingEnv source.rootsEnv results)
    (himpl : source.typingEnv.impl = some impl)
    (hdecl : impl.results.toList = target :: rest) (hpass : source.ty.passableTo target = true)
    (hexpr : TypedExprClaim n cfg results expr)
    (hlow : lowerStmt loop (.ret (some expr) org) (lowerEnv cfg.mod env.vars results) ls = ((), ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) (hrel : Rel cfg env cx fr ls)
    (hgir : cx.cfg.mod = lower cfg.mod) (hresults : cx.fn.results = results)
    (hgenerated : GeneratedBuilderState ls) :
    SimEAt cx pt fr (execStmt (n + 1) cfg env (.ret (some expr) org) >>= prepareReturn env)
      (fun flow pt' fr' => ∃ value, flow = .ret value ∧ ReturnSite cx pt' fr' value org) state := by
  have hresult : (lowerEnv cfg.mod env.vars results).results.head? = some target := by
    change results.head? = some target
    rw [(hmetadata impl himpl).2, hdecl]
    rfl
  refine stmt_ret_coerced_sim hresult hlow hext ?_ ?_
  · intro id middle hvalue hextMiddle
    exact hexpr env state source hmetadata ls middle id pt cx fr hvalue hpp hextMiddle
      hrel hgir hresults hgenerated
  · intro value after hdone
    exact (source.result n value hdone).coercionValue hpass

theorem typedStatementLoopSimulation_let {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {slot : VarId} {expr : Expr} {org : OriginId}
    (hexpr : TypedExprClaim n cfg results expr) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.letS slot expr org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter hgenerated hframes
  obtain ⟨child, declaration, hvar, htyping, hroots, hpass⟩ := source.letChild
  have hchild : SourceResults child.typingEnv child.rootsEnv results := by
    apply hmetadata.transport
    · rw [htyping]
    · rw [hroots]
  have hresult : result = () := Subsingleton.elim _ _
  subst result
  exact (stmt_let_typed_sim child hchild hvar hpass hexpr hlow hpp hext hrel hgir
    hresults hgenerated).prepareNormalLoopFlow

theorem typedStatementLoopSimulation_rebind {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {slot : VarId} {expr : Expr} {org : OriginId}
    (hexpr : TypedExprClaim n cfg results expr) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.rebind slot expr org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter hgenerated hframes
  obtain ⟨child, declaration, hvar, htyping, hroots, hpass⟩ := source.rebindChild
  have hchild : SourceResults child.typingEnv child.rootsEnv results := by
    apply hmetadata.transport
    · rw [htyping]
    · rw [hroots]
  have hresult : result = () := Subsingleton.elim _ _
  subst result
  exact (stmt_rebind_typed_sim child hchild hvar hpass hexpr hlow hpp hext hrel hgir
    hresults hgenerated).prepareNormalLoopFlow

theorem typedStatementLoopSimulation_return_some {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {expr : Expr} {org : OriginId}
    (hexpr : TypedExprClaim n cfg results expr) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.ret (some expr) org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter hgenerated hframes
  obtain ⟨child, impl, target, himpl, hdecl, htyping, hroots, hpass⟩ := source.retChild
  have hchild : SourceResults child.typingEnv child.rootsEnv results := by
    apply hmetadata.transport
    · rw [htyping]
    · rw [hroots]
  have hchildImpl : child.typingEnv.impl = some impl := by rw [htyping]; exact himpl
  have hresult : result = () := Subsingleton.elim _ _
  subst result
  rw [prepareLoopFlow_execStmt_return_some]
  exact (stmt_ret_typed_sim (rest := []) child hchild hchildImpl hdecl hpass hexpr hlow
    hpp hext hrel hgir hresults hgenerated).mono fun flow _ pt' fr' _ ⟨value, hflow, hsite⟩ =>
      Or.inr (Or.inl ⟨value, org, hflow, hsite⟩)

theorem typedStatementLoopSimulation_expr {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {expr : Expr} {org : OriginId}
    (hexpr : TypedExprClaim n cfg results expr) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.expr expr org) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter hgenerated hframes
  obtain ⟨child, htyping, hroots⟩ := source.exprChild
  have hchild : SourceResults child.typingEnv child.rootsEnv results := by
    apply hmetadata.transport
    · rw [htyping]
    · rw [hroots]
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨value, middle, hvalue, hend⟩ := hlow
  rw [pure_run] at hend
  obtain ⟨_, rfl⟩ := Prod.mk.inj hend
  apply SimEAt.prepareNormalLoopFlow
  simp only [execStmt]
  refine SimEAt.bind (hexpr env state child hchild ls middle value pt cx fr hvalue hpp hext
    hrel hgir hresults hgenerated) fun value _ pt' fr' _ P => ?_
  exact SimEAt.ret ⟨rfl, P.sub (by simp)⟩

end Goose.Lower
