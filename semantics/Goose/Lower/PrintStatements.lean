import Goose.Lower.PrintSources
import Goose.Lower.Claims
import Goose.Lower.TypedStatements

namespace Goose.Lower

open Goose.Core Goose.GIR

private theorem renderAt {cx : FnCtx} {pt : Pt} {fr : Frame} {value : Val}
    {action : String → M α} {post : α → Pt → Frame → Prop} {state : St}
    (next : ∀ part, Core.render value = pure part → SimEAt cx pt fr (action part) post state) :
    SimEAt cx pt fr (Core.render value >>= action) post state := by
  cases value with
  | int ty value => exact next (toString value) rfl
  | bool value => cases value <;> exact next _ rfl
  | _ => exact SimEAt.of_simG (SimG.of_fault_bind fun state => ⟨_, state, rfl⟩) state

private theorem printArgs_typed_sim {n : Nat} {cfg : Cfg} {results : List Ty} {env : Env}
    (expressions : ∀ expr, TypedExprClaim n cfg results expr) :
    ∀ (args : List PrintArg) (state : St), PrintSourceCursor (cfg := cfg) env n results args state →
    ∀ (ls ls' : LS) (parts : List PrintPart) (pt : Pt) (cx : FnCtx) (fr : Frame),
    lowerPrintArgs args (lowerEnv cfg.mod env.vars results) ls = (parts, ls') →
    ls.pp = some pt → ExtT ls' cx.fn.blocks → Rel cfg env cx fr ls →
    cx.cfg.mod = lower cfg.mod → cx.fn.results = results →
    SimEAt cx pt fr (mapList (execPrintArg (n + 1) cfg env) args)
      (fun strings pt' fr' => ∃ cells, Post cfg env cx ls fr ls' fr' pt' cells ∧
        (∀ id ∈ partsIds parts, ∃ value, (id, value) ∈ cells) ∧ PartsRender fr' parts strings) state := by
  intro args
  induction args with
  | nil =>
    intro state cursor ls ls' parts pt cx fr lowered point extension related module resultsEq
    simp only [lowerPrintArgs, pure_run] at lowered
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj lowered
    exact SimEAt.ret ⟨[], Post.init related point, by simp [partsIds], trivial⟩
  | cons arg args induction =>
    intro state cursor ls ls' parts pt cx fr lowered point extension related module resultsEq
    cases arg with
    | text text =>
      cases cursor with
      | text tail =>
        simp only [lowerPrintArgs, bind_eq] at lowered
        obtain ⟨suffix, middle, loweredTail, finished⟩ := lowered
        rw [pure_run] at finished
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj finished
        simp only [mapList, execPrintArg, pure_bind]
        refine SimEAt.bind (induction state tail ls middle suffix pt cx fr loweredTail point
          extension related module resultsEq) fun strings after pt1 fr1 done ⟨cells, P, ids, rendered⟩ => ?_
        exact SimEAt.ret ⟨cells, P, by simpa [partsIds] using ids, rfl, rendered⟩
    | expr expr =>
      cases cursor with
      | expr source printable metadata resume =>
        simp only [lowerPrintArgs, bind_eq] at lowered
        obtain ⟨value, middle, loweredExpr, suffix, final, loweredTail, finished⟩ := lowered
        rw [pure_run] at finished
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj finished
        have middleExtension := extension.of_adv (advB_lowerPrintArgs args _ _ _ _ loweredTail)
        simp only [mapList, execPrintArg, bind_assoc]
        refine SimEAt.bind (expressions expr env state source metadata ls middle value pt cx fr
          loweredExpr point middleExtension related module resultsEq) fun actual after pt1 fr1 done P1 => ?_
        apply renderAt
        intro part rendered
        have head : execPrintArg (n + 1) cfg env (.expr expr) state = .ok part after := by
          simp only [execPrintArg, bind_apply, done, rendered, pure_apply]
        refine SimEAt.bind (induction after (resume head) middle final suffix pt1 cx fr1 loweredTail
          P1.pp extension P1.rel module resultsEq) fun strings finished pt2 fr2 tailDone ⟨cells, P2, ids, tailRendered⟩ => ?_
        refine SimEAt.ret ⟨(value, .val actual) :: cells, ?_, ?_, ?_⟩
        · exact (P1.comp P2).sub (by intro cell member; simpa using member)
        · intro id member
          simp only [partsIds, List.mem_cons] at member
          rcases member with rfl | member
          · exact ⟨.val actual, by simp⟩
          · obtain ⟨cell, present⟩ := ids id member
            exact ⟨cell, by simp [present]⟩
        · refine ⟨⟨actual, ?_, rendered⟩, tailRendered⟩
          rw [P2.same value (P1.lt (value, .val actual) (by simp))]
          exact P1.has (value, .val actual) (by simp)

theorem typedStatementLoopSimulation_print_succ {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {args : List PrintArg} {origin : OriginId}
    (expressions : ∀ expr, TypedExprClaim n cfg results expr) :
    TypedStatementLoopSimulation (n + 2) cfg results loop (.print args origin) := by
  intro env state source metadata loops ls ls' result pt cx fr lowered point extension related
    module resultsEq depth targets counter
  have resultEq : result = () := Subsingleton.elim _ _
  subst result
  simp only [lowerStmt, bind_eq] at lowered
  obtain ⟨parts, middle, loweredArgs, emitted⟩ := lowered
  have middleExtension := extension.of_adv (adv_emitEffect emitted)
  apply SimEAt.prepareNormalLoopFlow
  simp only [execStmt]
  refine SimEAt.bind (printArgs_typed_sim expressions args state
    (source.printSourceCursor n metadata) ls middle parts pt cx fr loweredArgs point middleExtension
    related module resultsEq) fun strings after pt1 fr1 done ⟨cells, P, ids, rendered⟩ => ?_
  have step : execEff cx.fn fr1 (.print parts (some origin)) =
      emit (String.join strings ++ "\n") >>= fun _ => pure fr1 := by
    simp only [execEff, mapList_renderPart_of rendered, pure_bind]
  exact SimEAt.of_simG (leaf_eff P emitted extension (Flow.normal .unit) rfl step) after

theorem typedStatementLoopSimulation_print_one (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (args : List PrintArg) (origin : OriginId) :
    TypedStatementLoopSimulation 1 cfg results loop (.print args origin) := by
  intro env state source metadata loops ls ls' result pt cx fr lowered point extension related
    module resultsEq depth targets counter
  cases args with
  | nil =>
    have resultEq : result = () := Subsingleton.elim _ _
    subst result
    have old := stmtClaim_print 0 loop
      (printArgsClaim 0 (fun smaller impossible => by omega)) [] origin rfl
      (lowerEnv cfg.mod env.vars results) ls () ls' pt cfg env cx fr lowered point extension related
    exact (SimEAt.of_simG old state).prepareNormalLoopFlow
  | cons arg args =>
    simp only [execStmt, mapList, execPrintArg, bind_assoc]
    exact SimEAt.of_simG SimG.of_timeout_bind state

end Goose.Lower
