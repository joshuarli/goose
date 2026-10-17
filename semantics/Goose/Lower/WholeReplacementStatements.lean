import Goose.Lower.WholeReplacementSources
import Goose.Lower.TypedStatements
import Goose.Lower.Claims

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem typedStatementLoopSimulation_assignWhole {n : Nat} {cfg : Cfg} {results : List Ty}
    {loop : Option LoopCtx} {owner : Place} {replacement : Expr} {org : OriginId}
    (hplace : TypedPlaceClaim n cfg results owner) (hexpr : TypedExprClaim n cfg results replacement) :
    TypedStatementLoopSimulation (n + 1) cfg results loop (.assignWhole owner replacement org) := by
  intro env state source metadata loops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults depth targets counter
  obtain ⟨destination, typing, roots, _, _, ready⟩ := source.assignWholeChildren
  have destinationMetadata : SourceResults destination.typingEnv destination.rootsEnv results := by
    rw [typing, roots]
    exact metadata
  have resultEq : result = () := Subsingleton.elim _ _
  subst result
  let le := lowerEnv cfg.mod env.vars results
  simp only [lowerStmt, bind_eq] at hlow
  obtain ⟨rp, ls1, h1, u, ls2, h2, run, ls3, h3, h4⟩ := hlow
  cases u
  have hext3 : ExtT ls3 cx.fn.blocks := hext.of_adv (adv_emitEffect h4)
  have hext2 : ExtT ls2 cx.fn.blocks := hext3.of_adv (advB_lowerExpr replacement _ _ _ _ h3)
  have hext1 : ExtT ls1 cx.fn.blocks := hext2.of_adv (adv_emitEffect h2)
  apply SimEAt.prepareNormalLoopFlow
  simp only [execStmt]
  refine SimEAt.bind (hplace env state destination destinationMetadata ls ls1 rp pt cx fr h1 hpp hext1 hrel
    hgir hresults) fun l afterPlace pt1 fr1 donePlace P1 => ?_
  obtain ⟨Pclear, hi⟩ := Post.eff_leaf P1 h2 hext2
  have hrp1 : fr1.vals[rp]? = some (.val (.ref l)) := P1.has (rp, _) (by simp)
  have hvals : ls2.vals.size = ls1.vals.size := (emitEffect_facts h2 P1.pp hext2).1
  have PclearKeep : Post cfg env cx ls fr ls2 fr1 (pt1.1, pt1.2 + 1) [(rp, .val (.ref l))] := by
    refine ⟨Pclear.pp, ?_, ?_, Pclear.mono, Pclear.same, Pclear.rel⟩
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      exact hrp1
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      rw [hvals]
      exact P1.lt (rp, .val (.ref l)) (by simp)
  have hclear : execEff cx.fn fr1 (.clear rp (some org)) = truncateLoc l 0 >>= fun _ => pure fr1 := by
    simp only [execEff, getVal_of hrp1, Goose.Core.expectRef, bind_assoc, pure_bind]
  refine SimEAt.bind (SimEAt.of_simG (SimG.eff_step (fun _ => fr1) hi hclear) afterPlace)
    fun _ afterClear pt2 fr2 doneClear ⟨hpt, hfr⟩ => ?_
  subst pt2
  subst fr2
  cases cleared : afterPlace.store.truncate l 0 with
  | error error => simp [truncateLoc, cleared] at doneClear
  | ok clear =>
    have stateEq : afterClear = { afterPlace with store := clear } := by
      simp only [truncateLoc, cleared] at doneClear
      exact (Res.ok.inj doneClear).2.symm
    subst afterClear
    obtain ⟨child, typing, roots, _⟩ := ready n l afterPlace clear donePlace cleared
    have childMetadata : SourceResults child.typingEnv child.rootsEnv results := by
      rw [typing, roots]
      exact metadata
    refine SimEAt.bind (hexpr env { afterPlace with store := clear } child childMetadata ls2 ls3 run
      (pt1.1, pt1.2 + 1) cx fr1 h3 Pclear.pp hext3 Pclear.rel hgir hresults)
      fun replacementVal afterReplacement pt3 fr3 doneReplacement Preplacement => ?_
    have P13 := PclearKeep.comp Preplacement
    have hrp : fr3.vals[rp]? = some (.val (.ref l)) := P13.has (rp, _) (by simp)
    have hr : fr3.vals[run]? = some (.val replacementVal) := P13.has (run, _) (by simp)
    have hx : execEff cx.fn fr3 (.replace rp run (some org)) =
        (match replacementVal with
         | .resizable .. => writeLoc l replacementVal
         | _ => fault .shape) >>= fun _ => pure fr3 := by
      simp only [execEff, getVal_of hrp, getVal_of hr, Goose.Core.expectRef, bind_assoc, pure_bind]
      funext s
      cases replacementVal <;> rfl
    apply SimEAt.of_simG (leaf_eff P13 h4 hext (Flow.normal .unit) ?_ hx) afterReplacement
    funext s
    cases replacementVal <;> rfl

end Goose.Lower
