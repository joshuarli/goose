import Goose.Lower.TypedBlocks

namespace Goose.Lower

open Goose.Core Goose.GIR

theorem typedStatementsLoopSimulation_cons (n : Nat) (cfg : Cfg) (results : List Ty)
    (loop : Option LoopCtx) (stmt : Stmt) (rest : List Stmt)
    (hstmt : TypedStatementLoopSimulation n cfg results loop stmt)
    (hrest : TypedStatementsLoopSimulation n cfg results loop rest) :
    TypedStatementsLoopSimulation (n + 1) cfg results loop (stmt :: rest) := by
  intro env state source hmetadata hloops ls ls' result pt cx fr hlow hpp hext hrel
    hgir hresults hdepth htargets hcounter hgenerated hframes
  obtain ⟨block, hcur, _, _⟩ := LS.pp_some hpp
  simp only [lowerStmts, bind_eq] at hlow
  obtain ⟨live, initial, hlive, hlow⟩ := hlow
  rw [isLive_run hcur] at hlive
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlive
  simp only [ite_true, bind_eq] at hlow
  obtain ⟨firstResult, middle, hfirst, hremaining⟩ := hlow
  have hextMiddle := hext.of_adv (advB_lowerStmts loop rest _ _ _ _ hremaining)
  obtain ⟨head, htyping, hroots, next⟩ := source.split
  have hhead : SourceResults head.typingEnv head.rootsEnv results := by
    apply hmetadata.transport
    · rw [htyping]
    · rw [hroots]
  have hheadLoops : LoopSourceMatches head.typingEnv loop := by
    apply hloops.transport
    rw [htyping]
  rw [prepareLoopFlow_execStmts]
  refine SimEAt.bind (hstmt env state head hhead hheadLoops ls middle firstResult pt cx fr hfirst hpp
    hextMiddle hrel hgir hresults hdepth htargets hcounter hgenerated hframes)
    fun flow after ptMiddle frMiddle hactual hpost => ?_
  rcases hpost with ⟨rfl, P⟩ | hreturned | ⟨context, hloop, htransfer⟩
  · have hraw := preparedLoopFlow_normal_success hactual
    obtain ⟨tail, htailTyping, htailRoots, htailFinal⟩ := next n .unit after hraw
    have htail : SourceResults tail.typingEnv tail.rootsEnv results := by
      apply hhead.transport
      · rw [htailTyping]
        exact (head.result n (.normal .unit) hraw).same.impl
      · rw [htailRoots, hroots]
    have htailLoops : LoopSourceMatches tail.typingEnv loop := by
      apply hheadLoops.transport
      rw [htailTyping]
      exact (head.result n (.normal .unit) hraw).same.loops
    exact (hrest env after tail htail htailLoops middle ls' result ptMiddle cx frMiddle hremaining P.pp
      hext P.rel hgir hresults hdepth htargets (hcounter.afterPost P) (hgenerated.lowerStmt loop stmt hframes.toTargets hfirst)
      (hframes.mono (advB_lowerStmt loop stmt _ _ _ _ hfirst).ext)).mono
        fun flow' _ pt' fr' _ Q => StatementLoopPost.prefix hrel P hcounter Q
  · obtain ⟨returned, org, rfl, hsite⟩ := hreturned
    exact SimEAt.ret (Or.inr (Or.inl ⟨returned, org, rfl, hsite⟩))
  · rcases htransfer with ⟨rfl, hexit⟩ | ⟨rfl, hcontinue⟩
    · exact SimEAt.ret (Or.inr (Or.inr ⟨context, hloop, Or.inl ⟨rfl, hexit⟩⟩))
    · exact SimEAt.ret (Or.inr (Or.inr ⟨context, hloop, Or.inr ⟨rfl, hcontinue⟩⟩))

end Goose.Lower
