import Goose.Lower.DemandWhileSource

namespace Goose.Lower
open Goose.Core Goose.GIR Goose.Core.Sound

theorem generated_while_header_entry {cfg : Cfg} {env : Env} {cx : FnCtx} {results : List Ty}
    {loop : Option LoopCtx} {condition : Expr} {body : Core.Block} {origin : OriginId} {before after : LS}
    {frame : GIR.Frame} {point : Pt} {state : St}
    (lowered : lowerStmt loop (.while condition body origin) (lowerEnv cfg.mod env.vars results) before = ((), after))
    (atPoint : before.pp = some point) (extended : ExtT after cx.fn.blocks)
    (related : Rel cfg env cx frame before) (generated : GeneratedBuilderState before) :
    ∃ header headerState,
      lowerWhile header (lowerExpr condition)
        (fun depth exitBlock => lowerBlock (some ⟨depth, exitBlock, .jump header⟩) [] false body)
        (lowerEnv cfg.mod env.vars results) headerState = ((), after) ∧
      headerState = demandWhileHeaderBefore (lowerEnv cfg.mod env.vars results) before ∧
      Post cfg env cx before frame headerState frame (header, 0) [] ∧
      GeneratedBuilderState headerState ∧
      ∀ fuel, DemandInstructionStep cx fuel ⟨point, frame, state⟩ ⟨(header, 0), frame, state⟩ := by
  let le := lowerEnv cfg.mod env.vars results
  simp only [lowerStmt, bind_eq] at lowered
  obtain ⟨⟨header, parameters⟩, made, newRun, _, jumped, jumpRun, _, headerState, setRun, loopRun⟩ := lowered
  have loopAdvance := advB_lowerWhile header (advB_lowerExpr condition)
    (fun _ _ => advB_lowerBlock _ [] false body) _ _ _ _ loopRun
  have headerExtended : ExtT headerState cx.fn.blocks := extended.of_adv loopAdvance
  have headerEq : headerState = { jumped with cur := some header } := by
    rw [setCur_run] at setRun
    exact (Prod.mk.inj setRun).2.symm
  have jumpExtended : ExtT jumped cx.fn.blocks := by rw [headerEq] at headerExtended; exact headerExtended
  have newRun' := newRun
  rw [newBlock0_run] at newRun'
  obtain ⟨ids, madeEq⟩ := Prod.mk.inj newRun'
  obtain ⟨headerEq', _⟩ := Prod.mk.inj ids
  have madeVals : made.vals = before.vals := by rw [← madeEq]
  have madeStack : made.stack = before.stack := by rw [← madeEq]
  have madeCurrent : made.cur = before.cur := by rw [← madeEq]
  obtain ⟨block, current, blockAt, pointEq⟩ := LS.pp_some atPoint
  have pointBound : point.1 < before.blocks.size := (Array.getElem?_eq_some_iff.mp blockAt).1
  have madeAt : made.blocks[point.1]? = some block := by
    rw [← madeEq]
    exact (getElem?_push_lt pointBound).trans blockAt
  have madePoint : made.pp = some point := by
    have pointMatch := LS.pp_eq (madeCurrent.trans current) madeAt
    rw [← pointEq] at pointMatch
    exact pointMatch
  obtain ⟨jumpVals, jumpStack, _, instruction⟩ := emitTerm_facts jumpRun madePoint jumpExtended
  have headerMade : made.blocks[header]? = some ⟨[], #[]⟩ := by
    rw [← headerEq', ← madeEq]
    simp
  have different : made.cur ≠ some header := by
    rw [madeCurrent, current]
    intro equal
    have ids := Option.some.inj equal
    rw [← headerEq'] at ids
    exact Nat.ne_of_lt pointBound ids
  have headerJumped : jumped.blocks[header]? = some ⟨[], #[]⟩ := (adv_emitTerm jumpRun).keep header _ different headerMade
  have headerPoint : headerState.pp = some (header, 0) := by rw [headerEq]; exact LS.pp_cur headerJumped
  obtain ⟨target, targetAt, targetParams⟩ := jumpExtended.params headerJumped
  have headerRelated : Rel cfg env cx frame headerState := related.stack_eq (by
    rw [headerEq]
    change jumped.stack = before.stack
    rw [jumpStack, madeStack])
  have headerValues : headerState.vals.size = before.vals.size := by
    rw [headerEq]
    change jumped.vals.size = before.vals.size
    rw [jumpVals, madeVals]
  have madeGenerated := generated.newBlock [] newRun
  have jumpGenerated := madeGenerated.emitTerm (.br header [])
    (by
      intro target member
      simp only [Term.successors, List.mem_singleton] at member
      subst target
      exact (Array.getElem?_eq_some_iff.mp headerMade).1) jumpRun
  have headerGenerated := jumpGenerated.setCur (some header)
    (by intro current same; cases same; exact (Array.getElem?_eq_some_iff.mp headerJumped).1) setRun
  have inst : instAt cx.fn point = some (.term (.br header [])) := instruction
  let branch : DemandBranch := .jump header []
  have branchAt : instAt cx.fn point = some (.term branch.term) := by simpa [branch, DemandBranch.term] using inst
  have execution : branch.enter cx.fn frame state = .ok (header, instsAt cx.fn (header, 0), frame) state := by
    simp [branch, DemandBranch.enter, mapList, enterBlock, targetAt, targetParams, bindParams, instsAt, bind_apply, pure_apply]
  have headerCanonical : headerState = demandWhileHeaderBefore le before := by
    unfold demandWhileHeaderBefore
    rw [newRun]
    simp only
    rw [jumpRun]
    exact headerEq
  have post : Post cfg env cx before frame headerState frame (header, 0) [] :=
    Post.nil headerPoint (Nat.le_of_eq headerValues.symm) (Same.refl _ _) headerRelated
  exact ⟨header, headerState, loopRun, headerCanonical, post, headerGenerated, fun fuel => .control branchAt execution⟩

#print axioms generated_while_header_entry
end Goose.Lower
