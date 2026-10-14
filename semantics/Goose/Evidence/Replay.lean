import Goose.Evidence.Bounds
import Goose.GIR.Step

namespace Goose.Proofs.Bounds

open Goose.Core Goose.GIR

def ReplayPoint (m : GIR.Module) (f : Func) (certificate : FactCertificate)
    (point : Pt) (facts : Facts) : Prop :=
  ∃ block, f.blocks[point.1]? = some block ∧
    (block.insts.take point.2).foldlM (transferInst m f)
      (certificate[point.1]?.getD []) = .ok facts

def PointFactsHold (cx : FnCtx) (certificate : FactCertificate)
    (point : Pt) (fr : Frame) (state : St) : Prop :=
  ∃ facts, ReplayPoint cx.cfg.mod cx.fn certificate point facts ∧ FactsHold fr state facts

private theorem replay_prefix {m : GIR.Module} {f : Func} {insts : List Inst}
    {initial final : Facts} (checked : insts.foldlM (transferInst m f) initial = .ok final)
    (offset : Nat) : ∃ facts,
    (insts.take offset).foldlM (transferInst m f) initial = .ok facts := by
  have splitChecked : ((insts.take offset).foldlM (transferInst m f) initial >>= fun facts =>
      (insts.drop offset).foldlM (transferInst m f) facts) = .ok final := by
    simpa only [← List.foldlM_append, List.take_append_drop] using checked
  obtain ⟨facts, replayedPrefix, _⟩ := Goose.GIR.bind_ok splitChecked
  exact ⟨facts, replayedPrefix⟩

theorem CertificateValid.replay {m : GIR.Module} {f : Func} {vt : Array (Option VTy)}
    {certificate : FactCertificate} (valid : CertificateValid m f vt certificate)
    {point : Pt} (blockExists : point.1 < f.blocks.size) :
    ∃ facts, ReplayPoint m f certificate point facts := by
  have accepted := valid.blocks point.1 blockExists
  cases blockAt : f.blocks[point.1]? with
  | none => simp [BlockEvidenceValid, blockAt] at accepted
  | some block =>
    simp only [BlockEvidenceValid, blockAt] at accepted
    obtain ⟨outgoing, checked, _⟩ := accepted
    obtain ⟨facts, replayedPrefix⟩ := replay_prefix checked point.2
    exact ⟨facts, block, blockAt, replayedPrefix⟩

theorem ReplayPoint.unique {m : GIR.Module} {f : Func} {certificate : FactCertificate}
    {point : Pt} {left right : Facts} (hl : ReplayPoint m f certificate point left)
    (hr : ReplayPoint m f certificate point right) : left = right := by
  obtain ⟨lb, lbAt, leftReplay⟩ := hl
  obtain ⟨rb, rbAt, rightReplay⟩ := hr
  rw [lbAt] at rbAt
  cases rbAt
  rw [leftReplay] at rightReplay
  cases rightReplay
  rfl

theorem ReplayPoint.next {m : GIR.Module} {f : Func} {certificate : FactCertificate}
    {point : Pt} {facts outgoing : Facts} {inst : Inst}
    (replayed : ReplayPoint m f certificate point facts)
    (instruction : instAt f point = some inst)
    (checked : transferInst m f facts inst = .ok outgoing) :
    ReplayPoint m f certificate (point.1, point.2 + 1) outgoing := by
  obtain ⟨block, blockAt, replayedPrefix⟩ := replayed
  have instructionAt : block.insts[point.2]? = some inst := by
    simpa only [instAt, blockAt, Option.bind_some] using instruction
  refine ⟨block, blockAt, ?_⟩
  rw [List.take_add_one, instructionAt]
  simp only [Option.toList_some, List.foldlM_append, replayedPrefix,
    List.foldlM_cons, List.foldlM_nil, pure, Except.pure, bind, Except.bind, checked]

theorem PointFactsHold.def {fuel : Nat} {cx : FnCtx} {certificate : FactCertificate}
    {point : Pt} {fr : Frame} {state after : St} {result : ValueId} {op : Op} {cell : RVal}
    {outgoing : Facts} (hold : PointFactsHold cx certificate point fr state)
    (instruction : instAt cx.fn point = some (.def result op))
    (freshLength : ∀ reference, op = .arrayLen reference → result ≠ reference)
    (success : execOp fuel cx fr op state = .ok cell after)
    (checked : ∀ facts, ReplayPoint cx.cfg.mod cx.fn certificate point facts →
      transferInst cx.cfg.mod cx.fn facts (.def result op) = .ok outgoing) :
    PointFactsHold cx certificate (point.1, point.2 + 1) (withCell fr result cell) after := by
  obtain ⟨facts, replayed, valid⟩ := hold
  have transfer := checked facts replayed
  exact ⟨outgoing, ReplayPoint.next replayed instruction transfer,
    transfer_def_sound valid freshLength success transfer⟩

theorem PointFactsHold.eff {cx : FnCtx} {certificate : FactCertificate} {point : Pt}
    {fr next : Frame} {state after : St} {effect : Effect} {outgoing : Facts}
    (hold : PointFactsHold cx certificate point fr state)
    (instruction : instAt cx.fn point = some (.eff effect))
    (success : execEff cx.fn fr effect state = .ok next after)
    (checked : ∀ facts, ReplayPoint cx.cfg.mod cx.fn certificate point facts →
      transferInst cx.cfg.mod cx.fn facts (.eff effect) = .ok outgoing) :
    PointFactsHold cx certificate (point.1, point.2 + 1) next after := by
  obtain ⟨facts, replayed, valid⟩ := hold
  have transfer := checked facts replayed
  exact ⟨outgoing, ReplayPoint.next replayed instruction transfer,
    transfer_effect_sound valid success transfer⟩

theorem CertificateValid.instruction {m : GIR.Module} {f : Func} {vt : Array (Option VTy)}
    {certificate : FactCertificate} (valid : CertificateValid m f vt certificate)
    {point : Pt} {facts : Facts} {inst : Inst} (replayed : ReplayPoint m f certificate point facts)
    (instruction : instAt f point = some inst) :
    ∃ outgoing, transferInst m f facts inst = .ok outgoing := by
  obtain ⟨block, blockAt, replayedPrefix⟩ := replayed
  have blockExists : point.1 < f.blocks.size := by
    exact (Array.getElem?_eq_some_iff.mp blockAt).1
  obtain ⟨outgoing, nextReplay⟩ := valid.replay (point := (point.1, point.2 + 1)) blockExists
  obtain ⟨nextBlock, nextAt, nextPrefix⟩ := nextReplay
  rw [blockAt] at nextAt
  cases nextAt
  have instructionAt : block.insts[point.2]? = some inst := by
    simpa only [instAt, blockAt, Option.bind_some] using instruction
  rw [List.take_add_one, instructionAt] at nextPrefix
  simp only [Option.toList_some, List.foldlM_append, replayedPrefix,
    List.foldlM_cons, List.foldlM_nil, pure, Except.pure, bind, Except.bind] at nextPrefix
  cases transferred : transferInst m f facts inst with
  | error reason => simp [transferred] at nextPrefix
  | ok derived => exact ⟨derived, rfl⟩

theorem PointFactsHold.entry {cx : FnCtx} {vt : Array (Option VTy)}
    {certificate : FactCertificate} {block : GIR.Block}
    (valid : CertificateValid cx.cfg.mod cx.fn vt certificate)
    (entry : cx.fn.blocks[0]? = some block) (fr : Frame) (state : St) :
    PointFactsHold cx certificate (0, 0) fr state := by
  refine ⟨[], ⟨block, entry, ?_⟩, FactsHold.empty fr state⟩
  simp [valid.entryEmpty, pure, Except.pure]

theorem PointFactsHold.index {cx : FnCtx} {vt : Array (Option VTy)}
    {certificate : FactCertificate} {point : Pt} {fr : Frame} {state : St}
    {result view index : ValueId} (valid : CertificateValid cx.cfg.mod cx.fn vt certificate)
    (hold : PointFactsHold cx certificate point fr state)
    (instruction : instAt cx.fn point = some (.def result (.indexProven view index))) :
    execPure cx fr (.indexProven view index) = execPure cx fr (.indexChecked view index none) := by
  obtain ⟨facts, replayed, holds⟩ := hold
  obtain ⟨outgoing, checked⟩ := valid.instruction replayed instruction
  have justified : provesIndex facts view index = true := by
    by_cases justified : provesIndex facts view index = true
    · exact justified
    · have unjustified : provesIndex facts view index = false := Bool.eq_false_iff.mpr justified
      simp [transferInst, unjustified, bind, Except.bind] at checked
  obtain ⟨bound, boundFacts⟩ := provesIndex_sound holds justified
  exact indexProven_eq_checked_of_facts boundFacts

private theorem terminated_shape {block : GIR.Block}
    (oneTerm : block.terms.length = 1) (lastTerm : block.lastTerm?.isSome = true) :
    ∃ body term, block.insts = body ++ [.term term] ∧ body.filterMap Inst.term? = [] := by
  unfold Block.lastTerm? at lastTerm
  cases lastAt : block.insts.getLast? with
  | none => simp [lastAt] at lastTerm
  | some inst =>
    cases inst with
    | «def» | eff => simp [lastAt] at lastTerm
    | term term =>
      obtain ⟨body, layout⟩ := List.getLast?_eq_some_iff.mp lastAt
      refine ⟨body, term, layout, List.length_eq_zero_iff.mp ?_⟩
      simp only [Block.terms, layout, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, Inst.term?, List.length_append, List.length_cons,
        List.length_nil] at oneTerm
      omega

theorem terminated_term_last {block : GIR.Block} {offset : Nat} {term : Term}
    (oneTerm : block.terms.length = 1) (lastTerm : block.lastTerm?.isSome = true)
    (instruction : block.insts[offset]? = some (.term term)) :
    block.lastTerm? = some term ∧ block.insts.take (offset + 1) = block.insts := by
  obtain ⟨body, final, layout, noTerms⟩ := terminated_shape oneTerm lastTerm
  by_cases before : offset < body.length
  · have inBody : body[offset]? = some (.term term) := by
      simpa only [layout, List.getElem?_append_left before] using instruction
    have member : .term term ∈ body := List.mem_of_getElem? inBody
    have termMember : term ∈ body.filterMap Inst.term? :=
      List.mem_filterMap.mpr ⟨.term term, member, rfl⟩
    simp [noTerms] at termMember
  · have after : body.length ≤ offset := by omega
    have inLast : ([.term final] : List Inst)[offset - body.length]? = some (.term term) := by
      simpa only [layout, List.getElem?_append_right after] using instruction
    have position : offset - body.length = 0 := by
      have bound := (List.getElem?_eq_some_iff.mp inLast).1
      simp only [List.length_cons, List.length_nil] at bound
      omega
    have same : final = term := by simpa [position] using inLast
    subst final
    have offsetBody : offset = body.length := by omega
    constructor
    · simp [Block.lastTerm?, layout]
    · have fullLength : offset + 1 = block.insts.length := by simp [layout, offsetBody]
      rw [fullLength, List.take_length]

theorem ReplayPoint.atTerm {m : GIR.Module} {f : Func} {certificate : FactCertificate}
    {point : Pt} {facts : Facts} {term : Term} (replayed : ReplayPoint m f certificate point facts)
    (terminated : TerminatedBlocks f) (instruction : instAt f point = some (.term term)) :
    ∃ block, f.blocks[point.1]? = some block ∧ block.lastTerm? = some term ∧
      transferBlock m f (certificate[point.1]?.getD []) block = .ok facts := by
  obtain ⟨block, blockAt, replayedPrefix⟩ := replayed
  have instructionAt : block.insts[point.2]? = some (.term term) := by
    simpa only [instAt, blockAt, Option.bind_some] using instruction
  obtain ⟨oneTerm, lastTerm⟩ := terminated block (Array.mem_of_getElem? blockAt)
  obtain ⟨lastAt, fullTake⟩ := terminated_term_last oneTerm lastTerm instructionAt
  refine ⟨block, blockAt, lastAt, ?_⟩
  unfold transferBlock
  rw [← fullTake, List.take_add_one, instructionAt]
  simp [List.foldlM_append, replayedPrefix, transferInst, killsLengths, pure, Except.pure, bind, Except.bind]

theorem CertificateValid.termClaims {m : GIR.Module} {f : Func} {vt : Array (Option VTy)}
    {certificate : FactCertificate} {point : Pt} {facts : Facts} {term : Term}
    (valid : CertificateValid m f vt certificate) (terminated : TerminatedBlocks f)
    (replayed : ReplayPoint m f certificate point facts)
    (instruction : instAt f point = some (.term term)) :
    match term with
    | .br target args => ClaimsDerived (certificate[target]?.getD []) (edgeFacts f facts none target args)
    | .condbr condition yes yesArgs no noArgs =>
      ClaimsDerived (certificate[yes]?.getD []) (edgeFacts f facts (some condition) yes yesArgs) ∧
        ClaimsDerived (certificate[no]?.getD []) (edgeFacts f facts none no noArgs)
    | _ => True := by
  obtain ⟨block, blockAt, lastAt, checked⟩ := replayed.atTerm terminated instruction
  have accepted := valid.blocks point.1 (Array.getElem?_eq_some_iff.mp blockAt).1
  simp only [BlockEvidenceValid, blockAt] at accepted
  obtain ⟨outgoing, outgoingChecked, claims⟩ := accepted
  rw [checked] at outgoingChecked
  cases outgoingChecked
  cases term <;> simp only [lastAt] at claims ⊢ <;> exact claims

theorem FactsHold.addTrueEdge {f : Func} {condition : ValueId} {fr : Frame} {state : St}
    {facts : Facts} (hold : FactsHold fr state facts)
    (comparison : ∀ left right, f.defOp? condition = some (.cmp .lt .i64 left right) →
      FactHolds fr state (.lt left right)) :
    FactsHold fr state (addTrueEdgeFacts f facts condition) := by
  unfold addTrueEdgeFacts
  cases definition : f.defOp? condition with
  | none => exact hold
  | some op =>
    cases op <;> try exact hold
    case cmp operator type left right =>
      cases operator <;> cases type <;> first
        | exact hold
        | exact FactsHold.add hold (comparison left right definition)

theorem PointFactsHold.edge {cx : FnCtx} {certificate : FactCertificate}
    {fr next : Frame} {state after : St} {target : BlockId}
    {args : List RVal} {insts : List Inst} {facts : Facts}
    (hold : FactsHold fr state facts)
    (claims : ClaimsDerived (certificate[target]?.getD []) (translateEdge cx.fn facts target []))
    (success : Goose.GIR.enterBlock cx.fn fr target args state = .ok (insts, next) after) :
    PointFactsHold cx certificate (target, 0) next after := by
  have runtimeFacts := FactsHold.claimedEdge hold claims success
  unfold Goose.GIR.enterBlock at success
  cases blockAt : cx.fn.blocks[target]? with
  | none => simp [blockAt, fault, M.stop] at success
  | some block =>
    refine ⟨certificate[target]?.getD [], ⟨block, blockAt, ?_⟩, runtimeFacts⟩
    simp [pure, Except.pure]

end Goose.Proofs.Bounds
