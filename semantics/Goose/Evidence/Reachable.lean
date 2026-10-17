import Goose.Evidence.Replay
import Goose.Evidence.Provenance

namespace Goose.Proofs.Bounds

open Goose.Core Goose.GIR Goose.Evidence

private theorem runtime_bind_success {computation : M α} {next : α → M β}
    {state after : St} {result : β}
    (success : (computation >>= next) state = .ok result after) :
    ∃ value middle, computation state = .ok value middle ∧ next value middle = .ok result after := by
  rw [bind_apply] at success
  cases evaluated : computation state with
  | stop reason stopped => simp [evaluated] at success
  | ok value middle => exact ⟨value, middle, rfl, by simpa [evaluated] using success⟩

theorem getCells_state {fr : Frame} {args : List ValueId} {state after : St} {values : List RVal}
    (success : mapList (getCell fr) args state = .ok values after) : after = state := by
  induction args generalizing state after values with
  | nil => exact (Res.ok.inj success).2.symm
  | cons arg args ih =>
    simp only [mapList] at success
    obtain ⟨cell, first, read, success⟩ := runtime_bind_success success
    obtain ⟨cells, second, rest, success⟩ := runtime_bind_success success
    have sameFirst := (getCell_success read).2
    have sameSecond := ih rest
    have sameFinal := (Res.ok.inj success).2.symm
    exact sameFinal.trans (sameSecond.trans sameFirst)

theorem branch_test_cell {fr : Frame} {condition : ValueId} {state after : St} {value : Bool}
    (success : (getVal fr condition >>= expectBool) state = .ok value after) :
    fr.vals[condition]? = some (.val (.bool value)) ∧ after = state := by
  obtain ⟨cell, middle, read, success⟩ := runtime_bind_success success
  obtain ⟨atCell, same⟩ := getVal_success read
  subst middle
  cases cell with
  | bool bit =>
    simp only [expectBool, pure_apply, Res.ok.injEq] at success
    obtain ⟨rfl, rfl⟩ := success
    exact ⟨atCell, rfl⟩
  | _ => simp [expectBool, fault, M.stop] at success

theorem validated_evidence {m : GIR.Module} {fn : Func} (accepted : Goose.GIR.validate m = .ok ())
    (member : fn ∈ m.allFuncs) : FunctionEvidenceValid m fn (fn.valueTypes m) := by
  have evidence : (checkAll m.infos fun info =>
      asCheck .v080 info.label (checkEvidence m info.f info.vt)) = .ok () := by
    unfold Goose.GIR.validate at accepted
    iterate 10 (obtain ⟨_, _, accepted⟩ := Goose.GIR.bind_ok accepted)
    obtain ⟨ignored, checked, _⟩ := Goose.GIR.bind_ok accepted
    cases ignored
    exact checked
  obtain ⟨info, infoMember, functionEq, typesEq⟩ := Goose.GIR.mem_infos member
  have checked := Goose.GIR.asCheck_ok (Goose.GIR.checkAll_mem evidence infoMember)
  rw [functionEq, typesEq] at checked
  exact checkEvidence_sound checked

theorem validated_certificate {m : GIR.Module} {fn : Func} {certificate : FactCertificate}
    (accepted : Goose.GIR.validate m = .ok ()) (member : fn ∈ m.allFuncs)
    (present : fn.certificate = some certificate) :
    CertificateValid m fn (fn.valueTypes m) certificate := by
  have evidence := validated_evidence accepted member
  cases evidence with
  | absent absent _ => rw [present] at absent; contradiction
  | present found same valid =>
    rw [present] at same
    cases same
    exact valid

theorem PointFactsHold.functionEntry {cfg : GCfg} {fn : Func} {depth : Nat} {args : List Val}
    {before after : St} {fr : Frame} {certificate : FactCertificate}
    (accepted : Goose.GIR.validate cfg.mod = .ok ()) (member : fn ∈ cfg.mod.allFuncs)
    (present : fn.certificate = some certificate)
    (entry : FunctionEntry fn depth args before fr after) :
    PointFactsHold ⟨cfg, fn⟩ certificate (0, 0) fr after := by
  have valid := validated_certificate accepted member present
  obtain ⟨arity, act, fresh, allocated, entered⟩ := entry
  cases blockAt : fn.blocks[0]? with
  | none => simp [Goose.GIR.enterBlock, blockAt, fault, M.stop] at entered
  | some block => exact PointFactsHold.entry valid blockAt fr after

def TrueComparisonFacts (cfg : GCfg) : Prop :=
  ∀ {fn point fr state condition yes yesArgs no noArgs left right},
    RuntimePoint cfg fn point fr state →
    instAt fn point = some (.term (.condbr condition yes yesArgs no noArgs)) →
    fn.defOp? condition = some (.cmp .lt .i64 left right) →
    fr.vals[condition]? = some (.val (.bool true)) →
    FactHolds fr state (.lt left right)

theorem validated_trueComparisonFacts {cfg : GCfg} (accepted : Goose.GIR.validate cfg.mod = .ok ()) :
    TrueComparisonFacts cfg := by
  intro fn point fr state condition yes yesArgs no noArgs left right reachable branch comparison conditionTrue
  obtain ⟨a, b, leftCell, rightCell, ordered⟩ :=
    validated_true_cmp_fact accepted reachable branch comparison conditionTrue
  exact ⟨a, b, ⟨.i64, leftCell⟩, ⟨.i64, rightCell⟩, ordered⟩

theorem reachable_facts {cfg : GCfg} (accepted : Goose.GIR.validate cfg.mod = .ok ())
    {fn : Func} {point : Pt} {fr : Frame} {state : St}
    (reachable : RuntimePoint cfg fn point fr state) :
    ∀ certificate, fn.certificate = some certificate →
      PointFactsHold ⟨cfg, fn⟩ certificate point fr state := by
  induction reachable with
  | initializer fuelPositive indexValid initialized lookup entry =>
    intro certificate present
    exact PointFactsHold.functionEntry accepted
      ((RuntimePoint.initializer fuelPositive indexValid initialized lookup entry).function_mem) present entry
  | entry fuelPositive globals lookup entry =>
    intro certificate present
    exact PointFactsHold.functionEntry accepted
      ((RuntimePoint.entry fuelPositive globals lookup entry).function_mem) present entry
  | call callerPoint instruction depth read lookup entry ih =>
    intro certificate present
    exact PointFactsHold.functionEntry accepted
      ((RuntimePoint.call callerPoint instruction depth read lookup entry).function_mem) present entry
  | step before transition ih =>
    intro certificate present
    have member := before.function_mem
    have valid := validated_certificate accepted member present
    have terminated := ((Goose.GIR.validate_sound cfg.mod accepted).1 _ member).1
    have holds := ih certificate present
    cases transition with
    | define instruction eval =>
      exact PointFactsHold.defStep accepted member valid holds instruction eval
    | effect instruction eval => exact PointFactsHold.effStep valid holds instruction eval
    | branch instruction read enter =>
      have same := getCells_state read
      subst_vars
      exact PointFactsHold.br valid terminated holds instruction enter
    | branchFalse instruction test read enter =>
      obtain ⟨cell, sameTest⟩ := branch_test_cell test
      have sameRead := getCells_state read
      subst_vars
      exact PointFactsHold.condFalse valid terminated holds instruction enter
    | branchTrue instruction test read enter =>
      obtain ⟨cell, sameTest⟩ := branch_test_cell test
      have sameRead := getCells_state read
      subst_vars
      exact PointFactsHold.condTrue valid terminated holds instruction
        (fun left right definition => validated_trueComparisonFacts accepted before instruction definition cell) enter

theorem hasProvenIndex_at {fn : Func} {point : Pt} {result view index : ValueId}
    (instruction : instAt fn point = some (.def result (.indexProven view index))) :
    hasProvenIndex fn = true := by
  unfold instAt at instruction
  cases blockAt : fn.blocks[point.1]? with
  | none => simp [blockAt] at instruction
  | some block =>
    simp only [blockAt, Option.bind_some] at instruction
    apply Array.any_eq_true'.mpr
    refine ⟨block, Array.mem_of_getElem? blockAt, List.any_eq_true.mpr ?_⟩
    exact ⟨.def result (.indexProven view index), List.mem_of_getElem? instruction, rfl⟩

theorem reachable_index {cfg : GCfg} (accepted : Goose.GIR.validate cfg.mod = .ok ())
    {fn : Func} {point : Pt} {fr : Frame} {state : St}
    {result view index : ValueId} (reachable : RuntimePoint cfg fn point fr state)
    (instruction : instAt fn point = some (.def result (.indexProven view index))) :
    execPure ⟨cfg, fn⟩ fr (.indexProven view index) =
      execPure ⟨cfg, fn⟩ fr (.indexChecked view index none) := by
  have evidence := validated_evidence accepted reachable.function_mem
  cases evidence with
  | absent absent noProven =>
    have contains := hasProvenIndex_at instruction
    rw [noProven] at contains
    contradiction
  | present certificate present valid =>
    exact PointFactsHold.index valid
      (reachable_facts accepted reachable certificate present) instruction

end Goose.Proofs.Bounds
