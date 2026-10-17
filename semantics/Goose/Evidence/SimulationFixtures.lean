import Goose.Evidence.Simulation

namespace Goose.Proofs.Bounds.SimulationChecks

open Goose.Core Goose.GIR Goose.Evidence

inductive Variant
  | returned
  | aborted
  | called
  | looping
  deriving DecidableEq

inductive Placement
  | immediate
  | delayed
  | predecessor
  deriving DecidableEq

def entryBlock (placement : Placement) : GIR.Block := ⟨[], [
  .def 0 (.constInt .i64 0),
  .def 1 (.constInt .i64 1),
  .eff (.enter 0),
  .def 2 (.arrLit (.arr (.int .i64) 1) [1]),
  .eff (.slotInit 0 2 (some 0)),
  .def 3 (.slotAddr 0),
  .def 4 (.arrayLen 3),
  .def 5 (.cmp .lt .i64 0 4)] ++ match placement with
    | .immediate => [.term (.condbr 5 1 [] 2 [])]
    | .delayed => [.def 9 (.constInt .i64 2), .term (.condbr 5 1 [] 2 [])]
    | .predecessor => [.term (.br 1 [])]⟩

def dispatchBlock : GIR.Block := ⟨[], [.def 9 .constUnit, .term (.condbr 5 2 [] 3 [])]⟩

def indexBlock (variant : Variant) (placement : Placement := .immediate) : GIR.Block := ⟨[], [
  .def 6 (.snapshot .owner 3),
  .def 7 (.indexProven 6 0),
  .def 8 (.load 7),
  .eff (.print [.val 8] (some 0))] ++ match variant with
    | .aborted => [.term (.abort .userAbort (some 0))]
    | .called | .looping => [.def (if placement == .immediate then 9 else 10) (.call 1 [] (some 0)), .eff (.leave 0), .term (.ret [] none)]
    | .returned => [.eff (.leave 0), .term (.ret [] none)]⟩

def falseBlock : GIR.Block := ⟨[], [.eff (.leave 0), .term (.ret [] none)]⟩

def entryFacts : Facts := [.ge0 0, .ge0 1, .lenGe 3 4, .ge0 4]

def mainFunction (variant : Variant) (placement : Placement := .immediate) : Func :=
  { name := "main"
    params := []
    results := []
    slots := #[⟨.arr (.int .i64) 1, .mutable, 0, 0⟩]
    scopes := #[none]
    blocks := match placement with
      | .predecessor => #[entryBlock placement, dispatchBlock, indexBlock variant placement, falseBlock]
      | _ => #[entryBlock placement, indexBlock variant placement, falseBlock]
    summary := .unknown
    org := none
    certificate := some (match placement with
      | .predecessor => #[[], entryFacts, entryFacts ++ [.lt 0 4], entryFacts]
      | _ => #[[], entryFacts ++ [.lt 0 4], entryFacts]) }

def helperFunction (variant : Variant) : Func :=
  { name := "helper"
    params := []
    results := []
    slots := #[]
    scopes := #[]
    blocks := match variant with
      | .looping => #[⟨[], [.def 0 (.constBool true), .term (.br 1 [])]⟩,
          ⟨[], [.term (.condbr 0 1 [] 2 [])]⟩, ⟨[], [.term (.ret [] none)]⟩]
      | _ => #[⟨[], [.def 0 (.constInt .i64 7), .eff (.print [.val 0] (some 0)), .term (.ret [] none)]⟩]
    summary := .unknown
    org := none }

def fixture (variant : Variant) (placement : Placement := .immediate) : GIR.Module :=
  { files := #["bounds.goose"]
    globals := #[]
    funcs := #[mainFunction variant placement, helperFunction variant]
    entry := 0
    origins := #[⟨0, 1, "bounds"⟩] }

private def mainTypes (variant : Variant) (placement : Placement) : Array (Option VTy) :=
  #[some (.data (.int .i64)), some (.data (.int .i64)),
    some (.data (.arr (.int .i64) 1)), some (.data (.ref .mutable (.arr (.int .i64) 1))),
    some (.data (.int .i64)), some (.data .bool), some (.view .mutable (.int .i64)),
    some (.data (.ref .mutable (.int .i64))), some (.data (.int .i64))] ++
  (match placement with
    | .immediate => #[]
    | .delayed => #[some (.data (.int .i64))]
    | .predecessor => #[some (.data .unit)]) ++
  (match variant with
    | .called | .looping => #[some (.data .unit)]
    | _ => #[])

private def helperTypes (variant : Variant) : Array (Option VTy) :=
  #[some (.data (match variant with | .looping => .bool | _ => .int .i64))]

private theorem main_valueTypes (variant : Variant) (placement : Placement) :
    (mainFunction variant placement).valueTypes (fixture variant placement) = mainTypes variant placement := by
  cases variant <;> cases placement <;> cbv

private theorem helper_valueTypes (variant : Variant) (placement : Placement) :
    (helperFunction variant).valueTypes (fixture variant placement) = helperTypes variant := by
  cases variant <;> cases placement <;> cbv

private theorem main_checkTypes (variant : Variant) (placement : Placement) :
    checkTypes (fixture variant placement) "function main" (mainFunction variant placement) (mainTypes variant placement) = .ok () := by
  unfold checkTypes Module.tyEnv
  rw [main_valueTypes]
  cases variant <;> cases placement <;> cbv

private theorem fixture_infos (variant : Variant) (placement : Placement) :
    (fixture variant placement).infos =
      [FnInfo.mk "function main" (mainFunction variant placement) (mainTypes variant placement),
       FnInfo.mk "function helper" (helperFunction variant) (helperTypes variant)] := by
  unfold Module.infos
  change [FnInfo.mk "function main" (mainFunction variant placement) ((mainFunction variant placement).valueTypes (fixture variant placement)),
    FnInfo.mk "function helper" (helperFunction variant) ((helperFunction variant).valueTypes (fixture variant placement))] = _
  rw [main_valueTypes, helper_valueTypes]

private theorem helper_checkTypes (variant : Variant) (placement : Placement) :
    checkTypes (fixture variant placement) "function helper" (helperFunction variant) (helperTypes variant) = .ok () := by
  unfold checkTypes Module.tyEnv
  rw [helper_valueTypes]
  cases variant <;> cases placement <;> cbv

private theorem checkAll_success {items : List α} {action : α → Except ε Unit}
    (checked : ∀ item ∈ items, action item = .ok ()) : checkAll items action = .ok () := by
  induction items with
  | nil => rfl
  | cons item rest inductionHypothesis =>
    simp only [checkAll, checked item (by simp), bind, Except.bind]
    exact inductionHypothesis (fun next member => checked next (by simp [member]))

private theorem bind_success {action : Except ε α} {next : α → Except ε β} {value : α} {result : β}
    (first : action = .ok value) (remaining : next value = .ok result) :
    (action >>= next) = .ok result := by
  rw [first]
  exact remaining

private theorem validate_of_checks (m : GIR.Module)
    (entry : checkEntryAndGlobals m = .ok ())
    (symbols : (checkAll m.labelled fun (l, f) => checkSymbols m l f) = .ok ())
    (structs : checkStructTypes m = .ok ())
    (types : (checkAll m.infos fun i => checkTypes m i.label i.f i.vt) = .ok ())
    (cfg : (checkAll m.infos fun i => checkCfg i.label i.f i.vt) = .ok ())
    (unreachable : checkUnreachable m = .ok ())
    (storage : (checkAll (m.infos.zip (m.infos.map fun i => walkScopes i.label i.f)) fun (i, w) => do
      if let some msg := w.storage then violation .v030 msg
      checkStorage m i.label i.f i.vt
      checkPermissions m i.label i.f i.vt) = .ok ())
    (scopes : (checkAll (m.infos.map fun i => walkScopes i.label i.f) fun w => do
      if let some msg := w.scopes then violation .v040 msg) = .ok ())
    (summaries : checkAll (List.range m.funcs.size) (checkSummaryOf m m.implTypes (resultRoots m m.implTypes) m.rootCount) = .ok ())
    (shrink : (checkAll m.infos fun i => checkShrinkReplace m i.label i.f i.vt) = .ok ())
    (evidence : (checkAll m.infos fun i => asCheck .v080 i.label (checkEvidence m i.f i.vt)) = .ok ())
    (origins : (checkAll m.infos fun i => checkOrigins m.profile i.label i.f) = .ok ()) :
    GIR.validate m = .ok () := by
  unfold GIR.validate
  rw [entry, symbols, structs, types, cfg, unreachable]
  simp only [bind, Except.bind]
  apply bind_success (value := ())
  · apply checkAll_success
    intro pair member
    have checked := checkAll_ok storage pair member
    rcases pair with ⟨info, walk⟩
    cases found : walk.storage <;>
      simpa only [found, bind, Except.bind, pure, Except.pure] using checked
  · apply bind_success (value := ())
    · apply checkAll_success
      intro walk member
      have checked := checkAll_ok scopes walk member
      cases found : walk.scopes <;>
        simpa only [found, pure, Except.pure] using checked
    · simp only [GIR.checkShrinkReplace_canonical]
      rw [summaries, shrink, evidence, origins]

private theorem fixture_checks (variant : Variant) (placement : Placement) : GIR.validate (fixture variant placement) = .ok () := by
  apply validate_of_checks
  · cases variant <;> cases placement <;> cbv
  · cases variant <;> cases placement <;> cbv
  · cases variant <;> cases placement <;> cbv
  · rw [fixture_infos]
    simp only [checkAll, main_checkTypes, helper_checkTypes, bind, Except.bind, pure, Except.pure]
  · rw [fixture_infos]
    cases variant <;> cases placement <;> cbv
  · cases variant <;> cases placement <;> cbv
  · rw [fixture_infos]
    cases variant <;> cases placement <;> cbv
  · rw [fixture_infos]
    cases variant <;> cases placement <;> cbv
  · unfold Module.implTypes
    rw [fixture_infos]
    cases variant <;> cases placement <;> cbv
  · rw [fixture_infos]
    simp only [checkAll, checkShrinkReplace_eq]
    cases variant <;> cases placement <;> cbv
  · rw [fixture_infos]
    cases variant <;> cases placement <;> cbv
  · rw [fixture_infos]
    cases variant <;> cases placement <;> cbv

theorem fixture_accepts (variant : Variant) (placement : Placement := .immediate) :
    (match validate (fixture variant placement) with | .ok _ => true | .error _ => false) = true := by
  rw [fixture_checks]

theorem fixture_accepted (variant : Variant) (placement : Placement := .immediate) :
    validate (fixture variant placement) = .ok () := by
  have accepted := fixture_accepts variant placement
  cases checked : validate (fixture variant placement) with
  | error violation => simp [checked] at accepted
  | ok ignored => cases ignored; rfl

def defines (value : ValueId) : Inst → Bool
  | .def result _ => result == value
  | _ => false

theorem constant_position (variant : Variant) (placement : Placement) :
    ∀ block : Fin 4, ∀ offset : Fin 10,
    ((instAt (mainFunction variant placement) (block.val, offset.val)).map (defines 0)).getD false = true →
      block.val = 0 ∧ offset.val = 0 := by
  cases variant <;> cases placement <;> decide +kernel

theorem comparison_position (variant : Variant) (placement : Placement) :
    ∀ block : Fin 4, ∀ offset : Fin 10,
    ((instAt (mainFunction variant placement) (block.val, offset.val)).map (defines 5)).getD false = true →
      block.val = 0 ∧ offset.val = 7 := by
  cases variant <;> cases placement <;> decide +kernel

theorem array_length_position (variant : Variant) (placement : Placement) :
    ∀ block : Fin 4, ∀ offset : Fin 10,
    ((instAt (mainFunction variant placement) (block.val, offset.val)).map (defines 4)).getD false = true →
      block.val = 0 ∧ offset.val = 6 := by
  cases variant <;> cases placement <;> decide +kernel

theorem block_lengths (variant : Variant) (placement : Placement) :
    (mainFunction variant placement).blocks.toList.all (fun block => decide (block.insts.length ≤ 10)) = true := by
  cases variant <;> cases placement <;> decide +kernel

theorem block_parameters (variant : Variant) (placement : Placement) :
    (mainFunction variant placement).blocks.toList.all (fun block => block.params.isEmpty) = true := by
  cases variant <;> cases placement <;> decide +kernel

def rank (point : Pt) : Nat := point.1 * 16 + point.2

theorem branch_ranks (variant : Variant) (placement : Placement) :
    ∀ block : Fin 4, ∀ offset : Fin 10,
    (match instAt (mainFunction variant placement) (block.val, offset.val) with
      | some (.term term) => term.successors.all fun target => decide (rank (block.val, offset.val) < rank (target, 0))
      | _ => true) = true := by
  cases variant <;> cases placement <;> decide +kernel


end Goose.Proofs.Bounds.SimulationChecks
