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

theorem fixture_accepts (variant : Variant) (placement : Placement := .immediate) :
    (match validate (fixture variant placement) with | .ok _ => true | .error _ => false) = true := by
  cases variant <;> cases placement <;> decide +kernel

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
