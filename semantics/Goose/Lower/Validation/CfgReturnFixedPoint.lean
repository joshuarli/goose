import Goose.Lower.Validation.CfgReturnBits

namespace Goose.Lower.Validation

open Goose.GIR

def ReturnTransfer (module : Module) (current : Array Bool) : Array Bool :=
  module.funcs.map (funcMayReturn current)

def ReturnTransferMonotone (module : Module) : Prop :=
  ∀ left right, ReturnBitsLE left right →
    ReturnBitsLE (ReturnTransfer module left) (ReturnTransfer module right)

theorem returnTransfer_size (module : Module) (current : Array Bool) :
    (ReturnTransfer module current).size = module.funcs.size := by
  simp [ReturnTransfer]

theorem return_fix_invariant (module : Module) (monotone : ReturnTransferMonotone module)
    (invariant : Array Bool → Prop)
    (preserves : ∀ current, current.size = module.funcs.size → invariant current →
      invariant (ReturnTransfer module current))
    (conservative : Array Bool) (fuel : Nat) (current : Array Bool)
    (sized : current.size = module.funcs.size)
    (ascending : ReturnBitsLE current (ReturnTransfer module current))
    (budget : module.funcs.size - current.count true < fuel)
    (checked : invariant current) :
    invariant (Module.functionsMayReturn.fix module conservative fuel current) ∧
    ReturnTransfer module (Module.functionsMayReturn.fix module conservative fuel current) =
      Module.functionsMayReturn.fix module conservative fuel current := by
  induction fuel generalizing current with
  | zero => omega
  | succ fuel ih =>
    rw [Module.functionsMayReturn.fix]
    by_cases same : ReturnTransfer module current = current
    · simp only [ReturnTransfer] at same
      simp only [same, BEq.rfl, ite_true]
      exact ⟨checked, by simpa [ReturnTransfer] using same⟩
    · have different : current ≠ ReturnTransfer module current := Ne.symm same
      have increase := ascending.strict different
      have nextSized := returnTransfer_size module current
      have nextAscending := monotone current (ReturnTransfer module current) ascending
      have nextBudget : module.funcs.size - (ReturnTransfer module current).count true < fuel := by
        have bounded : (ReturnTransfer module current).count true ≤ module.funcs.size := by
          simpa only [nextSized] using (Array.count_le_size (a := true) (xs := ReturnTransfer module current))
        omega
      have nextChecked := preserves current sized checked
      have result := ih (ReturnTransfer module current) nextSized nextAscending nextBudget nextChecked
      have unequal : (module.funcs.map (funcMayReturn current) == current) = false := by
        exact Bool.eq_false_iff.mpr (fun equal => same (by simpa [ReturnTransfer] using (beq_iff_eq.mp equal)))
      simp only [unequal, Bool.false_eq_true, ite_false]
      exact result

theorem functionsMayReturn_invariant (module : Module) (monotone : ReturnTransferMonotone module)
    (invariant : Array Bool → Prop)
    (initial : invariant (Array.replicate module.funcs.size false))
    (preserves : ∀ current, current.size = module.funcs.size → invariant current →
      invariant (ReturnTransfer module current)) :
    invariant module.functionsMayReturn ∧ ReturnTransfer module module.functionsMayReturn = module.functionsMayReturn := by
  have ascending : ReturnBitsLE (Array.replicate module.funcs.size false)
      (ReturnTransfer module (Array.replicate module.funcs.size false)) := by
    have bottom := ReturnBitsLE.replicate_false (ReturnTransfer module (Array.replicate module.funcs.size false))
    simpa only [returnTransfer_size] using bottom
  have checked := return_fix_invariant module monotone invariant preserves
    (Array.replicate module.funcs.size true) (module.funcs.size + 1)
    (Array.replicate module.funcs.size false) (by simp) ascending (by omega) initial
  exact checked

def ReturnBarrier (forbidden : Nat → Prop) (current : Array Bool) : Prop :=
  ∀ callee, forbidden callee → current[callee]? = some false

theorem functionsMayReturn_barrier (module : Module) (monotone : ReturnTransferMonotone module)
    (forbidden : Nat → Prop) (bounded : ∀ callee, forbidden callee → callee < module.funcs.size)
    (preserves : ∀ current, current.size = module.funcs.size → ReturnBarrier forbidden current →
      ReturnBarrier forbidden (ReturnTransfer module current)) :
    ∀ callee, forbidden callee → module.functionsMayReturn[callee]?.getD true = false := by
  have initial : ReturnBarrier forbidden (Array.replicate module.funcs.size false) := by
    intro callee stopped
    simp [bounded callee stopped]
  have checked := (functionsMayReturn_invariant module monotone (ReturnBarrier forbidden) initial preserves).1
  intro callee stopped
  simp [checked callee stopped]

end Goose.Lower.Validation
