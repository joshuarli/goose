import Goose.Core.Validate
import Goose.Core.Eval

/-!
What `validate` is meant to guarantee, stated as propositions. Nothing here is
proved; each is a target for the proofs about `eval` and `validate`.

The dynamic properties speak of `eval` alone. The rule-level properties speak
of the per-item stages `validate` is built from, collected without
short-circuiting so that a failure of one rule does not hide another.
-/

namespace Goose.Core

def FaultKind.isShape : FaultKind → Bool
  | .shape | .unbound | .arity | .flow => true
  | .danglingRoot | .pathRange => false

def FaultKind.isMemory : FaultKind → Bool
  | .danglingRoot | .pathRange => true
  | .shape | .unbound | .arity | .flow => false

/-- A result that was reached with some fuel is reached with more. Together
with `eval` being a function this makes results unique. -/
def FuelMonotone (m : Module) : Prop :=
  ∀ (n k : Nat) (p : NumProfile) (o : Outcome) (t : String),
    n ≤ k → eval n p m = .done o t → eval k p m = .done o t

/-- The conclusion of the safety theorem: no run of the module faults. -/
def FaultFree (m : Module) : Prop :=
  ∀ (n : Nat) (p : NumProfile) (k : FaultKind), eval n p m ≠ .fault k

/-- `V-TYPE`, and the mutability half of `V-CALL`: no run meets a value of the
wrong shape, a table entry that is missing, a call with the wrong number of
arguments or a `break`, `continue` or block result leaving a function body. -/
def TypeSafe (m : Module) : Prop :=
  ∀ (n : Nat) (p : NumProfile) (k : FaultKind), eval n p m = .fault k → k.isShape = false

/-- `V-ROOT`, `V-BLOCK`, `V-RESULT` and the root half of `V-CALL`: no run reads
or writes through a root whose scope has ended or a path outside its object. -/
def MemorySafe (m : Module) : Prop :=
  ∀ (n : Nat) (p : NumProfile) (k : FaultKind), eval n p m = .fault k → k.isMemory = false

/-- Safety is the conjunction of the two classes of fault being absent. -/
theorem faultFree_iff (m : Module) : FaultFree m ↔ TypeSafe m ∧ MemorySafe m := by
  constructor
  · intro h
    exact ⟨fun n p k hk => absurd hk (h n p k), fun n p k hk => absurd hk (h n p k)⟩
  · intro ⟨ht, hm⟩ n p k hk
    have a := ht n p k hk
    have b := hm n p k hk
    cases k <;> simp [FaultKind.isShape, FaultKind.isMemory] at a b

/-- Every rejection `validate` would give, each stage run on its own. -/
def stageRejections (m : Module) : List Rejection :=
  let err {α : Type} (r : V α) : List Rejection :=
    match r with
    | .error e => [e]
    | .ok _ => []
  err (checkEntry m)
    ++ (List.range m.globals.size).flatMap (fun g =>
        match m.globals[g]? with
        | some gl => err (checkGlobal m g gl)
        | none => [])
    ++ m.impls.toList.flatMap (fun i => err (checkImpl m i))
    ++ m.contexts.toList.flatMap (fun c => err (checkContext m c))
    ++ (List.range m.globals.size).flatMap (fun g => err (checkInitRoots m g))

/-- Rule `r` holds of the module: no stage rejects it for `r`. `V-MUT` and the
mutability half of `V-CALL` are decided inside the typing stage, the root half
of `V-CALL` and `V-SUMMARY` inside the context stage, and what an initializer
may reach, a part of `V-CALL`, in the last stage. -/
def RuleHolds (r : Rule) (m : Module) : Prop :=
  ∀ e ∈ stageRejections m, e.rule ≠ r

/-- `validate` accepts exactly the modules for which every rule holds. -/
def ValidateAgrees (m : Module) : Prop :=
  validate m = .ok () ↔ ∀ r, RuleHolds r m

end Goose.Core
