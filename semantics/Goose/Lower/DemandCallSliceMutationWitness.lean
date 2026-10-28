import Goose.Lower.DemandCallSliceSlotWitness

namespace Goose.Lower.SliceSlotWitness
open Goose.Core Goose.GIR

def mutation : Stmt := .assign (.deref (.read (.var 0)))
  (.slice .mutable (.of (.global 0)) .omitted (.expr (.lit .i64 0)) 0) 0

def mutatingImpl : Impl := { calleeImpl with body := .mk 0 [mutation] none, summary := .known ⟨[.param 0, .global 0], [.param 0], [], [], [.param 0], true, false⟩ }

def verifyingMain : Impl := { mainImpl with body := .mk 0 [
  .letS 0 (.slice .mutable (.of (.global 0)) .omitted .omitted 0) 0,
  .expr (.call 1 [.byRef .mutable (.var 0)] 0) 0,
  .assertS (.cmp .eq (.len (.val (.read (.var 0)))) (.lit .i64 0)) 0] none }

def mutatingModel : Core.Module := { model with impls := #[verifyingMain, mutatingImpl] }
def nonMutatingModel : Core.Module := { mutatingModel with impls := #[verifyingMain, calleeImpl] }

#guard match Core.validate mutatingModel with | .ok _ => true | .error _ => false
#guard match Core.runModule 100 ⟨.release, mutatingModel⟩ St.initial with | .ok _ _ => true | _ => false
#guard match GIR.runModule 200 ⟨.release, lower mutatingModel⟩ St.initial with | .ok _ _ => true | _ => false
#guard match Core.runModule 100 ⟨.release, nonMutatingModel⟩ St.initial with
  | .stop .timeout _ => false | .stop _ _ => true | _ => false
#guard match GIR.runModule 200 ⟨.release, lower nonMutatingModel⟩ St.initial with
  | .stop .timeout _ => false | .stop _ _ => true | _ => false

end Goose.Lower.SliceSlotWitness
