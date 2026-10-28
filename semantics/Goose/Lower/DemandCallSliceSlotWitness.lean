import Goose.Lower.DemandCallSliceSlot
import Goose.Lower.DemandRecursiveNestedCallValidatedGlobals
namespace Goose.Lower.SliceSlotWitness
open Goose.Core Goose.GIR

def owner : Ty := .growshrink .bool
def slice : Ty := .slice .mutable .bool
def mainImpl : Impl := {
  name := "main", params := #[], results := #[]
  vars := #[⟨"header", slice, .mutable, 0, 0⟩]
  body := .mk 0 [.letS 0 (.slice .mutable (.of (.global 0)) .omitted .omitted 0) 0,
    .expr (.call 1 [.byRef .mutable (.var 0)] 0) 0] none, summary := .unknown }
def calleeImpl : Impl := {
  name := "callee", params := #[⟨0, .byRef⟩], results := #[]
  vars := #[⟨"header", .ref .mutable slice, .immutable, 0, 0⟩]
  body := .mk 0 [] none
  summary := .known ⟨[], [], [], [], [], true, true⟩ }
def model : Core.Module := {
  files := #["w.goose"], types := #[]
  globals := #[⟨"owner", owner, .mutable, .arrLit owner [.bool true], 0⟩]
  impls := #[mainImpl, calleeImpl], contexts := #[⟨0, "main", [(0, [.global 0])], [], []⟩,
    ⟨1, "callee", [(0, [.param 0])], [], [(0, [.global 0])]⟩]
  entry := 0, origins := #[⟨0, 1, "expr"⟩], profile := .shrink }

def callPoint : Core.M Val := do
  let cfg : Core.Cfg := ⟨.release, model⟩
  initGlobals 50 cfg [0]
  let act ← freshAct
  let scope ← freshScope
  let env : Core.Env := ⟨mainImpl.vars, act, [(0, scope)], 1⟩
  let _ ← execStmt 45 cfg env (.letS 0 (.slice .mutable (.of (.global 0)) .omitted .omitted 0) 0)
  evalArg 40 cfg env (.byRef .mutable (.var 0))

#guard match Core.validate model with | .ok _ => true | .error _ => false
#guard match Core.runModule 50 ⟨.release, model⟩ St.initial with | .ok _ _ => true | _ => false
#guard match GIR.runModule 100 ⟨.release, lower model⟩ St.initial with | .ok _ _ => true | _ => false
#guard match callPoint St.initial with
  | .ok (.ref slot) state => slot == (⟨.local 1 0 0, []⟩ : Loc) &&
      match state.store.roots[slot.root]? with
      | some (.slice backing start length) => backing.root == .global 0 && start == 0 && length == 1
      | _ => false
  | _ => false
#guard match (⟨model, mainImpl, model.contexts[0]'(by decide)⟩ : AccessEnv).aliasArg [] (.byRef .mutable (.var 0)) with
  | .ok [alias] => alias.ty == slice && alias.roots == [.global 0]
  | _ => false

end Goose.Lower.SliceSlotWitness
