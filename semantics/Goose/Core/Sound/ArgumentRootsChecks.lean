import Goose.Core.Sound.ArgumentRoots
namespace Goose.Core.Sound.ArgumentRootsChecks
open Goose.Core Goose.Proofs.Memory

def caller : Impl := {
  name := "caller", params := #[⟨0, .byRef⟩], results := #[],
  vars := #[⟨"slice", .ref .mutable (.slice .mutable .bool), .immutable, 0, 0⟩]
  body := .mk 0 [] none, summary := .unknown }
def context : Context := ⟨0, "caller", [(0, [.param 0])], [], [(0, [.global 0])]⟩
def module : Module := {
  files := #[], types := #[], globals := #[], impls := #[caller],
  contexts := #[context], entry := 0, origins := #[], profile := .shrink }
def consumer : Impl := {
  name := "consume", params := #[⟨0, .byValue⟩], results := #[],
  vars := #[⟨"value", .slice .mutable .bool, .immutable, 0, 0⟩]
  body := .mk 0 [] none, summary := .unknown }
def arg : Arg := .byVal (.read (.deref (.read (.var 0))))
def tenv : TEnv := implEnv module caller
def penv : PEnv := ⟨module, caller, context, [0]⟩
#guard match checkAnnotationShape module caller context with | .ok _ => true | _ => false
#guard match checkResultShape module caller context with | .ok _ => true | _ => false
#guard match checkContentShape module caller context with | .ok _ => false | _ => true
#guard consumer.params.size == [arg].length
#guard match tyArgs tenv consumer consumer.params.toList [arg] 1 with | .ok _ => true | _ => false
#guard match rpArgs penv [arg] ⟨1, {}⟩ with | .ok (roots, _) => roots == [[.global 0]] | _ => false
#guard module.globals[0]?.isNone

#guard match checkContext module context with
  | .error error => error.rule == .root
  | .ok _ => false

example (env : Env) : ¬ ArgumentRootDeclarations module tenv env [[.global 0]] := by
  intro declarations
  have missing := declarations 0 (.global 0) (by simp)
  simpa [module] using missing

end Goose.Core.Sound.ArgumentRootsChecks
