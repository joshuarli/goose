import Goose.Lower.Validation.ExpressionTypingRecursive
import Goose.Lower.Validation.ExpressionTypingChecks

namespace Goose.Lower.Validation.ExpressionTypingRecursiveChecks

open Goose.Core Goose.GIR
open ExpressionTypingChecks

def nestedIndex : Expr :=
  .bin .add
    (.blockE (.mk 1 [] (some (.ifE (.and (.bool true) (.bool true))
      (.mk 2 [] (some (.lit .i64 1)))
      (.mk 3 [] (some (.lit .i64 2)))))))
    (.lit .i64 1) 0

def nestedElement : Place := .elem (.of (.var 1)) nestedIndex 0

def nestedReference : Expr :=
  .ifE (.bool true)
    (.mk 1 [] (some (.blockE (.mk 2 [] (some (.ref .readOnly (.deref (.read (.var 0)))))))))
    (.mk 3 [] (some (.ref .readOnly (.elem (.of (.var 1)) (.lit .i64 0) 0))))

theorem nested_element_source : Core.tyPlace env nestedElement 2 =
    .ok (⟨.int .i64, true, true⟩, 2) := by rfl

theorem nested_element_typed {before after : LS} {value : ValueId}
    (run : lowerPlace nestedElement (lowerEnv module env.vars []) before = (value, after))
    (live : after.cur.isSome = true) :
    ∃ mu, after.vals[value]? = some (some (.data (.ref mu (.int .i64)))) := by
  exact lowerPlace_recursive_typed nestedElement (by trivial) nested_element_source run live

theorem nested_deref_source : Core.tyPlace env (.deref nestedReference) 2 =
    .ok (⟨.int .i64, false, false⟩, 2) := by rfl

theorem nested_deref_typed {before after : LS} {value : ValueId}
    (run : lowerPlace (.deref nestedReference) (lowerEnv module env.vars []) before = (value, after))
    (live : after.cur.isSome = true) :
    ∃ mu, after.vals[value]? = some (some (.data (.ref mu (.int .i64)))) := by
  exact lowerPlace_recursive_typed (.deref nestedReference) (by trivial) nested_deref_source run live

#guard let (_, after) := lowerPlace nestedElement (lowerEnv module env.vars []) initial
       after.cur.isSome

def callee : Core.Impl :=
  { name := "index", params := #[⟨0, .byValue⟩], results := #[.int .i64],
    vars := #[⟨"index", .int .i64, .immutable, 0, 0⟩],
    body := .mk 0 [] (some (.read (.var 0))), summary := .unknown }

def callModule : Core.Module :=
  { module with impls := #[callee], contexts := #[⟨0, "index", [], [], []⟩, ⟨0, "alias", [], [], []⟩] }

def callEnv : Core.TEnv := { env with mod := callModule }

def callElement : Place :=
  .elem (.of (.var 1)) (.call 1 [.byVal (.blockE (.mk 1 [] (some (.lit .i64 2))))] 0) 0

theorem call_element_source : Core.tyPlace callEnv callElement 2 =
    .ok (⟨.int .i64, true, true⟩, 2) := by rfl

theorem call_element_typed {before after : LS} {value : ValueId}
    (run : lowerPlace callElement (lowerEnv callModule env.vars []) before = (value, after))
    (live : after.cur.isSome = true) :
    ∃ mu, after.vals[value]? = some (some (.data (.ref mu (.int .i64)))) := by
  exact lowerPlace_recursive_typed callElement (by trivial) call_element_source run live

#guard let (_, after) := lowerPlace callElement (lowerEnv callModule env.vars []) initial
       after.cur.isSome

#print axioms lowerArgs_recursive_typed
#print axioms call_resultTy_of_passable
#print axioms lowerExpr_recursive_typed
#print axioms lowerPlace_recursive_typed
#print axioms lowerView_recursive_typed
#print axioms lowerBlock_recursive_typed

end Goose.Lower.Validation.ExpressionTypingRecursiveChecks
