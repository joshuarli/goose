import Goose.Lower.Validation.ExpressionTypingGenerated
import Goose.Lower.Validation.ExpressionTypingRecursiveChecks

namespace Goose.Lower.Validation.ExpressionTypingGeneratedChecks

open Goose.Core Goose.GIR
open ExpressionTypingChecks ExpressionTypingRecursiveChecks

def ownerChoice : Expr :=
  .ifE (.bool true)
    (.mk 1 [] (some (.ref .mutable (.var 1))))
    (.mk 2 [] (some (.ref .mutable (.var 1))))

def compoundOwner : Place := .deref ownerChoice

def compoundOwnerSlice : Expr :=
  .slice .mutable (.of compoundOwner) .omitted (.fromEnd (.lit .i8 1)) 0

def compoundOwnerElement : Place := .elem (.of compoundOwner) nestedIndex 0

theorem compound_owner_source : Core.tyPlace env compoundOwner 2 =
    .ok (⟨.arr (.int .i64) 4, true, true⟩, 2) := by rfl

theorem compound_owner_slice_source : Core.tyExpr env compoundOwnerSlice 2 =
    .ok (.slice .mutable (.int .i64), 2) := by rfl

theorem compound_owner_element_source : Core.tyPlace env compoundOwnerElement 2 =
    .ok (⟨.int .i64, true, true⟩, 2) := by rfl

theorem compound_owner_typed {before after : LS} {value : ValueId}
    (generated : GeneratedBuilderState before)
    (run : lowerPlace compoundOwner (lowerEnv module env.vars []) before = (value, after))
    (live : after.cur.isSome = true) :
    ∃ mu, after.vals[value]? = some (some (.data (.ref mu (.arr (.int .i64) 4)))) :=
  lowerPlace_generated_typed compoundOwner compound_owner_source run live generated

theorem compound_owner_slice_typed {before after : LS} {value : ValueId}
    (generated : GeneratedBuilderState before)
    (run : lowerExpr compoundOwnerSlice (lowerEnv module env.vars []) before = (value, after))
    (live : after.cur.isSome = true) :
    after.vals[value]? = some (some (.data (.slice .mutable (.int .i64)))) :=
  by
  exact lowerExpr_generated_typed compoundOwnerSlice compound_owner_slice_source run live

theorem compound_owner_element_typed {before after : LS} {value : ValueId}
    (generated : GeneratedBuilderState before)
    (run : lowerPlace compoundOwnerElement (lowerEnv module env.vars []) before = (value, after))
    (live : after.cur.isSome = true) :
    after.vals[value]? = some (some (.data (.ref .mutable (.int .i64)))) :=
  lowerPlace_generated_writable_typed compoundOwnerElement compound_owner_element_source rfl run live generated

#guard let (value, after) := lowerExpr compoundOwnerSlice (lowerEnv module env.vars []) initial
  after.vals[value]? == some (some (.data (.slice .mutable (.int .i64))))

#guard let (value, after) := lowerPlace compoundOwnerElement (lowerEnv module env.vars []) initial
  after.vals[value]? == some (some (.data (.ref .mutable (.int .i64))))

end Goose.Lower.Validation.ExpressionTypingGeneratedChecks
