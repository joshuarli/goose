import Goose.Lower.Validation.PermissionPreservationFreshRules

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem FreshPermissionInstruction.mutation {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {state : LS} {instruction : Inst} {owner : ValueId}
    (mutation : ContentsMutation owner instruction)
    (contents : FreshContentsEvidence le first state owner) :
    FreshPermissionInstruction module func le first state instruction := by
  cases mutation
  all_goals
    constructor
    · constructor
      · intro a b c impossible; cases impossible
      · intro a b c d e impossible; cases impossible
      · intro other actual; cases actual; exact contents
      · intro a b impossible; cases impossible
      · intro a b c impossible; cases impossible
      · intro a b c d impossible; cases impossible
      · intro a b c d e impossible; cases impossible
      · intro a b c d impossible; cases impossible
      · intro a b impossible; cases impossible
    · constructor
      · intro a b c impossible; cases impossible
      · intro a b c impossible; cases impossible

theorem FreshPermissionInstruction.ownerBorrow {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {state : LS} {value owner : ValueId}
    (contents : FreshContentsEvidence le first state owner) :
    FreshPermissionInstruction module func le first state (.def value (.ownerBorrow owner)) := by
  constructor
  · constructor
    · intro a b c impossible; cases impossible
    · intro a b c d e impossible; cases impossible
    · intro a impossible; cases impossible
    · intro result actualOwner shape; cases shape; exact contents
    · intro a b c impossible; cases impossible
    · intro a b c d impossible; cases impossible
    · intro a b c d e impossible; cases impossible
    · intro a b c d impossible; cases impossible
    · intro a b impossible; cases impossible
  · constructor
    · intro a b c impossible; cases impossible
    · intro a b c impossible; cases impossible

theorem FreshPermissionInstruction.store {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {state : LS} {owner value : ValueId} {origin : Option OriginId}
    {mu : Mutability} {target : Ty}
    (typed : state.vals[owner]? = some (some (.data (.ref mu target))))
    (writable : FreshWritableEvidence le first state owner)
    (transfer : PermissionTransfer module.profile (FreshWritableEvidence le first state)
      (FreshContentsEvidence le first state) value target) :
    FreshPermissionInstruction module func le first state (.eff (.store owner value origin)) := by
  constructor
  · constructor
    · intro actualOwner actualValue actualOrigin shape; cases shape; exact writable
    · intro actualOwner actualValue actualOrigin actualMu actualTarget shape actualTyped
      cases shape
      rw [typed] at actualTyped
      cases actualTyped
      exact transfer
    · intro a impossible; cases impossible
    · intro a b impossible; cases impossible
    · intro a b c impossible; cases impossible
    · intro a b c d impossible; cases impossible
    · intro a b c d e impossible; cases impossible
    · intro a b c d impossible; cases impossible
    · intro a b impossible; cases impossible
  · constructor
    · intro actualOwner actualValue actualOrigin shape; cases shape; exact ⟨_, typed⟩
    · intro a b c impossible; cases impossible

theorem FreshPermissionInstruction.replace {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {state : LS} {owner value : ValueId} {origin : Option OriginId}
    (writable : FreshWritableEvidence le first state owner)
    (contents : FreshContentsEvidence le first state owner) :
    FreshPermissionInstruction module func le first state (.eff (.replace owner value origin)) := by
  constructor
  · constructor
    · intro a b c impossible; cases impossible
    · intro a b c d e impossible; cases impossible
    · intro a impossible; cases impossible
    · intro a b impossible; cases impossible
    · intro actualOwner actualValue actualOrigin shape; cases shape; exact ⟨writable, contents⟩
    · intro a b c d impossible; cases impossible
    · intro a b c d e impossible; cases impossible
    · intro a b c d impossible; cases impossible
    · intro a b impossible; cases impossible
  · constructor
    · intro a b c impossible; cases impossible
    · intro a b c impossible; cases impossible

theorem FreshPermissionInstruction.slotInit {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {state : LS} {slot : SlotId} {value : ValueId} {origin : Option OriginId}
    (transfer : ∀ descriptor, func.slots[slot]? = some descriptor →
      PermissionTransfer module.profile (FreshWritableEvidence le first state)
        (FreshContentsEvidence le first state) value descriptor.ty) :
    FreshPermissionInstruction module func le first state (.eff (.slotInit slot value origin)) := by
  constructor
  · constructor
    · intro a b c impossible; cases impossible
    · intro a b c d e impossible; cases impossible
    · intro a impossible; cases impossible
    · intro a b impossible; cases impossible
    · intro a b c impossible; cases impossible
    · intro a b c d impossible; cases impossible
    · intro a b c d e impossible; cases impossible
    · intro actualSlot actualValue actualOrigin descriptor shape row
      cases shape
      exact transfer descriptor row
    · intro a b impossible; cases impossible
  · constructor
    · intro a b c impossible; cases impossible
    · intro a b c impossible; cases impossible

theorem FreshPermissionInstruction.call {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {state : LS} {value : ValueId} {callee : FnId} {args : List ValueId}
    {origin : Option OriginId}
    (transfer : ∀ descriptor, module.funcs[callee]? = some descriptor →
      ∀ entry ∈ descriptor.params.zip args,
        PermissionTransfer module.profile (FreshWritableEvidence le first state)
          (FreshContentsEvidence le first state) entry.2 entry.1) :
    FreshPermissionInstruction module func le first state (.def value (.call callee args origin)) := by
  constructor
  · constructor
    · intro a b c impossible; cases impossible
    · intro a b c d e impossible; cases impossible
    · intro a impossible; cases impossible
    · intro a b impossible; cases impossible
    · intro a b c impossible; cases impossible
    · intro a b c d impossible; cases impossible
    · intro actualValue actualCallee actualArgs actualOrigin descriptor shape row
      cases shape
      exact transfer descriptor row
    · intro a b c d impossible; cases impossible
    · intro a b impossible; cases impossible
  · constructor
    · intro a b c impossible; cases impossible
    · intro a b c impossible; cases impossible

theorem FreshPermissionInstruction.ret {module : GIR.Module} {func : Func} {le : LEnv}
    {first : Nat} {state : LS} {values : List ValueId} {origin : Option OriginId}
    (transfer : ∀ entry ∈ func.results.zip values,
      PermissionTransfer module.profile (FreshWritableEvidence le first state)
        (FreshContentsEvidence le first state) entry.2 entry.1) :
    FreshPermissionInstruction module func le first state (.term (.ret values origin)) := by
  constructor
  · constructor
    · intro a b c impossible; cases impossible
    · intro a b c d e impossible; cases impossible
    · intro a impossible; cases impossible
    · intro a b impossible; cases impossible
    · intro a b c impossible; cases impossible
    · intro a b c d impossible; cases impossible
    · intro a b c d e impossible; cases impossible
    · intro a b c d impossible; cases impossible
    · intro actualValues actualOrigin shape
      cases shape
      exact transfer
  · constructor
    · intro a b c impossible; cases impossible
    · intro a b c impossible; cases impossible

#print axioms FreshPermissionInstruction.slotInit
#print axioms FreshPermissionInstruction.call
#print axioms FreshPermissionInstruction.ret

#print axioms FreshPermissionInstruction.mutation
#print axioms FreshPermissionInstruction.ownerBorrow
#print axioms FreshPermissionInstruction.store
#print axioms FreshPermissionInstruction.replace

end Goose.Lower.Validation
