import Goose.Lower.Validation.SymbolTables
import Goose.Lower.Validation.ExpressionTypingCallOps
import Goose.Lower.Validation.ScopeLexical
import Goose.Lower.Validation.ScopeBlocks

namespace Goose.Lower.Validation

open Goose.Core Goose.Core.Sound Goose.GIR

structure Inst.SourceSymbolsWithin (le : LEnv) (scopeCount : Nat) (inst : Inst) : Prop where
  origin : ∀ o, inst.origin = some o → o < le.mod.origins.size
  slots : ∀ s ∈ instSlotRefs inst, s < le.slots.size
  globals : ∀ g ∈ instGlobalRefs inst, g < le.globals.size
  functions : ∀ f ∈ instFunctionRefs inst, f < le.sigs.size
  scopes : ∀ sc ∈ instScopeRefs inst, sc < scopeCount

theorem Inst.SourceSymbolsWithin.def {le : LEnv} {scopeCount : Nat} {value : ValueId}
    {op : Op} (origin : ∀ o, op.origin = some o → o < le.mod.origins.size)
    (references : Op.SymbolRefsValid le op) :
    Inst.SourceSymbolsWithin le scopeCount (.def value op) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Inst.origin] using origin
  · intro slot member
    cases op <;> simp_all [instSlotRefs, Op.SymbolRefsValid]
  · intro global member
    cases op <;> simp_all [instGlobalRefs, Op.SymbolRefsValid]
  · intro function member
    cases op <;> simp_all [instFunctionRefs, Op.SymbolRefsValid]
  · simp [instScopeRefs]

theorem Inst.SourceSymbolsWithin.eff {le : LEnv} {scopeCount : Nat} {effect : Effect}
    (origin : ∀ o, effect.origin = some o → o < le.mod.origins.size)
    (references : Effect.SymbolRefsValid le scopeCount effect) :
    Inst.SourceSymbolsWithin le scopeCount (.eff effect) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Inst.origin] using origin
  · intro slot member
    cases effect <;> simp_all [instSlotRefs, Effect.SymbolRefsValid]
  · simp [instGlobalRefs]
  · simp [instFunctionRefs]
  · intro scope member
    cases effect <;> simp_all [instScopeRefs, Effect.SymbolRefsValid]

theorem Inst.SourceSymbolsWithin.term {le : LEnv} {scopeCount : Nat} {term : Term}
    (origin : ∀ o, term.origin = some o → o < le.mod.origins.size) :
    Inst.SourceSymbolsWithin le scopeCount (.term term) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Inst.origin] using origin
  · simp [instSlotRefs]
  · simp [instGlobalRefs]
  · simp [instFunctionRefs]
  · simp [instScopeRefs]

def LS.SourceSymbolsWF (le : LEnv) (scopeCount : Nat) (state : LS) : Prop :=
  (∀ inst ∈ state.insts, Inst.SourceSymbolsWithin le scopeCount inst) ∧
    (∀ scope ∈ state.stack, scope < scopeCount)

def LS.SourceSymbolsRun (le : LEnv) (scopeCount : Nat) (action : B α) : Prop :=
  ∀ before result after, action le before = (result, after) →
    LS.SourceSymbolsWF le scopeCount before → LS.SourceSymbolsWF le scopeCount after

theorem LS.SourceSymbolsRun.pure {le : LEnv} {scopeCount : Nat} (value : α) :
    LS.SourceSymbolsRun le scopeCount (pure value) := by
  intro before result after run checked
  obtain ⟨_, rfl⟩ := pure_eq.mp run
  exact checked

theorem LS.SourceSymbolsRun.of_unchanged {le : LEnv} {scopeCount : Nat} {action : B α}
    (unchanged : ∀ state, (action le state).2 = state) :
    LS.SourceSymbolsRun le scopeCount action := by
  intro before result after run checked
  have same := congrArg Prod.snd run
  rw [unchanged before] at same
  have afterEq : after = before := same.symm
  subst after
  exact checked

theorem LS.SourceSymbolsRun.of_insts_stack {le : LEnv} {scopeCount : Nat} {action : B α}
    (sameInsts : ∀ state, (action le state).2.insts = state.insts)
    (sameStack : ∀ state, (action le state).2.stack = state.stack) :
    LS.SourceSymbolsRun le scopeCount action := by
  intro before result after run checked
  have stateEq := congrArg Prod.snd run
  have instEq := congrArg LS.insts stateEq
  have stackEq := congrArg LS.stack stateEq
  rw [sameInsts before] at instEq
  rw [sameStack before] at stackEq
  refine ⟨?_, ?_⟩
  · intro inst member
    exact checked.1 inst (by rw [← instEq] at member; exact member)
  · intro scope member
    exact checked.2 scope (by rw [← stackEq] at member; exact member)

theorem LS.SourceSymbolsRun.bind {le : LEnv} {scopeCount : Nat} {action : B α}
    {next : α → B β} (first : LS.SourceSymbolsRun le scopeCount action)
    (second : ∀ value, LS.SourceSymbolsRun le scopeCount (next value)) :
    LS.SourceSymbolsRun le scopeCount (action >>= next) := by
  intro before result after run checked
  obtain ⟨value, mid, firstRun, secondRun⟩ := bind_eq.mp run
  exact second value _ _ _ secondRun (first _ _ _ firstRun checked)

theorem LS.SourceSymbolsRun.curBlock {le : LEnv} {scopeCount : Nat} :
    LS.SourceSymbolsRun le scopeCount Goose.Lower.curBlock := by
  apply LS.SourceSymbolsRun.of_unchanged
  intro state
  rw [curBlock_run]

theorem LS.SourceSymbolsRun.valTy {le : LEnv} {scopeCount : Nat} (value : ValueId) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.valTy value) := by
  apply LS.SourceSymbolsRun.of_unchanged
  intro state
  cases row : state.vals[value]? with
  | none => simp [Goose.Lower.valTy, bind_run, get_apply, pure_run, row]
  | some valueTy => cases valueTy <;>
      simp [Goose.Lower.valTy, bind_run, get_apply, pure_run, row]

theorem LS.SourceSymbolsRun.intTyOf {le : LEnv} {scopeCount : Nat} (value : ValueId) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.intTyOf value) := by
  apply LS.SourceSymbolsRun.of_unchanged
  intro state
  cases row : state.vals[value]? with
  | none => simp [Goose.Lower.intTyOf, Goose.Lower.valTy, bind_run, get_apply, pure_run, row]
  | some valueTy =>
    cases valueTy with
    | none => simp [Goose.Lower.intTyOf, Goose.Lower.valTy, bind_run, get_apply, pure_run, row]
    | some valueType =>
      cases valueType with
      | view _ _ => simp [Goose.Lower.intTyOf, Goose.Lower.valTy, bind_run, get_apply, pure_run, row]
      | data ty => cases ty <;>
          simp [Goose.Lower.intTyOf, Goose.Lower.valTy, bind_run, get_apply, pure_run, row]

theorem LS.SourceSymbolsRun.readAction {le : LEnv} {scopeCount : Nat} :
    LS.SourceSymbolsRun le scopeCount (read : B LEnv) := by
  apply LS.SourceSymbolsRun.of_unchanged
  intro state
  rfl

theorem LS.SourceSymbolsRun.newBlock {le : LEnv} {scopeCount : Nat} (types : List VTy) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.newBlock types) := by
  apply LS.SourceSymbolsRun.of_insts_stack
  · intro state
    simp [newBlock_run_general, LS.insts, Array.toList_push]
  · intro state
    simp [newBlock_run_general]

theorem LS.SourceSymbolsRun.setCur {le : LEnv} {scopeCount : Nat} (current : Option BlockId) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.setCur current) := by
  apply LS.SourceSymbolsRun.of_insts_stack
  · intro state
    simp [setCur_run, LS.insts]
  · intro state
    simp [setCur_run]

theorem LS.sourceSymbols_appendInst {le : LEnv} {scopeCount : Nat} {before : LS}
    (checked : LS.SourceSymbolsWF le scopeCount before) (block : BlockId) (inst : Inst)
    (source : Inst.SourceSymbolsWithin le scopeCount inst) :
    LS.SourceSymbolsWF le scopeCount (before.appendInst block inst) := by
  refine ⟨?_, ?_⟩
  · intro next member
    have checked := checked.1
    change next ∈ (before.blocks.modify block fun current =>
      { current with insts := current.insts.push inst }).toList.flatMap (fun current => current.insts.toList) at member
    obtain ⟨current, currentMember, instructionMember⟩ := List.mem_flatMap.mp member
    obtain ⟨index, lookup⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp currentMember)
    rw [Array.getElem?_modify] at lookup
    by_cases same : block = index
    · simp only [same, ↓reduceIte] at lookup
      cases previous : before.blocks[index]? with
      | none => simp [previous] at lookup
      | some old =>
        simp only [previous, Option.map_some, Option.some.injEq] at lookup
        subst current
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at instructionMember
        rcases instructionMember with oldInstruction | fresh
        · exact checked next (by
            simp only [LS.insts, List.mem_flatMap]
            exact ⟨old, Array.mem_toList_iff.mpr (Array.mem_of_getElem? previous), oldInstruction⟩)
        · subst next
          exact source
    · simp only [same, ↓reduceIte] at lookup
      exact checked next (by
        simp only [LS.insts, List.mem_flatMap]
        exact ⟨current, Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup), instructionMember⟩)
  · simpa [LS.appendInst] using checked.2

theorem LS.SourceSymbolsRun.emitDef {le : LEnv} {scopeCount : Nat} {op : Op}
    (origin : ∀ o, op.origin = some o → o < le.mod.origins.size)
    (references : Op.SymbolRefsValid le op) :
    LS.SourceSymbolsRun le scopeCount (emitDef op) := by
  intro before result after run checked
  cases current : before.cur with
  | none =>
    rw [emitDef_none op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitDef_run op le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    have source : Inst.SourceSymbolsWithin le scopeCount (.def before.vals.size op) :=
      Inst.SourceSymbolsWithin.def (scopeCount := scopeCount) origin references
    have appended := LS.sourceSymbols_appendInst checked block (.def before.vals.size op) source
    simpa only [LS.SourceSymbolsWF, LS.insts, LS.appendInst] using appended

theorem LS.SourceSymbolsRun.emitDef_unreferenced {le : LEnv} {scopeCount : Nat} {op : Op}
    (noOrigin : op.origin = none) (references : Op.SymbolRefsValid le op) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.emitDef op) := by
  apply LS.SourceSymbolsRun.emitDef
  · intro origin equality
    rw [noOrigin] at equality
    cases equality
  · exact references

theorem LS.SourceSymbolsRun.freezeTo {le : LEnv} {scopeCount : Nat}
    (mutability : Core.Mutability) (address : ValueId) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.freezeTo mutability address) := by
  change LS.SourceSymbolsRun le scopeCount
    (Goose.Lower.valTy address >>= fun valueTy =>
      match mutability, valueTy with
      | .readOnly, .data (.ref .mutable _) => Goose.Lower.emitDef (.refFreeze address)
      | _, _ => Pure.pure address)
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.valTy address)
    (LS.SourceSymbolsRun.valTy address)
  intro valueTy
  cases mutability with
  | mutable => exact LS.SourceSymbolsRun.pure address
  | readOnly =>
    cases valueTy with
    | view _ _ => exact LS.SourceSymbolsRun.pure address
    | data ty =>
      cases ty with
      | ref mutability _ =>
        cases mutability with
        | mutable =>
          exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by
            simp [Op.SymbolRefsValid])
        | readOnly => exact LS.SourceSymbolsRun.pure address
      | _ => exact LS.SourceSymbolsRun.pure address

theorem LS.SourceSymbolsRun.coerceTo {le : LEnv} {scopeCount : Nat}
    (target : Core.Ty) (value : ValueId) (origin : Core.OriginId)
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.coerceTo target value origin) := by
  unfold Goose.Lower.coerceTo
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.valTy value)
    (LS.SourceSymbolsRun.valTy value)
  intro valueTy
  cases target with
  | ref requested _ =>
    cases valueTy with
    | data sourceTy =>
      cases sourceTy with
      | ref actual _ =>
        cases requested with
        | mutable => simpa [Goose.Lower.coerceTo] using LS.SourceSymbolsRun.pure value
        | readOnly =>
          cases actual with
          | mutable => simpa [Goose.Lower.coerceTo] using
              (LS.SourceSymbolsRun.emitDef_unreferenced (le := le) (scopeCount := scopeCount)
                (op := .refFreeze value) (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]))
          | readOnly => simpa [Goose.Lower.coerceTo] using LS.SourceSymbolsRun.pure value
      | _ => simpa [Goose.Lower.coerceTo] using LS.SourceSymbolsRun.pure value
    | view _ _ => simpa [Goose.Lower.coerceTo] using LS.SourceSymbolsRun.pure value
  | slice requested _ =>
    cases valueTy with
    | data sourceTy =>
      cases sourceTy with
      | slice actual _ =>
        cases requested with
        | mutable => simpa [Goose.Lower.coerceTo] using LS.SourceSymbolsRun.pure value
        | readOnly =>
          cases actual with
          | mutable =>
            simpa [Goose.Lower.coerceTo] using
              (LS.SourceSymbolsRun.bind (action := Goose.Lower.emitDef (.sliceView value))
              (LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin])
                (by simp [Op.SymbolRefsValid]))
                (fun sampled => LS.SourceSymbolsRun.emitDef
                  (by
                    intro emitted equality
                    simp only [Op.origin, Option.some.injEq] at equality
                    cases equality
                    exact originBound)
                  (by simp [Op.SymbolRefsValid])))
          | readOnly => simpa [Goose.Lower.coerceTo] using LS.SourceSymbolsRun.pure value
      | _ => simpa [Goose.Lower.coerceTo] using LS.SourceSymbolsRun.pure value
    | view _ _ => simpa [Goose.Lower.coerceTo] using LS.SourceSymbolsRun.pure value
  | _ => simpa [Goose.Lower.coerceTo] using LS.SourceSymbolsRun.pure value

theorem LS.SourceSymbolsRun.coerceSlot {le : LEnv} {scopeCount : Nat}
    (slot : SlotId) (value : ValueId) (origin : Core.OriginId)
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.coerceSlot slot value origin) := by
  unfold Goose.Lower.coerceSlot
  apply LS.SourceSymbolsRun.bind (action := (read : B LEnv)) LS.SourceSymbolsRun.readAction
  intro env
  cases row : env.slots[slot]? with
  | none => exact LS.SourceSymbolsRun.pure value
  | some destination => exact LS.SourceSymbolsRun.coerceTo destination.ty value origin originBound

theorem LS.SourceSymbolsRun.coerceResult {le : LEnv} {scopeCount : Nat}
    (value : ValueId) (origin : Core.OriginId)
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.coerceResult value origin) := by
  unfold Goose.Lower.coerceResult
  apply LS.SourceSymbolsRun.bind (action := (read : B LEnv)) LS.SourceSymbolsRun.readAction
  intro env
  cases row : env.results.head? with
  | none => exact LS.SourceSymbolsRun.pure value
  | some destination => exact LS.SourceSymbolsRun.coerceTo destination value origin originBound

theorem LS.SourceSymbolsRun.lowerExpr_read {le : LEnv} {scopeCount : Nat} {place : Core.Place}
    (source : LS.SourceSymbolsRun le scopeCount (lowerPlace place)) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.read place)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerPlace place >>= fun address => Goose.Lower.emitDef (.load address))
  apply LS.SourceSymbolsRun.bind (action := lowerPlace place) source
  intro address
  exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by
    simp [Op.SymbolRefsValid])

theorem LS.SourceSymbolsRun.lowerExpr_ref {le : LEnv} {scopeCount : Nat}
    {mutability : Core.Mutability} {place : Core.Place}
    (child : LS.SourceSymbolsRun le scopeCount (lowerPlace place)) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.ref mutability place)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerPlace place >>= fun address => Goose.Lower.freezeTo mutability address)
  apply LS.SourceSymbolsRun.bind (action := lowerPlace place) child
  intro address
  exact LS.SourceSymbolsRun.freezeTo mutability address

theorem LS.SourceSymbolsRun.lowerExpr_lit {le : LEnv} {scopeCount : Nat}
    (ty : Core.IntTy) (value : Int) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.lit ty value)) := by
  change LS.SourceSymbolsRun le scopeCount (Goose.Lower.emitDef (.constInt ty value))
  exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by
    simp [Op.SymbolRefsValid])

theorem LS.SourceSymbolsRun.lowerExpr_bool {le : LEnv} {scopeCount : Nat}
    (value : Bool) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.bool value)) := by
  change LS.SourceSymbolsRun le scopeCount (Goose.Lower.emitDef (.constBool value))
  exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by
    simp [Op.SymbolRefsValid])

theorem LS.SourceSymbolsRun.lowerExprs {le : LEnv} {scopeCount : Nat} :
    ∀ exprs : List Core.Expr, (∀ expr ∈ exprs,
      LS.SourceSymbolsRun le scopeCount (lowerExpr expr)) →
      LS.SourceSymbolsRun le scopeCount (Goose.Lower.lowerExprs exprs)
  | [], _ => by
    change LS.SourceSymbolsRun le scopeCount (Pure.pure [])
    exact LS.SourceSymbolsRun.pure []
  | expr :: rest, children => by
    change LS.SourceSymbolsRun le scopeCount
      (lowerExpr expr >>= fun value => Goose.Lower.lowerExprs rest >>= fun values => Pure.pure (value :: values))
    apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) (children expr (by simp))
    intro _
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.lowerExprs rest)
      (LS.SourceSymbolsRun.lowerExprs rest (fun child member => children child (by simp [member])))
    intro _
    exact LS.SourceSymbolsRun.pure _

theorem LS.SourceSymbolsRun.lowerArg_byVal {le : LEnv} {scopeCount : Nat}
    {expr : Core.Expr} (child : LS.SourceSymbolsRun le scopeCount (lowerExpr expr)) :
    LS.SourceSymbolsRun le scopeCount (lowerArg (.byVal expr)) := by
  exact child

theorem LS.SourceSymbolsRun.lowerArg_byRef {le : LEnv} {scopeCount : Nat}
    {mutability : Core.Mutability} {place : Core.Place}
    (child : LS.SourceSymbolsRun le scopeCount (lowerPlace place)) :
    LS.SourceSymbolsRun le scopeCount (lowerArg (.byRef mutability place)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerPlace place >>= fun address => Goose.Lower.freezeTo mutability address)
  apply LS.SourceSymbolsRun.bind (action := lowerPlace place) child
  intro address
  exact LS.SourceSymbolsRun.freezeTo mutability address

theorem LS.SourceSymbolsRun.lowerArgs {le : LEnv} {scopeCount : Nat} :
    ∀ args : List Core.Arg, (∀ arg ∈ args,
      LS.SourceSymbolsRun le scopeCount (lowerArg arg)) →
      LS.SourceSymbolsRun le scopeCount (Goose.Lower.lowerArgs args)
  | [], _ => by
    change LS.SourceSymbolsRun le scopeCount (Pure.pure [])
    exact LS.SourceSymbolsRun.pure []
  | arg :: rest, children => by
    change LS.SourceSymbolsRun le scopeCount
      (lowerArg arg >>= fun value => Goose.Lower.lowerArgs rest >>= fun values => Pure.pure (value :: values))
    apply LS.SourceSymbolsRun.bind (action := lowerArg arg) (children arg (by simp))
    intro _
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.lowerArgs rest)
      (LS.SourceSymbolsRun.lowerArgs rest (fun child member => children child (by simp [member])))
    intro _
    exact LS.SourceSymbolsRun.pure _

theorem LS.SourceSymbolsRun.lowerPrintArgs {le : LEnv} {scopeCount : Nat} :
    ∀ args : List Core.PrintArg, (∀ expr, Core.PrintArg.expr expr ∈ args →
      LS.SourceSymbolsRun le scopeCount (lowerExpr expr)) →
      LS.SourceSymbolsRun le scopeCount (Goose.Lower.lowerPrintArgs args)
  | [], _ => by
    change LS.SourceSymbolsRun le scopeCount (Pure.pure [])
    exact LS.SourceSymbolsRun.pure []
  | .text text :: rest, children => by
    change LS.SourceSymbolsRun le scopeCount
      (Goose.Lower.lowerPrintArgs rest >>= fun values => Pure.pure (.text text :: values))
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.lowerPrintArgs rest)
      (LS.SourceSymbolsRun.lowerPrintArgs rest (fun expr member => children expr (by simp [member])))
    intro _
    exact LS.SourceSymbolsRun.pure _
  | .expr expr :: rest, children => by
    change LS.SourceSymbolsRun le scopeCount
      (lowerExpr expr >>= fun value =>
        Goose.Lower.lowerPrintArgs rest >>= fun values => Pure.pure (.val value :: values))
    apply LS.SourceSymbolsRun.bind (action := lowerExpr expr)
      (children expr (by simp))
    intro _
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.lowerPrintArgs rest)
      (LS.SourceSymbolsRun.lowerPrintArgs rest (fun child member => children child (by simp [member])))
    intro _
    exact LS.SourceSymbolsRun.pure _

theorem LS.SourceSymbolsRun.lowerExpr_un {le : LEnv} {scopeCount : Nat}
    {op : Core.UnOp} {expr : Core.Expr} {origin : Core.OriginId}
    (child : LS.SourceSymbolsRun le scopeCount (lowerExpr expr))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.un op expr origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr expr >>= fun value =>
      Goose.Lower.intTyOf value >>= fun ty =>
      Goose.Lower.emitDef (.un op ty value (some origin)))
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) child
  intro value
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.intTyOf value)
    (LS.SourceSymbolsRun.intTyOf value)
  intro ty
  apply LS.SourceSymbolsRun.emitDef
  · intro emitted equality
    simp only [Op.origin, Option.some.injEq] at equality
    cases equality
    exact originBound
  · simp [Op.SymbolRefsValid]

theorem LS.SourceSymbolsRun.lowerExpr_conv {le : LEnv} {scopeCount : Nat}
    {kind : Core.ConvKind} {target : Core.Ty} {expr : Core.Expr} {origin : Core.OriginId}
    (child : LS.SourceSymbolsRun le scopeCount (lowerExpr expr))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.conv kind target expr origin)) := by
  simp only [lowerExpr]
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) child
  intro value
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.intTyOf value)
    (LS.SourceSymbolsRun.intTyOf value)
  intro sourceTy
  apply LS.SourceSymbolsRun.emitDef
  · intro emitted equality
    simp only [Op.origin, Option.some.injEq] at equality
    cases equality
    exact originBound
  · simp [Op.SymbolRefsValid]

theorem LS.SourceSymbolsRun.lowerExpr_bin {le : LEnv} {scopeCount : Nat}
    {op : Core.BinOp} {left right : Core.Expr} {origin : Core.OriginId}
    (leftSource : LS.SourceSymbolsRun le scopeCount (lowerExpr left))
    (rightSource : LS.SourceSymbolsRun le scopeCount (lowerExpr right))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.bin op left right origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr left >>= fun leftValue =>
      lowerExpr right >>= fun rightValue =>
      Goose.Lower.intTyOf leftValue >>= fun ty =>
      Goose.Lower.emitDef (.bin op ty leftValue rightValue (some origin)))
  apply LS.SourceSymbolsRun.bind (action := lowerExpr left) leftSource
  intro leftValue
  apply LS.SourceSymbolsRun.bind (action := lowerExpr right) rightSource
  intro rightValue
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.intTyOf leftValue)
    (LS.SourceSymbolsRun.intTyOf leftValue)
  intro ty
  apply LS.SourceSymbolsRun.emitDef
  · intro emitted equality
    simp only [Op.origin, Option.some.injEq] at equality
    cases equality
    exact originBound
  · simp [Op.SymbolRefsValid]

theorem LS.SourceSymbolsRun.lowerExpr_cmp {le : LEnv} {scopeCount : Nat}
    {op : Core.CmpOp} {left right : Core.Expr}
    (leftSource : LS.SourceSymbolsRun le scopeCount (lowerExpr left))
    (rightSource : LS.SourceSymbolsRun le scopeCount (lowerExpr right)) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.cmp op left right)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr left >>= fun leftValue =>
      lowerExpr right >>= fun rightValue =>
      Goose.Lower.valTy leftValue >>= fun ty =>
      match ty with
      | .data (.int intTy) => Goose.Lower.emitDef (.cmp op intTy leftValue rightValue)
      | _ => Goose.Lower.emitDef (.boolCmp op leftValue rightValue))
  apply LS.SourceSymbolsRun.bind (action := lowerExpr left) leftSource
  intro leftValue
  apply LS.SourceSymbolsRun.bind (action := lowerExpr right) rightSource
  intro rightValue
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.valTy leftValue)
    (LS.SourceSymbolsRun.valTy leftValue)
  intro ty
  cases ty with
  | data dataTy => cases dataTy <;>
      exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
  | view mutability element =>
      exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])

theorem LS.SourceSymbolsRun.lowerExpr_not {le : LEnv} {scopeCount : Nat}
    {expr : Core.Expr} (child : LS.SourceSymbolsRun le scopeCount (lowerExpr expr)) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.not expr)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr expr >>= fun value => Goose.Lower.emitDef (.boolNot value))
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) child
  intro value
  exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by
    simp [Op.SymbolRefsValid])

theorem LS.SourceSymbolsRun.lowerExpr_structLit {le : LEnv} {scopeCount : Nat}
    {ty : Core.Ty} {exprs : List Core.Expr}
    (children : LS.SourceSymbolsRun le scopeCount (Goose.Lower.lowerExprs exprs)) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.structLit ty exprs)) := by
  change LS.SourceSymbolsRun le scopeCount
    (Goose.Lower.lowerExprs exprs >>= fun values => Goose.Lower.emitDef (.structLit ty values))
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.lowerExprs exprs) children
  intro values
  exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by
    simp [Op.SymbolRefsValid])

theorem LS.SourceSymbolsRun.lowerExpr_arrLit {le : LEnv} {scopeCount : Nat}
    {ty : Core.Ty} {exprs : List Core.Expr}
    (children : LS.SourceSymbolsRun le scopeCount (Goose.Lower.lowerExprs exprs)) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.arrLit ty exprs)) := by
  change LS.SourceSymbolsRun le scopeCount
    (Goose.Lower.lowerExprs exprs >>= fun values => Goose.Lower.emitDef (.arrLit ty values))
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.lowerExprs exprs) children
  intro values
  exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by
    simp [Op.SymbolRefsValid])

theorem LS.SourceSymbolsRun.lowerExpr_fill {le : LEnv} {scopeCount : Nat}
    {ty : Core.Ty} {expr : Core.Expr}
    (child : LS.SourceSymbolsRun le scopeCount (lowerExpr expr)) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.fill ty expr)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr expr >>= fun value => Goose.Lower.emitDef (.arrFill ty value))
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) child
  intro value
  exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by
    simp [Op.SymbolRefsValid])

theorem LS.SourceSymbolsRun.lowerExpr_slice {le : LEnv} {scopeCount : Nat}
    {mutability : Core.Mutability} {view : Core.View} {lower upper : Core.Bound}
    {origin : Core.OriginId}
    (viewSource : LS.SourceSymbolsRun le scopeCount (lowerView view))
    (lowerSource : LS.SourceSymbolsRun le scopeCount (lowerBound lower))
    (upperSource : LS.SourceSymbolsRun le scopeCount (lowerBound upper))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.slice mutability view lower upper origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerView view >>= fun sampled =>
      lowerBound lower >>= fun low =>
      lowerBound upper >>= fun high =>
      Goose.Lower.emitDef (.viewSlice mutability sampled low high (some origin)))
  apply LS.SourceSymbolsRun.bind (action := lowerView view) viewSource
  intro sampled
  apply LS.SourceSymbolsRun.bind (action := lowerBound lower) lowerSource
  intro low
  apply LS.SourceSymbolsRun.bind (action := lowerBound upper) upperSource
  intro high
  apply LS.SourceSymbolsRun.emitDef
  · intro emitted equality
    simp only [Op.origin, Option.some.injEq] at equality
    cases equality
    exact originBound
  · simp [Op.SymbolRefsValid]

theorem LS.SourceSymbolsRun.lowerExpr_push {le : LEnv} {scopeCount : Nat}
    {place : Core.Place} {expr : Core.Expr} {origin : Option Core.OriginId}
    (placeSource : LS.SourceSymbolsRun le scopeCount (lowerPlace place))
    (exprSource : LS.SourceSymbolsRun le scopeCount (lowerExpr expr))
    (originBound : ∀ value, origin = some value → value < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.push place expr origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerPlace place >>= fun address =>
      lowerExpr expr >>= fun value => Goose.Lower.emitDef (.push address value origin))
  apply LS.SourceSymbolsRun.bind (action := lowerPlace place) placeSource
  intro address
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) exprSource
  intro value
  apply LS.SourceSymbolsRun.emitDef
  · exact originBound
  · simp [Op.SymbolRefsValid]

theorem LS.SourceSymbolsRun.lowerExpr_pop {le : LEnv} {scopeCount : Nat}
    {place : Core.Place} {origin : Core.OriginId}
    (placeSource : LS.SourceSymbolsRun le scopeCount (lowerPlace place))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.pop place origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerPlace place >>= fun address => Goose.Lower.emitDef (.pop address (some origin)))
  apply LS.SourceSymbolsRun.bind (action := lowerPlace place) placeSource
  intro address
  apply LS.SourceSymbolsRun.emitDef
  · intro emitted equality
    simp only [Op.origin, Option.some.injEq] at equality
    cases equality
    exact originBound
  · simp [Op.SymbolRefsValid]

theorem LS.SourceSymbolsRun.lowerPlace_deref {le : LEnv} {scopeCount : Nat}
    {expr : Core.Expr} (child : LS.SourceSymbolsRun le scopeCount (lowerExpr expr)) :
    LS.SourceSymbolsRun le scopeCount (lowerPlace (.deref expr)) := by
  simpa only [lowerPlace] using child

theorem LS.SourceSymbolsRun.lowerPlace_field {le : LEnv} {scopeCount : Nat}
    {owner : Core.Place} {index : Nat}
    (child : LS.SourceSymbolsRun le scopeCount (lowerPlace owner)) :
    LS.SourceSymbolsRun le scopeCount (lowerPlace (.field owner index)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerPlace owner >>= fun address => Goose.Lower.emitDef (.fieldAddr address index))
  apply LS.SourceSymbolsRun.bind (action := lowerPlace owner) child
  intro address
  exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by
    simp [Op.SymbolRefsValid])

theorem LS.SourceSymbolsRun.lowerPlace_elem {le : LEnv} {scopeCount : Nat}
    {view : Core.View} {index : Core.Expr} {origin : Core.OriginId}
    (viewSource : LS.SourceSymbolsRun le scopeCount (lowerView view))
    (indexSource : LS.SourceSymbolsRun le scopeCount (lowerExpr index))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerPlace (.elem view index origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerView view >>= fun sampled =>
      lowerExpr index >>= fun subscript =>
      Goose.Lower.emitDef (.indexChecked sampled subscript (some origin)))
  apply LS.SourceSymbolsRun.bind (action := lowerView view) viewSource
  intro sampled
  apply LS.SourceSymbolsRun.bind (action := lowerExpr index) indexSource
  intro subscript
  apply LS.SourceSymbolsRun.emitDef
  · intro emitted equality
    simp only [Op.origin, Option.some.injEq] at equality
    cases equality
    exact originBound
  · simp [Op.SymbolRefsValid]

theorem LS.SourceSymbolsRun.lowerView_of {le : LEnv} {scopeCount : Nat}
    {place : Core.Place} (child : LS.SourceSymbolsRun le scopeCount (lowerPlace place)) :
    LS.SourceSymbolsRun le scopeCount (lowerView (.of place)) := by
  simp only [lowerView]
  apply LS.SourceSymbolsRun.bind (action := lowerPlace place) child
  intro address
  exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by
    simp [Op.SymbolRefsValid])

theorem LS.SourceSymbolsRun.lowerView_val {le : LEnv} {scopeCount : Nat}
    {expr : Core.Expr} (child : LS.SourceSymbolsRun le scopeCount (lowerExpr expr)) :
    LS.SourceSymbolsRun le scopeCount (lowerView (.val expr)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr expr >>= fun value => Goose.Lower.emitDef (.sliceView value))
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) child
  intro value
  exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by
    simp [Op.SymbolRefsValid])

theorem LS.SourceSymbolsRun.lowerBound_expr {le : LEnv} {scopeCount : Nat}
    {expr : Core.Expr} (child : LS.SourceSymbolsRun le scopeCount (lowerExpr expr)) :
    LS.SourceSymbolsRun le scopeCount (lowerBound (.expr expr)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr expr >>= fun value => Pure.pure (Bnd.val value))
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) child
  intro value
  exact LS.SourceSymbolsRun.pure (Bnd.val value)

theorem LS.SourceSymbolsRun.lowerBound_fromEnd {le : LEnv} {scopeCount : Nat}
    {expr : Core.Expr} (child : LS.SourceSymbolsRun le scopeCount (lowerExpr expr)) :
    LS.SourceSymbolsRun le scopeCount (lowerBound (.fromEnd expr)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr expr >>= fun value => Pure.pure (Bnd.fromEnd value))
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) child
  intro value
  exact LS.SourceSymbolsRun.pure (Bnd.fromEnd value)

theorem LS.SourceSymbolsRun.lowerExpr_len {le : LEnv} {scopeCount : Nat}
    {view : Core.View} (child : LS.SourceSymbolsRun le scopeCount (lowerView view)) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.len view)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerView view >>= fun sampled => Goose.Lower.emitDef (.viewLen sampled))
  apply LS.SourceSymbolsRun.bind (action := lowerView view) child
  intro sampled
  exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by
    simp [Op.SymbolRefsValid])

theorem LS.SourceSymbolsRun.emitEffect {le : LEnv} {scopeCount : Nat} (effect : Effect)
    (origin : ∀ o, effect.origin = some o → o < le.mod.origins.size)
    (references : Effect.SymbolRefsValid le scopeCount effect) :
    LS.SourceSymbolsRun le scopeCount (emitEffect effect) := by
  intro before result after run checked
  cases current : before.cur with
  | none =>
    rw [emitEffect_none effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitEffect_run effect le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact LS.sourceSymbols_appendInst checked block (.eff effect)
      (Inst.SourceSymbolsWithin.eff (scopeCount := scopeCount) origin references)

theorem LS.SourceSymbolsRun.emitTerm {le : LEnv} {scopeCount : Nat} (term : Term)
    (origin : ∀ o, term.origin = some o → o < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (emitTerm term) := by
  intro before result after run checked
  cases current : before.cur with
  | none =>
    rw [emitTerm_none term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    exact checked
  | some block =>
    rw [emitTerm_run term le current] at run
    obtain ⟨_, rfl⟩ := Prod.mk.inj run
    have appended := LS.sourceSymbols_appendInst checked block (.term term)
      (Inst.SourceSymbolsWithin.term (scopeCount := scopeCount) origin)
    simpa only [LS.SourceSymbolsWF, LS.insts, LS.appendInst] using appended

theorem LS.SourceSymbolsRun.patchTerm {le : LEnv} {scopeCount : Nat} (block : BlockId)
    (term : Term) (origin : ∀ o, term.origin = some o → o < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.patchTerm block term) := by
  intro before result after run checked
  rw [patchTerm_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  have appended := LS.sourceSymbols_appendInst checked block (.term term)
    (Inst.SourceSymbolsWithin.term (scopeCount := scopeCount) origin)
  simpa only [LS.SourceSymbolsWF, LS.insts, LS.appendInst] using appended

theorem LS.SourceSymbolsRun.whenLive {le : LEnv} {scopeCount : Nat} (default : α)
    {action : BlockId → B α} (children : ∀ block, LS.SourceSymbolsRun le scopeCount (action block)) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.whenLive default action) := by
  change LS.SourceSymbolsRun le scopeCount
    ((Goose.Lower.curBlock : B (Option BlockId)) >>= fun current =>
      match current with
      | none => (Pure.pure default : B α)
      | some block => action block)
  apply LS.SourceSymbolsRun.bind LS.SourceSymbolsRun.curBlock
  intro current
  cases current with
  | none => exact LS.SourceSymbolsRun.pure default
  | some block => exact children block

theorem LS.SourceSymbolsRun.fork {le : LEnv} {scopeCount : Nat} (condition : ValueId) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.fork condition) := by
  simp only [Goose.Lower.fork]
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.newBlock [])
    (LS.SourceSymbolsRun.newBlock [])
  intro _
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.newBlock [])
    (LS.SourceSymbolsRun.newBlock [])
  intro _
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitTerm _)
  · apply LS.SourceSymbolsRun.emitTerm
    intro origin equality
    simp [Term.origin] at equality
  · intro _
    exact LS.SourceSymbolsRun.pure _

theorem LS.SourceSymbolsRun.scFork {le : LEnv} {scopeCount : Nat}
    (isAnd : Bool) (condition : ValueId) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.scFork isAnd condition) := by
  simp only [Goose.Lower.scFork]
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.newBlock [])
    (LS.SourceSymbolsRun.newBlock [])
  intro _
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.newBlock [.data .bool])
    (LS.SourceSymbolsRun.newBlock [.data .bool])
  intro _
  cases isAnd <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitTerm _)
    · apply LS.SourceSymbolsRun.emitTerm
      intro origin equality
      simp [Term.origin] at equality
    · intro _
      exact LS.SourceSymbolsRun.pure _
  · apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitTerm _)
    · apply LS.SourceSymbolsRun.emitTerm
      intro origin equality
      simp [Term.origin] at equality
    · intro _
      exact LS.SourceSymbolsRun.pure _

theorem LS.SourceSymbolsRun.shortCircuit {le : LEnv} {scopeCount : Nat}
    {isAnd : Bool} {left : ValueId} {right : B ValueId}
    (rightSource : LS.SourceSymbolsRun le scopeCount right) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.shortCircuit isAnd left right) := by
  unfold Goose.Lower.shortCircuit
  apply LS.SourceSymbolsRun.whenLive
  intro current
  change LS.SourceSymbolsRun le scopeCount
    (Goose.Lower.scFork isAnd left >>= fun blocks =>
      Goose.Lower.setCur (some blocks.1) >>= fun _ =>
      right >>= fun value =>
      Goose.Lower.emitTerm (.br blocks.2.1 [value]) >>= fun _ =>
      Goose.Lower.setCur (some blocks.2.1) >>= fun _ =>
      (Pure.pure blocks.2.2 : B ValueId))
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.scFork isAnd left)
    (LS.SourceSymbolsRun.scFork isAnd left)
  intro blocks
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.setCur (some blocks.1))
    (LS.SourceSymbolsRun.setCur (some blocks.1))
  intro _
  apply LS.SourceSymbolsRun.bind (action := right) rightSource
  intro value
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitTerm (.br blocks.2.1 [value]))
  · apply LS.SourceSymbolsRun.emitTerm
    intro origin equality
    simp [Term.origin] at equality
  · intro _
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.setCur (some blocks.2.1))
      (LS.SourceSymbolsRun.setCur (some blocks.2.1))
    intro _
    exact LS.SourceSymbolsRun.pure _

theorem LS.SourceSymbolsRun.lowerExpr_and {le : LEnv} {scopeCount : Nat}
    {left right : Core.Expr}
    (leftSource : LS.SourceSymbolsRun le scopeCount (lowerExpr left))
    (rightSource : LS.SourceSymbolsRun le scopeCount (lowerExpr right)) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.and left right)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr left >>= fun value => Goose.Lower.shortCircuit true value (lowerExpr right))
  apply LS.SourceSymbolsRun.bind (action := lowerExpr left) leftSource
  intro value
  exact LS.SourceSymbolsRun.shortCircuit rightSource

theorem LS.SourceSymbolsRun.lowerExpr_or {le : LEnv} {scopeCount : Nat}
    {left right : Core.Expr}
    (leftSource : LS.SourceSymbolsRun le scopeCount (lowerExpr left))
    (rightSource : LS.SourceSymbolsRun le scopeCount (lowerExpr right)) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.or left right)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr left >>= fun value => Goose.Lower.shortCircuit false value (lowerExpr right))
  apply LS.SourceSymbolsRun.bind (action := lowerExpr left) leftSource
  intro value
  exact LS.SourceSymbolsRun.shortCircuit rightSource

theorem LS.SourceSymbolsRun.lowerExpr_call {le : LEnv} {scopeCount : Nat}
    {context : Core.ContextId} {args : List Core.Arg} {origin : Core.OriginId}
    (argsSource : LS.SourceSymbolsRun le scopeCount (Goose.Lower.lowerArgs args))
    (originBound : origin < le.mod.origins.size)
    (functionReference : Op.SymbolRefsValid le (.call context [] (some origin))) :
    LS.SourceSymbolsRun le scopeCount (lowerExpr (.call context args origin)) := by
  simp only [lowerExpr]
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.lowerArgs args) argsSource
  intro values
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitDef (.call context values (some origin)))
  · apply LS.SourceSymbolsRun.emitDef
    · intro emitted equality
      simp only [Op.origin, Option.some.injEq] at equality
      cases equality
      exact originBound
    · simpa [Op.SymbolRefsValid] using functionReference
  · intro result
    apply LS.SourceSymbolsRun.bind (action := (read : B LEnv)) LS.SourceSymbolsRun.readAction
    intro env
    cases returns : env.mod.noReturn context
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact LS.SourceSymbolsRun.pure result
    · simp only [↓reduceIte]
      apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitTerm .unreachable)
      · apply LS.SourceSymbolsRun.emitTerm
        intro value equality
        simp [Term.origin] at equality
      · intro _
        exact LS.SourceSymbolsRun.pure result

theorem LS.SourceSymbolsRun.lowerStmt_expr {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    {expr : Core.Expr} {origin : Core.OriginId}
    (child : LS.SourceSymbolsRun le scopeCount (lowerExpr expr)) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.expr expr origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr expr >>= fun _ => Pure.pure ())
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) child
  intro _
  exact LS.SourceSymbolsRun.pure ()

theorem LS.SourceSymbolsRun.lowerStmt_let {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    {slot : Core.VarId} {expr : Core.Expr} {origin : Core.OriginId}
    (child : LS.SourceSymbolsRun le scopeCount (lowerExpr expr))
    (slotBound : slot < le.slots.size) (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.letS slot expr origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr expr >>= fun value =>
      Goose.Lower.coerceSlot slot value origin >>= fun coerced =>
      Goose.Lower.emitEffect (.slotInit slot coerced (some origin)))
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) child
  intro value
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.coerceSlot slot value origin)
    (LS.SourceSymbolsRun.coerceSlot slot value origin originBound)
  intro coerced
  apply LS.SourceSymbolsRun.emitEffect
  · intro emitted equality
    simp only [Effect.origin, Option.some.injEq] at equality
    cases equality
    exact originBound
  · simpa [Effect.SymbolRefsValid] using slotBound

theorem LS.SourceSymbolsRun.lowerStmt_assign {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    {place : Core.Place} {expr : Core.Expr} {origin : Core.OriginId}
    (placeSource : LS.SourceSymbolsRun le scopeCount (lowerPlace place))
    (exprSource : LS.SourceSymbolsRun le scopeCount (lowerExpr expr))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.assign place expr origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerPlace place >>= fun address =>
      lowerExpr expr >>= fun value => Goose.Lower.emitEffect (.store address value (some origin)))
  apply LS.SourceSymbolsRun.bind (action := lowerPlace place) placeSource
  intro address
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) exprSource
  intro value
  apply LS.SourceSymbolsRun.emitEffect
  · intro emitted equality
    simp only [Effect.origin, Option.some.injEq] at equality
    cases equality
    exact originBound
  · simp [Effect.SymbolRefsValid]

theorem LS.SourceSymbolsRun.lowerStmt_rebind {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    {slot : Core.VarId} {expr : Core.Expr} {origin : Core.OriginId}
    (exprSource : LS.SourceSymbolsRun le scopeCount (lowerExpr expr))
    (slotBound : slot < le.slots.size) (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.rebind slot expr origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr expr >>= fun value =>
      Goose.Lower.coerceSlot slot value origin >>= fun coerced =>
      Goose.Lower.emitDef (.slotAddr slot) >>= fun address =>
      Goose.Lower.emitEffect (.store address coerced (some origin)))
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) exprSource
  intro value
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.coerceSlot slot value origin)
    (LS.SourceSymbolsRun.coerceSlot slot value origin originBound)
  intro coerced
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitDef (.slotAddr slot))
  · apply LS.SourceSymbolsRun.emitDef
    · intro emitted equality
      simp [Op.origin] at equality
    · simpa [Op.SymbolRefsValid] using slotBound
  · intro address
    apply LS.SourceSymbolsRun.emitEffect
    · intro emitted equality
      simp only [Effect.origin, Option.some.injEq] at equality
      cases equality
      exact originBound
    · simp [Effect.SymbolRefsValid]

theorem LS.SourceSymbolsRun.lowerStmt_assignOp {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    {op : Core.BinOp} {place : Core.Place} {expr : Core.Expr} {origin : Core.OriginId}
    (placeSource : LS.SourceSymbolsRun le scopeCount (lowerPlace place))
    (exprSource : LS.SourceSymbolsRun le scopeCount (lowerExpr expr))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.assignOp op place expr origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerPlace place >>= fun address =>
      Goose.Lower.emitDef (.load address) >>= fun old =>
      lowerExpr expr >>= fun value =>
      Goose.Lower.intTyOf old >>= fun ty =>
      Goose.Lower.emitDef (.bin op ty old value (some origin)) >>= fun result =>
      Goose.Lower.emitEffect (.store address result (some origin)))
  apply LS.SourceSymbolsRun.bind (action := lowerPlace place) placeSource
  intro address
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitDef (.load address))
    (LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]))
  intro old
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) exprSource
  intro value
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.intTyOf old)
    (LS.SourceSymbolsRun.intTyOf old)
  intro ty
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitDef (.bin op ty old value (some origin)))
  · apply LS.SourceSymbolsRun.emitDef
    · intro emitted equality
      simp only [Op.origin, Option.some.injEq] at equality
      cases equality
      exact originBound
    · simp [Op.SymbolRefsValid]
  · intro result
    apply LS.SourceSymbolsRun.emitEffect
    · intro emitted equality
      simp only [Effect.origin, Option.some.injEq] at equality
      cases equality
      exact originBound
    · simp [Effect.SymbolRefsValid]

theorem LS.SourceSymbolsRun.lowerStmt_append {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    {place : Core.Place} {view : Core.View} {origin : Core.OriginId}
    (placeSource : LS.SourceSymbolsRun le scopeCount (lowerPlace place))
    (viewSource : LS.SourceSymbolsRun le scopeCount (lowerView view))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.append place view origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerPlace place >>= fun address =>
      lowerView view >>= fun sampled =>
      Goose.Lower.emitEffect (.append address sampled (some origin)))
  apply LS.SourceSymbolsRun.bind (action := lowerPlace place) placeSource
  intro address
  apply LS.SourceSymbolsRun.bind (action := lowerView view) viewSource
  intro sampled
  apply LS.SourceSymbolsRun.emitEffect
  · intro emitted equality
    simp only [Effect.origin, Option.some.injEq] at equality
    cases equality
    exact originBound
  · simp [Effect.SymbolRefsValid]

theorem LS.SourceSymbolsRun.lowerStmt_popN {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    {place : Core.Place} {count : Core.Expr} {origin : Core.OriginId}
    (placeSource : LS.SourceSymbolsRun le scopeCount (lowerPlace place))
    (countSource : LS.SourceSymbolsRun le scopeCount (lowerExpr count))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.popN place count origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerPlace place >>= fun address =>
      lowerExpr count >>= fun value =>
      Goose.Lower.emitEffect (.popN address value (some origin)))
  apply LS.SourceSymbolsRun.bind (action := lowerPlace place) placeSource
  intro address
  apply LS.SourceSymbolsRun.bind (action := lowerExpr count) countSource
  intro value
  apply LS.SourceSymbolsRun.emitEffect
  · intro emitted equality
    simp only [Effect.origin, Option.some.injEq] at equality
    cases equality
    exact originBound
  · simp [Effect.SymbolRefsValid]

theorem LS.SourceSymbolsRun.lowerStmt_resize {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    {place : Core.Place} {size : Core.Expr} {fill : Option Core.Expr} {origin : Core.OriginId}
    (placeSource : LS.SourceSymbolsRun le scopeCount (lowerPlace place))
    (sizeSource : LS.SourceSymbolsRun le scopeCount (lowerExpr size))
    (fillSource : ∀ expr, fill = some expr → LS.SourceSymbolsRun le scopeCount (lowerExpr expr))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.resize place size fill origin)) := by
  cases fill with
  | none =>
    change LS.SourceSymbolsRun le scopeCount
      (lowerPlace place >>= fun address =>
        lowerExpr size >>= fun count =>
        (Pure.pure none : B (Option ValueId)) >>= fun fill =>
        Goose.Lower.emitEffect (.resize address count fill (some origin)))
    apply LS.SourceSymbolsRun.bind (action := lowerPlace place) placeSource
    intro address
    apply LS.SourceSymbolsRun.bind (action := lowerExpr size) sizeSource
    intro count
    apply LS.SourceSymbolsRun.bind (action := (Pure.pure none : B (Option ValueId)))
      (LS.SourceSymbolsRun.pure none)
    intro fill
    apply LS.SourceSymbolsRun.emitEffect
    · intro emitted equality
      simp only [Effect.origin, Option.some.injEq] at equality
      cases equality
      exact originBound
    · simp [Effect.SymbolRefsValid]
  | some expr =>
    change LS.SourceSymbolsRun le scopeCount
      (lowerPlace place >>= fun address =>
        lowerExpr size >>= fun count =>
        lowerExpr expr >>= fun value =>
        (Pure.pure (some value) : B (Option ValueId)) >>= fun fill =>
        Goose.Lower.emitEffect (.resize address count fill (some origin)))
    apply LS.SourceSymbolsRun.bind (action := lowerPlace place) placeSource
    intro address
    apply LS.SourceSymbolsRun.bind (action := lowerExpr size) sizeSource
    intro count
    apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) (fillSource expr rfl)
    intro value
    apply LS.SourceSymbolsRun.bind (action := (Pure.pure (some value) : B (Option ValueId)))
      (LS.SourceSymbolsRun.pure (some value))
    intro fill
    apply LS.SourceSymbolsRun.emitEffect
    · intro emitted equality
      simp only [Effect.origin, Option.some.injEq] at equality
      cases equality
      exact originBound
    · simp [Effect.SymbolRefsValid]

theorem LS.SourceSymbolsRun.lowerStmt_clear {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    {place : Core.Place} {origin : Core.OriginId}
    (placeSource : LS.SourceSymbolsRun le scopeCount (lowerPlace place))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.clear place origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerPlace place >>= fun address => Goose.Lower.emitEffect (.clear address (some origin)))
  apply LS.SourceSymbolsRun.bind (action := lowerPlace place) placeSource
  intro address
  apply LS.SourceSymbolsRun.emitEffect
  · intro emitted equality
    simp only [Effect.origin, Option.some.injEq] at equality
    cases equality
    exact originBound
  · simp [Effect.SymbolRefsValid]

theorem LS.SourceSymbolsRun.lowerStmt_assignWhole {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    {place : Core.Place} {replacement : Core.Expr} {origin : Core.OriginId}
    (placeSource : LS.SourceSymbolsRun le scopeCount (lowerPlace place))
    (replacementSource : LS.SourceSymbolsRun le scopeCount (lowerExpr replacement))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.assignWhole place replacement origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerPlace place >>= fun address =>
      Goose.Lower.emitEffect (.clear address (some origin)) >>= fun _ =>
      lowerExpr replacement >>= fun value =>
      Goose.Lower.emitEffect (.replace address value (some origin)))
  apply LS.SourceSymbolsRun.bind (action := lowerPlace place) placeSource
  intro address
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitEffect (.clear address (some origin)))
  · apply LS.SourceSymbolsRun.emitEffect
    · intro emitted equality
      simp only [Effect.origin, Option.some.injEq] at equality
      cases equality
      exact originBound
    · simp [Effect.SymbolRefsValid]
  · intro _
    apply LS.SourceSymbolsRun.bind (action := lowerExpr replacement) replacementSource
    intro value
    apply LS.SourceSymbolsRun.emitEffect
    · intro emitted equality
      simp only [Effect.origin, Option.some.injEq] at equality
      cases equality
      exact originBound
    · simp [Effect.SymbolRefsValid]

theorem LS.SourceSymbolsRun.pushScope {le : LEnv} {scopeCount : Nat} (scope : ScopeId)
    (bounded : scope < scopeCount) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.pushScope scope) := by
  intro before result after run checked
  rw [pushScope_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  refine ⟨checked.1, ?_⟩
  intro next member
  simp only [List.mem_cons] at member
  rcases member with same | member
  · subst next
    exact bounded
  · exact checked.2 next member

theorem LS.SourceSymbolsRun.popScope {le : LEnv} {scopeCount : Nat} :
    LS.SourceSymbolsRun le scopeCount Goose.Lower.popScope := by
  intro before result after run checked
  rw [popScope_run] at run
  obtain ⟨_, rfl⟩ := Prod.mk.inj run
  refine ⟨checked.1, ?_⟩
  intro next member
  cases stack : before.stack with
  | nil => simp [stack] at member
  | cons head rest =>
    simp only [stack, List.drop_succ_cons, List.drop_zero] at member
    exact checked.2 next (by rw [stack]; exact List.mem_cons.mpr (Or.inr member))

theorem LS.SourceSymbolsRun.enterScope {le : LEnv} {scopeCount scope : Nat}
    (bounded : scope < scopeCount) :
    LS.SourceSymbolsRun le scopeCount (enterScope scope) := by
  change LS.SourceSymbolsRun le scopeCount
    (Goose.Lower.emitEffect (.enter scope) >>= fun _ => Goose.Lower.pushScope scope)
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitEffect (.enter scope))
  · exact LS.SourceSymbolsRun.emitEffect (.enter scope) (by simp [Effect.origin]) (by
      simpa [Effect.SymbolRefsValid] using bounded)
  · intro _
    exact LS.SourceSymbolsRun.pushScope scope bounded

theorem LS.SourceSymbolsRun.leaveScope {le : LEnv} {scopeCount scope : Nat}
    (bounded : scope < scopeCount) :
    LS.SourceSymbolsRun le scopeCount (leaveScope scope) := by
  change LS.SourceSymbolsRun le scopeCount
    (Goose.Lower.emitEffect (.leave scope) >>= fun _ => Goose.Lower.popScope)
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitEffect (.leave scope))
  · exact LS.SourceSymbolsRun.emitEffect (.leave scope) (by simp [Effect.origin]) (by
      simpa [Effect.SymbolRefsValid] using bounded)
  · intro _
    exact LS.SourceSymbolsRun.popScope

theorem LS.SourceSymbolsRun.leaveAll {le : LEnv} {scopeCount : Nat} :
    ∀ scopes : List ScopeId, (∀ scope ∈ scopes, scope < scopeCount) →
      LS.SourceSymbolsRun le scopeCount (Goose.Lower.leaveAll scopes)
  | [], _ => by
    change LS.SourceSymbolsRun le scopeCount (Pure.pure ())
    exact LS.SourceSymbolsRun.pure ()
  | scope :: rest, bounded => by
    change LS.SourceSymbolsRun le scopeCount
      (Goose.Lower.emitEffect (.leave scope) >>= fun _ => Goose.Lower.leaveAll rest)
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitEffect (.leave scope))
    · apply LS.SourceSymbolsRun.emitEffect
      · intro origin equality
        simp [Effect.origin] at equality
      · simpa [Effect.SymbolRefsValid] using bounded scope (by simp)
    · intro _
      apply LS.SourceSymbolsRun.leaveAll
      intro next member
      exact bounded next (by simp [member])

theorem LS.SourceSymbolsRun.leaveTo {le : LEnv} {scopeCount depth : Nat} :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.leaveTo depth) := by
  intro before result after run checked
  simp only [Goose.Lower.leaveTo, bind_run, get_apply] at run
  let scopes := before.stack.take (before.stack.length - depth)
  have bounded : ∀ scope ∈ scopes, scope < scopeCount := by
    intro scope member
    exact checked.2 scope (List.mem_of_mem_take member)
  exact LS.SourceSymbolsRun.leaveAll scopes bounded before result _ run checked

theorem LS.SourceSymbolsRun.initSlots {le : LEnv} {scopeCount : Nat} :
    ∀ entries : List (SlotId × ValueId × OriginId),
      (∀ entry ∈ entries, entry.1 < le.slots.size ∧ entry.2.2 < le.mod.origins.size) →
      LS.SourceSymbolsRun le scopeCount (initSlots entries)
  | [], _ => by
    change LS.SourceSymbolsRun le scopeCount (Pure.pure ())
    exact LS.SourceSymbolsRun.pure ()
  | (slot, value, origin) :: rest, bounded => by
    change LS.SourceSymbolsRun le scopeCount
      (Goose.Lower.emitEffect (.slotInit slot value (some origin)) >>= fun _ => Goose.Lower.initSlots rest)
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitEffect (.slotInit slot value (some origin)))
    · apply LS.SourceSymbolsRun.emitEffect
      · intro emitted equality
        simp only [Effect.origin, Option.some.injEq] at equality
        cases equality
        exact (bounded (slot, value, origin) (by simp)).2
      · simpa [Effect.SymbolRefsValid] using (bounded (slot, value, origin) (by simp)).1
    · intro _
      apply LS.SourceSymbolsRun.initSlots
      intro entry member
      exact bounded entry (by simp [member])

theorem Inst.SymbolsWithin.ofSource {le : LEnv} {scopeCount valueCount blockCount : Nat}
    {inst : Inst} (source : Inst.SourceSymbolsWithin le scopeCount inst)
    (uses : ∀ v ∈ inst.uses, v < valueCount)
    (targets : ∀ b ∈ instTargetRefs inst, b < blockCount) :
    Inst.SymbolsWithin le scopeCount valueCount blockCount inst :=
  ⟨uses, source.origin, source.slots, source.globals, source.functions, source.scopes, targets⟩

theorem Core.tyExpr_call_success_context_bound {env : Core.TEnv} {context : Core.ContextId}
    {args : List Core.Arg} {origin : Core.OriginId} {ty : Core.Ty} {start finish : Nat}
    (source : Core.tyExpr env (.call context args origin) start = .ok (ty, finish)) :
    context < env.mod.contexts.size := by
  obtain ⟨ctx, _, _, _, _, contextAt, _, _, _, _⟩ := tyExpr_call_tables source
  exact (Array.getElem?_eq_some_iff.mp contextAt).1

theorem Core.tyExpr_call_success_function_reference {env : Core.TEnv}
    {context : Core.ContextId} {args : List Core.Arg} {origin : Core.OriginId}
    {ty : Core.Ty} {start finish : Nat} {le : LEnv}
    (source : Core.tyExpr env (.call context args origin) start = .ok (ty, finish))
    (sigs : le.sigs.size = env.mod.contexts.size) :
    Op.SymbolRefsValid le (.call context [] (some origin)) := by
  simpa only [Op.SymbolRefsValid] using Nat.lt_of_lt_of_eq
    (Core.tyExpr_call_success_context_bound source) sigs.symm

theorem LS.SourceSymbolsRun.lowerPlace_var {env : Core.TEnv} {le : LEnv}
    {scopeCount : Nat} {slot : Core.VarId} {start : Nat}
    {info : Core.PlaceInfo} {finish : Nat}
    (source : Core.tyPlace env (.var slot) start = .ok (info, finish))
    (slots : env.vars.size = le.slots.size) :
    LS.SourceSymbolsRun le scopeCount (lowerPlace (.var slot)) := by
  change LS.SourceSymbolsRun le scopeCount (Goose.Lower.emitDef (.slotAddr slot))
  apply LS.SourceSymbolsRun.emitDef
  · intro origin member
    simp [Op.origin] at member
  · simpa [Op.SymbolRefsValid] using Nat.lt_of_lt_of_eq
      (Core.tyPlace_var_success_bound source) slots

theorem LS.SourceSymbolsRun.lowerPlace_global {env : Core.TEnv} {le : LEnv}
    {scopeCount : Nat} {global : Core.GlobalId} {start : Nat}
    {info : Core.PlaceInfo} {finish : Nat}
    (source : Core.tyPlace env (.global global) start = .ok (info, finish))
    (globals : env.globalLimit ≤ le.globals.size) :
    LS.SourceSymbolsRun le scopeCount (lowerPlace (.global global)) := by
  change LS.SourceSymbolsRun le scopeCount (Goose.Lower.emitDef (.globalAddr global))
  apply LS.SourceSymbolsRun.emitDef
  · intro origin member
    simp [Op.origin] at member
  · simpa [Op.SymbolRefsValid] using Nat.lt_of_lt_of_le
      (Core.tyPlace_global_success_bound source) globals

theorem Core.tyPlace_var_success_slot_reference {env : Core.TEnv} {le : LEnv}
    {slot : Core.VarId} {start : Nat} {info : Core.PlaceInfo} {finish : Nat}
    (source : (Core.tyPlace env (.var slot)).run start = .ok (info, finish))
    (slots : env.vars.size = le.slots.size) :
    Op.SymbolRefsValid le (.slotAddr slot) := by
  simpa [Op.SymbolRefsValid] using Nat.lt_of_lt_of_eq
    (Core.tyPlace_var_success_bound source) slots

theorem Core.tyPlace_global_success_reference {env : Core.TEnv} {le : LEnv}
    {global : Core.GlobalId} {start : Nat} {info : Core.PlaceInfo} {finish : Nat}
    (source : (Core.tyPlace env (.global global)).run start = .ok (info, finish))
    (globals : env.globalLimit ≤ le.globals.size) :
    Op.SymbolRefsValid le (.globalAddr global) := by
  simpa [Op.SymbolRefsValid] using Nat.lt_of_lt_of_le
    (Core.tyPlace_global_success_bound source) globals

theorem Core.tyPlace_elem_success_origin_bound {env : Core.TEnv} {view : Core.View}
    {index : Core.Expr} {origin : Core.OriginId} {start : Nat}
    {info : Core.PlaceInfo} {finish : Nat}
    (source : Core.tyPlace env (.elem view index origin) start = .ok (info, finish)) :
    origin < env.mod.origins.size := by
  simp only [Core.tyPlace] at source
  obtain ⟨_, _, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.declare_success_slot_reference {env : Core.TEnv} {le : LEnv}
    {slot scope start finish : Nat} {localVar : Core.LocalVar}
    (source : Core.declare env slot scope start = .ok (localVar, finish))
    (slots : env.vars.size = le.slots.size) : slot < le.slots.size := by
  have declared := Core.Sound.declare_ok env slot scope start (localVar, finish) source
  have slotBound : slot < env.vars.size := (Array.getElem?_eq_some_iff.mp declared.2.1).1
  exact Nat.lt_of_lt_of_eq slotBound slots

theorem ScopeTableContains.scope_bound {parents : Array (Option ScopeId)}
    {pairs : List (ScopeId × Option ScopeId)}
    (contains : ScopeTableContains parents pairs) {scope : ScopeId} {parent : Option ScopeId}
    (member : (scope, parent) ∈ pairs) : scope < parents.size :=
  (Array.getElem?_eq_some_iff.mp (contains scope parent member)).1

theorem Core.tyExpr_slice_success_origin_bound {env : Core.TEnv} {mutability : Core.Mutability}
    {view : Core.View} {lower upper : Core.Bound} {origin : Core.OriginId} {start : Nat}
    {ty : Core.Ty} {finish : Nat}
    (source : Core.tyExpr env (.slice mutability view lower upper origin) start = .ok (ty, finish)) :
    origin < env.mod.origins.size := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.tyExpr_conv_success_origin_bound {env : Core.TEnv} {kind : Core.ConvKind}
    {target : Core.Ty} {expr : Core.Expr} {origin : Core.OriginId} {start : Nat}
    {ty : Core.Ty} {finish : Nat}
    (source : Core.tyExpr env (.conv kind target expr origin) start = .ok (ty, finish)) :
    origin < env.mod.origins.size := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.tyExpr_un_success_origin_bound {env : Core.TEnv} {op : Core.UnOp}
    {expr : Core.Expr} {origin : Core.OriginId} {start : Nat} {ty : Core.Ty} {finish : Nat}
    (source : Core.tyExpr env (.un op expr origin) start = .ok (ty, finish)) :
    origin < env.mod.origins.size := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.tyExpr_bin_success_origin_bound {env : Core.TEnv} {op : Core.BinOp}
    {left right : Core.Expr} {origin : Core.OriginId} {start : Nat}
    {ty : Core.Ty} {finish : Nat}
    (source : Core.tyExpr env (.bin op left right origin) start = .ok (ty, finish)) :
    origin < env.mod.origins.size := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.tyExpr_call_success_origin_bound {env : Core.TEnv} {context : Core.ContextId}
    {args : List Core.Arg} {origin : Core.OriginId} {start : Nat} {ty : Core.Ty}
    {finish : Nat}
    (source : Core.tyExpr env (.call context args origin) start = .ok (ty, finish)) :
    origin < env.mod.origins.size := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.tyExpr_pop_success_origin_bound {env : Core.TEnv} {owner : Core.Place}
    {origin : Core.OriginId} {start : Nat} {ty : Core.Ty} {finish : Nat}
    (source : Core.tyExpr env (.pop owner origin) start = .ok (ty, finish)) :
    origin < env.mod.origins.size := by
  simp only [Core.tyExpr] at source
  obtain ⟨_, next, shrink, source⟩ := (st_bind_ok _ _ _ _).mp source
  obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.tyExpr_push_success_origin_bound {env : Core.TEnv} {owner : Core.Place}
    {expr : Core.Expr} {start : Nat} {ty : Core.Ty}
    {finish : Nat} {value : Core.OriginId}
    (source : Core.tyExpr env (.push owner expr (some value)) start = .ok (ty, finish)) :
    value < env.mod.origins.size := by
  simp only [Core.tyExpr] at source
  cases profile : env.mod.profile with
  | pilot => simp [profile, chk] at source
  | shrink =>
    simp only [profile] at source
    obtain ⟨_, next, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
    exact (checkOrg_ok _ _ _ _).mp checked |>.1

def stmtSourceOrigin : Core.Stmt → Core.OriginId
  | .letS _ _ origin | .assign _ _ origin | .assignOp _ _ _ origin | .rebind _ _ origin
  | .expr _ origin | .append _ _ origin | .popN _ _ origin | .resize _ _ _ origin
  | .clear _ origin | .assignWhole _ _ origin | .ifS _ _ _ origin | .while _ _ origin
  | .forRange _ _ _ _ origin | .forEach _ _ _ _ _ origin | .ret _ origin | .brk origin
  | .cont origin | .print _ origin | .assertS _ origin | .abort _ origin | .exit _ origin => origin

private theorem checkOrg_bind_origin_bound {env : Core.TEnv} {origin : Core.OriginId}
    {α : Type} {next : Unit → Core.T α} {start finish : Nat} {value : α}
    (source : ((Core.checkOrg env origin) >>= next) start = .ok (value, finish)) :
    origin < env.mod.origins.size := by
  obtain ⟨_, _, checked, _⟩ := (st_bind_ok _ _ _ _).mp source
  exact (checkOrg_ok _ _ _ _).mp checked |>.1

theorem Core.tyStmt_success_origin_bound {env after : Core.TEnv} {scope start finish : Nat}
    {stmt : Core.Stmt}
    (source : Core.tyStmt env scope stmt start = .ok (after, finish)) :
    stmtSourceOrigin stmt < env.mod.origins.size := by
  cases stmt
  case' resize owner size fill origin => cases fill
  case' ifS condition thenBlock otherwise origin => cases otherwise
  case' ret value origin => cases value
  all_goals
    simp only [stmtSourceOrigin] at ⊢
    simp only [Core.tyStmt] at source
    first
    | exact checkOrg_bind_origin_bound source
    | (obtain ⟨_, _, _, rest⟩ := (st_bind_ok _ _ _ _).mp source
       exact checkOrg_bind_origin_bound rest)

theorem LS.SourceSymbolsRun.getState {le : LEnv} {scopeCount : Nat} :
    LS.SourceSymbolsRun le scopeCount (get : B LS) := by
  intro before result after run checked
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
  exact checked

theorem LS.SourceSymbolsRun.isLive {le : LEnv} {scopeCount : Nat} :
    LS.SourceSymbolsRun le scopeCount Goose.Lower.isLive := by
  unfold Goose.Lower.isLive
  apply LS.SourceSymbolsRun.bind LS.SourceSymbolsRun.curBlock
  intro current
  cases current with
  | none => exact LS.SourceSymbolsRun.pure false
  | some _ => exact LS.SourceSymbolsRun.pure true

theorem LS.SourceSymbolsRun.growOwner {le : LEnv} {scopeCount : Nat} (address : ValueId) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.growOwner address) := by
  unfold Goose.Lower.growOwner
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.valTy address)
    (LS.SourceSymbolsRun.valTy address)
  intro ty
  cases ty with
  | data dataTy => cases dataTy <;> exact LS.SourceSymbolsRun.pure _
  | view _ _ => exact LS.SourceSymbolsRun.pure _

theorem LS.SourceSymbolsRun.regrowOf {le : LEnv} {scopeCount : Nat} :
    ∀ owner : Option ValueId, LS.SourceSymbolsRun le scopeCount (Goose.Lower.regrowOf owner)
  | none => by
    simp only [Goose.Lower.regrowOf]
    exact LS.SourceSymbolsRun.pure false
  | some address => by
    simp only [Goose.Lower.regrowOf]
    exact LS.SourceSymbolsRun.growOwner address

theorem LS.SourceSymbolsRun.eachSampled {le : LEnv} {scopeCount : Nat}
    (regrow : Bool) (view : ValueId) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.eachSampled regrow view) := by
  cases regrow with
  | false =>
    simp only [Goose.Lower.eachSampled, Bool.false_eq_true, ↓reduceIte]
    exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
  | true =>
    simp only [Goose.Lower.eachSampled, ↓reduceIte]
    exact LS.SourceSymbolsRun.pure 0

theorem LS.SourceSymbolsRun.eachLen {le : LEnv} {scopeCount : Nat}
    (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.eachLen regrow owner sampled) := by
  cases regrow with
  | false =>
    simp only [Goose.Lower.eachLen, Bool.false_eq_true, ↓reduceIte]
    exact LS.SourceSymbolsRun.pure sampled
  | true =>
    simp only [Goose.Lower.eachLen, ↓reduceIte]
    exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])

theorem LS.SourceSymbolsRun.eachElemValue {le : LEnv} {scopeCount : Nat}
    (slot : Core.VarId) (byRef : Bool) (element : ValueId) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.eachElemValue slot byRef element) := by
  unfold Goose.Lower.eachElemValue
  cases byRef with
  | false => exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
  | true =>
    apply LS.SourceSymbolsRun.bind (action := (read : B LEnv)) LS.SourceSymbolsRun.readAction
    intro env
    cases row : env.vars[slot]? with
    | none => simp only [row]; exact LS.SourceSymbolsRun.pure element
    | some localVar =>
      cases localVar with
      | mk name ty kind scope origin =>
        cases ty with
        | ref mutability _ => simp only [row]; exact LS.SourceSymbolsRun.freezeTo mutability element
        | _ => simp only [row]; exact LS.SourceSymbolsRun.pure element

theorem LS.SourceSymbolsRun.lowerEachSource {le : LEnv} {scopeCount : Nat}
    (placeSource : ∀ place, LS.SourceSymbolsRun le scopeCount (lowerPlace place))
    (exprSource : ∀ expr, LS.SourceSymbolsRun le scopeCount (lowerExpr expr)) :
    ∀ view : Core.View, LS.SourceSymbolsRun le scopeCount (Goose.Lower.lowerEachSource view)
  | .of place => by
    change LS.SourceSymbolsRun le scopeCount
      (lowerPlace place >>= fun address =>
        Goose.Lower.emitDef (.snapshot
          (match place with | .var _ | .global _ => .owner | _ => .borrowed) address) >>= fun view =>
        Pure.pure (some address, view))
    apply LS.SourceSymbolsRun.bind (action := lowerPlace place) (placeSource place)
    intro address
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitDef (.snapshot
      (match place with | .var _ | .global _ => .owner | _ => .borrowed) address))
    · exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    · intro view
      exact LS.SourceSymbolsRun.pure (some address, view)
  | .val expr => by
    change LS.SourceSymbolsRun le scopeCount
      (lowerExpr expr >>= fun sampled =>
        Goose.Lower.emitDef (.sliceView sampled) >>= fun view =>
        Pure.pure (none, view))
    apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) (exprSource expr)
    intro sampled
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitDef (.sliceView sampled))
    · exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    · intro view
      exact LS.SourceSymbolsRun.pure (none, view)

theorem LS.SourceSymbolsRun.patchBrs {le : LEnv} {scopeCount : Nat} (join : BlockId) :
    ∀ exits : List (BlockId × ValueId),
      LS.SourceSymbolsRun le scopeCount (Goose.Lower.patchBrs join exits)
  | [] => by
    simp only [Goose.Lower.patchBrs]
    exact LS.SourceSymbolsRun.pure ()
  | (block, value) :: rest => by
    simp only [Goose.Lower.patchBrs]
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.patchTerm block (.br join [value]))
    · exact LS.SourceSymbolsRun.patchTerm block (.br join [value]) (by
        intro origin equality
        simp [Term.origin] at equality)
    · intro _
      exact LS.SourceSymbolsRun.patchBrs join rest

theorem LS.SourceSymbolsRun.patchBrs0 {le : LEnv} {scopeCount : Nat} (join : BlockId) :
    ∀ exits : List BlockId,
      LS.SourceSymbolsRun le scopeCount (Goose.Lower.patchBrs0 join exits)
  | [] => by
    simp only [Goose.Lower.patchBrs0]
    exact LS.SourceSymbolsRun.pure ()
  | block :: rest => by
    simp only [Goose.Lower.patchBrs0]
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.patchTerm block (.br join []))
    · exact LS.SourceSymbolsRun.patchTerm block (.br join []) (by
        intro origin equality
        simp [Term.origin] at equality)
    · intro _
      exact LS.SourceSymbolsRun.patchBrs0 join rest

theorem LS.SourceSymbolsRun.joinValue {le : LEnv} {scopeCount : Nat}
    (thenEnd : Option BlockId) (thenValue : ValueId)
    (elseEnd : Option BlockId) (elseValue : ValueId) :
    LS.SourceSymbolsRun le scopeCount
      (Goose.Lower.joinValue thenEnd thenValue elseEnd elseValue) := by
  unfold Goose.Lower.joinValue
  cases thenEnd <;> cases elseEnd
  · simp only [Option.map_none, List.nil_append]
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.setCur none)
      (LS.SourceSymbolsRun.setCur none)
    intro _
    exact LS.SourceSymbolsRun.pure 0
  all_goals
    simp only [Option.map_some, List.cons_append, List.nil_append]
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.valTy _)
      (LS.SourceSymbolsRun.valTy _)
    intro ty
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.newBlock [ty])
      (LS.SourceSymbolsRun.newBlock [ty])
    intro joinState
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.patchBrs _ _)
      (LS.SourceSymbolsRun.patchBrs joinState.1 _)
    intro _
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.setCur (some joinState.1))
      (LS.SourceSymbolsRun.setCur (some joinState.1))
    intro _
    exact LS.SourceSymbolsRun.pure (joinState.2.headD 0)

theorem LS.SourceSymbolsRun.joinArms {le : LEnv} {scopeCount : Nat}
    (thenEnd elseEnd : Option BlockId) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.joinArms thenEnd elseEnd) := by
  unfold Goose.Lower.joinArms
  cases thenEnd <;> cases elseEnd
  · exact LS.SourceSymbolsRun.setCur none
  all_goals
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.newBlock [])
      (LS.SourceSymbolsRun.newBlock [])
    intro joinState
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.patchBrs0 _ _)
      (LS.SourceSymbolsRun.patchBrs0 joinState.1 _)
    intro _
    exact LS.SourceSymbolsRun.setCur (some joinState.1)

theorem LS.SourceSymbolsRun.loopBody {le : LEnv} {scopeCount : Nat} {condition : ValueId}
    {body : Nat → BlockId → B ValueId} {back : B Unit}
    (bodySource : ∀ depth exit, LS.SourceSymbolsRun le scopeCount (body depth exit))
    (backSource : LS.SourceSymbolsRun le scopeCount back) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.loopBody condition body back) := by
  unfold Goose.Lower.loopBody
  apply LS.SourceSymbolsRun.bind (action := (get : B LS)) LS.SourceSymbolsRun.getState
  intro state
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.fork condition)
    (LS.SourceSymbolsRun.fork condition)
  intro blocks
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.setCur (some blocks.1))
    (LS.SourceSymbolsRun.setCur (some blocks.1))
  intro _
  apply LS.SourceSymbolsRun.bind (action := body state.stack.length blocks.2)
    (bodySource state.stack.length blocks.2)
  intro _
  apply LS.SourceSymbolsRun.bind (action := back) backSource
  intro _
  exact LS.SourceSymbolsRun.setCur (some blocks.2)

theorem LS.SourceSymbolsRun.rangeBack {le : LEnv} {scopeCount : Nat}
    (intTy : Core.IntTy) (index : ValueId) (header : BlockId) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.rangeBack intTy index header) := by
  unfold Goose.Lower.rangeBack
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.isLive) LS.SourceSymbolsRun.isLive
  intro live
  cases live with
  | false => exact LS.SourceSymbolsRun.pure ()
  | true =>
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitDef (.next intTy index))
    · exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
    · intro next
      exact LS.SourceSymbolsRun.emitTerm (.br header [next]) (by
        intro origin equality
        simp [Term.origin] at equality)

theorem LS.SourceSymbolsRun.lowerWhile {le : LEnv} {scopeCount : Nat} (header : BlockId)
    {condition : B ValueId} {body : Nat → BlockId → B ValueId}
    (conditionSource : LS.SourceSymbolsRun le scopeCount condition)
    (bodySource : ∀ depth exit, LS.SourceSymbolsRun le scopeCount (body depth exit)) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.lowerWhile header condition body) := by
  unfold Goose.Lower.lowerWhile
  apply LS.SourceSymbolsRun.bind (action := condition) conditionSource
  intro value
  apply LS.SourceSymbolsRun.whenLive ()
  intro _
  exact LS.SourceSymbolsRun.loopBody bodySource
    (LS.SourceSymbolsRun.emitTerm (.br header []) (by
      intro origin equality
      simp [Term.origin] at equality))

theorem LS.SourceSymbolsRun.lowerRange {le : LEnv} {scopeCount : Nat}
    (intTy : Core.IntTy) (index bound : ValueId) (header : BlockId)
    {body : Nat → BlockId → B ValueId}
    (bodySource : ∀ depth exit, LS.SourceSymbolsRun le scopeCount (body depth exit)) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.lowerRange intTy index bound header body) := by
  unfold Goose.Lower.lowerRange
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitDef (.cmp .lt intTy index bound))
    (LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]))
  intro condition
  exact LS.SourceSymbolsRun.loopBody bodySource (LS.SourceSymbolsRun.rangeBack intTy index header)

theorem LS.SourceSymbolsRun.lowerEach {le : LEnv} {scopeCount : Nat}
    (regrow : Bool) (owner : Option ValueId) (sampled : ValueId) (header index : ValueId)
    {body : Nat → BlockId → B ValueId}
    (bodySource : ∀ depth exit, LS.SourceSymbolsRun le scopeCount (body depth exit)) :
    LS.SourceSymbolsRun le scopeCount
      (Goose.Lower.lowerEach regrow owner sampled header index body) := by
  unfold Goose.Lower.lowerEach
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.eachLen regrow owner sampled)
    (LS.SourceSymbolsRun.eachLen regrow owner sampled)
  intro bound
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitDef (.cmp .lt .i64 index bound))
    (LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid]))
  intro condition
  exact LS.SourceSymbolsRun.loopBody bodySource (LS.SourceSymbolsRun.rangeBack .i64 index header)

theorem LS.SourceSymbolsRun.ifValue {le : LEnv} {scopeCount : Nat}
    (condition : ValueId) {thenAction elseAction : B ValueId}
    (thenSource : LS.SourceSymbolsRun le scopeCount thenAction)
    (elseSource : LS.SourceSymbolsRun le scopeCount elseAction) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.whenLive 0 fun _ => do
      let (thenBlock, elseBlock) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some thenBlock)
      let thenValue ← thenAction
      let thenEnd ← Goose.Lower.curBlock
      Goose.Lower.setCur (some elseBlock)
      let elseValue ← elseAction
      let elseEnd ← Goose.Lower.curBlock
      Goose.Lower.joinValue thenEnd thenValue elseEnd elseValue) := by
  apply LS.SourceSymbolsRun.whenLive 0
  intro _
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.fork condition)
    (LS.SourceSymbolsRun.fork condition)
  intro blocks
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.setCur (some blocks.1))
    (LS.SourceSymbolsRun.setCur (some blocks.1))
  intro _
  apply LS.SourceSymbolsRun.bind (action := thenAction) thenSource
  intro thenValue
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.curBlock) LS.SourceSymbolsRun.curBlock
  intro thenEnd
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.setCur (some blocks.2))
    (LS.SourceSymbolsRun.setCur (some blocks.2))
  intro _
  apply LS.SourceSymbolsRun.bind (action := elseAction) elseSource
  intro elseValue
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.curBlock) LS.SourceSymbolsRun.curBlock
  intro elseEnd
  exact LS.SourceSymbolsRun.joinValue thenEnd thenValue elseEnd elseValue

theorem LS.SourceSymbolsRun.lowerBlockValue {le : LEnv} {scopeCount : Nat}
    (want : Bool) (value : Option Core.Expr)
    (exprSource : ∀ expr, value = some expr → LS.SourceSymbolsRun le scopeCount (lowerExpr expr)) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.lowerBlockValue want value) := by
  cases value with
  | some expr => exact exprSource expr rfl
  | none =>
    cases want with
    | false => exact LS.SourceSymbolsRun.pure 0
    | true => exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])

theorem LS.SourceSymbolsRun.inScope {le : LEnv} {scopeCount scope : Nat} {action : B α}
    (scopeBound : scope < scopeCount) (child : LS.SourceSymbolsRun le scopeCount action) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.inScope scope action) := by
  unfold Goose.Lower.inScope
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.pushScope scope)
    (LS.SourceSymbolsRun.pushScope scope scopeBound)
  intro _
  apply LS.SourceSymbolsRun.bind (action := action) child
  intro value
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.popScope) LS.SourceSymbolsRun.popScope
  intro _
  exact LS.SourceSymbolsRun.pure value

theorem LS.SourceSymbolsRun.lowerBlock {le : LEnv} {scopeCount : Nat}
    (scope : ScopeId) (pre : List (SlotId × ValueId × OriginId)) (want : Bool)
    (statements : List Core.Stmt) (value : Option Core.Expr) (loop : Option LoopCtx)
    (scopeBound : scope < scopeCount)
    (preBound : ∀ entry ∈ pre, entry.1 < le.slots.size ∧ entry.2.2 < le.mod.origins.size)
    (statementsSource : LS.SourceSymbolsRun le scopeCount (Goose.Lower.lowerStmts loop statements))
    (valueSource : LS.SourceSymbolsRun le scopeCount (Goose.Lower.lowerBlockValue want value)) :
    LS.SourceSymbolsRun le scopeCount
      (Goose.Lower.lowerBlock loop pre want (.mk scope statements value)) := by
  simp only [Goose.Lower.lowerBlock]
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitEffect (.enter scope))
  · exact LS.SourceSymbolsRun.emitEffect (.enter scope) (by simp [Effect.origin]) (by
      simpa [Effect.SymbolRefsValid] using scopeBound)
  · intro _
    apply LS.SourceSymbolsRun.inScope scopeBound
    change LS.SourceSymbolsRun le scopeCount
      (Goose.Lower.initSlots pre >>= fun _ =>
        Goose.Lower.lowerStmts loop statements >>= fun _ =>
        Goose.Lower.lowerBlockValue want value >>= fun result =>
        Goose.Lower.emitEffect (.leave scope) >>= fun _ => Pure.pure result)
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.initSlots pre)
      (LS.SourceSymbolsRun.initSlots pre preBound)
    intro _
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.lowerStmts loop statements) statementsSource
    intro _
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.lowerBlockValue want value) valueSource
    intro result
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitEffect (.leave scope))
    · exact LS.SourceSymbolsRun.emitEffect (.leave scope) (by simp [Effect.origin]) (by
        simpa [Effect.SymbolRefsValid] using scopeBound)
    · intro _
      exact LS.SourceSymbolsRun.pure result

theorem LS.SourceSymbolsRun.lowerStmts {le : LEnv} {scopeCount : Nat}
    (loop : Option LoopCtx) : ∀ statements : List Core.Stmt,
      (∀ stmt ∈ statements, LS.SourceSymbolsRun le scopeCount (lowerStmt loop stmt)) →
      LS.SourceSymbolsRun le scopeCount (Goose.Lower.lowerStmts loop statements)
  | [], _ => by
    simp only [Goose.Lower.lowerStmts]
    exact LS.SourceSymbolsRun.pure ()
  | stmt :: rest, children => by
    simp only [Goose.Lower.lowerStmts]
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.isLive) LS.SourceSymbolsRun.isLive
    intro live
    cases live with
    | false => exact LS.SourceSymbolsRun.pure ()
    | true =>
      apply LS.SourceSymbolsRun.bind (action := lowerStmt loop stmt) (children stmt (by simp))
      intro _
      exact LS.SourceSymbolsRun.lowerStmts loop rest
        (fun child member => children child (by simp [member]))

theorem LS.SourceSymbolsRun.lowerStmt_ifS_none {le : LEnv} {scopeCount : Nat}
    (condition : ValueId) (thenAction : B ValueId)
    (thenSource : LS.SourceSymbolsRun le scopeCount thenAction) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.whenLive () fun _ => do
      let (thenBlock, joinBlock) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some thenBlock)
      let _ ← thenAction
      Goose.Lower.emitTerm (.br joinBlock [])
      Goose.Lower.setCur (some joinBlock)) := by
  apply LS.SourceSymbolsRun.whenLive ()
  intro _
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.fork condition)
    (LS.SourceSymbolsRun.fork condition)
  intro blocks
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.setCur (some blocks.1))
    (LS.SourceSymbolsRun.setCur (some blocks.1))
  intro _
  apply LS.SourceSymbolsRun.bind (action := thenAction) thenSource
  intro _
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitTerm (.br blocks.2 []))
  · exact LS.SourceSymbolsRun.emitTerm (.br blocks.2 []) (by
      intro origin equality
      simp [Term.origin] at equality)
  · intro _
    exact LS.SourceSymbolsRun.setCur (some blocks.2)

theorem LS.SourceSymbolsRun.lowerStmt_ifS_some {le : LEnv} {scopeCount : Nat}
    (condition : ValueId) (thenAction elseAction : B ValueId)
    (thenSource : LS.SourceSymbolsRun le scopeCount thenAction)
    (elseSource : LS.SourceSymbolsRun le scopeCount elseAction) :
    LS.SourceSymbolsRun le scopeCount (Goose.Lower.whenLive () fun _ => do
      let (thenBlock, elseBlock) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some thenBlock)
      let _ ← thenAction
      let thenEnd ← Goose.Lower.curBlock
      Goose.Lower.setCur (some elseBlock)
      let _ ← elseAction
      let elseEnd ← Goose.Lower.curBlock
      Goose.Lower.joinArms thenEnd elseEnd) := by
  apply LS.SourceSymbolsRun.whenLive ()
  intro _
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.fork condition)
    (LS.SourceSymbolsRun.fork condition)
  intro blocks
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.setCur (some blocks.1))
    (LS.SourceSymbolsRun.setCur (some blocks.1))
  intro _
  apply LS.SourceSymbolsRun.bind (action := thenAction) thenSource
  intro _
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.curBlock) LS.SourceSymbolsRun.curBlock
  intro thenEnd
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.setCur (some blocks.2))
    (LS.SourceSymbolsRun.setCur (some blocks.2))
  intro _
  apply LS.SourceSymbolsRun.bind (action := elseAction) elseSource
  intro _
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.curBlock) LS.SourceSymbolsRun.curBlock
  intro elseEnd
  exact LS.SourceSymbolsRun.joinArms thenEnd elseEnd

theorem LS.SourceSymbolsRun.lowerStmt_ret_some {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    (expr : Core.Expr) (origin : Core.OriginId)
    (exprSource : LS.SourceSymbolsRun le scopeCount (lowerExpr expr))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.ret (some expr) origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr expr >>= fun value =>
      Goose.Lower.coerceResult value origin >>= fun result =>
      Goose.Lower.leaveTo 0 >>= fun _ =>
      Goose.Lower.emitTerm (.ret [result] (some origin)))
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) exprSource
  intro value
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.coerceResult value origin)
    (LS.SourceSymbolsRun.coerceResult value origin originBound)
  intro result
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.leaveTo 0)
    LS.SourceSymbolsRun.leaveTo
  intro _
  exact LS.SourceSymbolsRun.emitTerm (.ret [result] (some origin)) (by
    intro emitted equality
    simp only [Term.origin, Option.some.injEq] at equality
    cases equality
    exact originBound)

theorem LS.SourceSymbolsRun.lowerStmt_ret_none {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    (origin : Core.OriginId) (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.ret none origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (Pure.pure [] >>= fun values =>
      Goose.Lower.leaveTo 0 >>= fun _ =>
      Goose.Lower.emitTerm (.ret values (some origin)))
  apply LS.SourceSymbolsRun.bind (action := (Pure.pure [] : B (List ValueId)))
    (LS.SourceSymbolsRun.pure [])
  intro values
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.leaveTo 0)
    LS.SourceSymbolsRun.leaveTo
  intro _
  exact LS.SourceSymbolsRun.emitTerm (.ret values (some origin)) (by
    intro emitted equality
    simp only [Term.origin, Option.some.injEq] at equality
    cases equality
    exact originBound)

theorem LS.SourceSymbolsRun.lowerStmt_brk {le : LEnv} {scopeCount : Nat}
    (origin : Core.OriginId) (loop : Option LoopCtx)
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.brk origin)) := by
  cases loop with
  | none => exact LS.SourceSymbolsRun.pure ()
  | some context =>
    change LS.SourceSymbolsRun le scopeCount
      (Goose.Lower.leaveTo context.depth >>= fun _ =>
        Goose.Lower.emitTerm (.br context.breakTo []))
    apply LS.SourceSymbolsRun.bind (action := Goose.Lower.leaveTo context.depth)
      LS.SourceSymbolsRun.leaveTo
    intro _
    exact LS.SourceSymbolsRun.emitTerm (.br context.breakTo []) (by
      intro emitted equality
      simp [Term.origin] at equality)

theorem LS.SourceSymbolsRun.lowerStmt_cont {le : LEnv} {scopeCount : Nat}
    (origin : Core.OriginId) (loop : Option LoopCtx)
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.cont origin)) := by
  cases loop with
  | none => exact LS.SourceSymbolsRun.pure ()
  | some context =>
    cases context with
    | mk depth breakTo cont =>
      cases cont with
      | jump header =>
        simp only [lowerStmt]
        apply LS.SourceSymbolsRun.bind (action := Goose.Lower.leaveTo depth)
          LS.SourceSymbolsRun.leaveTo
        intro _
        exact LS.SourceSymbolsRun.emitTerm (.br header []) (by
          intro emitted equality
          simp [Term.origin] at equality)
      | next header intTy index =>
        simp only [lowerStmt]
        apply LS.SourceSymbolsRun.bind (action := Goose.Lower.leaveTo depth)
          LS.SourceSymbolsRun.leaveTo
        intro _
        apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitDef (.next intTy index))
        · exact LS.SourceSymbolsRun.emitDef_unreferenced (by simp [Op.origin]) (by simp [Op.SymbolRefsValid])
        · intro next
          exact LS.SourceSymbolsRun.emitTerm (.br header [next]) (by
            intro emitted equality
            simp [Term.origin] at equality)

theorem LS.SourceSymbolsRun.lowerStmt_assert {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    (expr : Core.Expr) (origin : Core.OriginId)
    (exprSource : LS.SourceSymbolsRun le scopeCount (lowerExpr expr))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.assertS expr origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr expr >>= fun condition => Goose.Lower.whenLive () fun _ => do
      let (passBlock, failBlock) ← Goose.Lower.fork condition
      Goose.Lower.setCur (some failBlock)
      Goose.Lower.emitTerm (.abort .assert (some origin))
      Goose.Lower.setCur (some passBlock))
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) exprSource
  intro condition
  apply LS.SourceSymbolsRun.whenLive ()
  intro _
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.fork condition)
    (LS.SourceSymbolsRun.fork condition)
  intro blocks
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.setCur (some blocks.2))
    (LS.SourceSymbolsRun.setCur (some blocks.2))
  intro _
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.emitTerm (.abort .assert (some origin)))
  · exact LS.SourceSymbolsRun.emitTerm (.abort .assert (some origin)) (by
      intro emitted equality
      simp only [Term.origin, Option.some.injEq] at equality
      cases equality
      exact originBound)
  · intro _
    exact LS.SourceSymbolsRun.setCur (some blocks.1)

theorem LS.SourceSymbolsRun.lowerStmt_exit {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    (expr : Core.Expr) (origin : Core.OriginId)
    (exprSource : LS.SourceSymbolsRun le scopeCount (lowerExpr expr))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.exit expr origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (lowerExpr expr >>= fun value => Goose.Lower.emitTerm (.exit value (some origin)))
  apply LS.SourceSymbolsRun.bind (action := lowerExpr expr) exprSource
  intro value
  exact LS.SourceSymbolsRun.emitTerm (.exit value (some origin)) (by
    intro emitted equality
    simp only [Term.origin, Option.some.injEq] at equality
    cases equality
    exact originBound)

theorem LS.SourceSymbolsRun.lowerStmt_abort {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    (message : String) (origin : Core.OriginId) (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.abort message origin)) := by
  change LS.SourceSymbolsRun le scopeCount (Goose.Lower.emitTerm (.abort .userAbort (some origin)))
  exact LS.SourceSymbolsRun.emitTerm (.abort .userAbort (some origin)) (by
    intro emitted equality
    simp only [Term.origin, Option.some.injEq] at equality
    cases equality
    exact originBound)

theorem LS.SourceSymbolsRun.lowerStmt_print {le : LEnv} {scopeCount : Nat} {loop : Option LoopCtx}
    (args : List Core.PrintArg) (origin : Core.OriginId)
    (argsSource : LS.SourceSymbolsRun le scopeCount (Goose.Lower.lowerPrintArgs args))
    (originBound : origin < le.mod.origins.size) :
    LS.SourceSymbolsRun le scopeCount (lowerStmt loop (.print args origin)) := by
  change LS.SourceSymbolsRun le scopeCount
    (Goose.Lower.lowerPrintArgs args >>= fun parts =>
      Goose.Lower.emitEffect (.print parts (some origin)))
  apply LS.SourceSymbolsRun.bind (action := Goose.Lower.lowerPrintArgs args) argsSource
  intro parts
  exact LS.SourceSymbolsRun.emitEffect (.print parts (some origin)) (by
    intro emitted equality
    simp only [Effect.origin, Option.some.injEq] at equality
    cases equality
    exact originBound) (by simp [Effect.SymbolRefsValid])

end Goose.Lower.Validation
