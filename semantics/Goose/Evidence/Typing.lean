import Goose.Evidence.MemoryTyping
import Goose.Evidence.Execution
import Goose.GIR.Step
import Goose.GIR.Typing

namespace Goose.Evidence

open Goose.Core Goose.GIR Goose.Proofs.Memory

abbrev ActivationTypes := ActId → Option Func

def runtimeDeclarations (cfg : GCfg) (activations : ActivationTypes) : RootDeclarations
  | .global id => cfg.mod.globals[id]?.map (·.ty)
  | .local act _ slot => (activations act).bind (fun fn => fn.slots[slot]?.map (·.ty))

def ActivationTypes.Before (activations : ActivationTypes) (next : ActId) : Prop :=
  ∀ act, next ≤ act → activations act = none

def ActivationTypes.enter (activations : ActivationTypes) (act : ActId) (fn : Func) : ActivationTypes :=
  fun other => if other = act then some fn else activations other

def RuntimeStateTy (cfg : GCfg) (activations : ActivationTypes) (state : St) : Prop :=
  activations.Before state.nextAct ∧ WeakStoreTy (runtimeDeclarations cfg activations) state.store

theorem runtimeDeclarations_enter_extends {cfg : GCfg} {activations : ActivationTypes}
    {act : ActId} {fn : Func} (fresh : activations act = none) :
    (runtimeDeclarations cfg activations).Extends
      (runtimeDeclarations cfg (activations.enter act fn)) := by
  intro root ty present
  cases root with
  | global id => exact present
  | «local» owner scope slot =>
    by_cases same : owner = act
    · subst owner
      simp [runtimeDeclarations, fresh] at present
    · simpa [runtimeDeclarations, ActivationTypes.enter, same] using present

theorem RuntimeStateTy.initial (cfg : GCfg) : RuntimeStateTy cfg (fun _ => none) St.initial := by
  constructor
  · intro act bound
    rfl
  · intro root value present
    simp [St.initial, Store.empty] at present

theorem RuntimeStateTy.freshAct {cfg : GCfg} {activations : ActivationTypes} {before after : St}
    {act : ActId} (typed : RuntimeStateTy cfg activations before) (fn : Func)
    (allocated : Goose.Core.freshAct before = .ok act after) :
    RuntimeStateTy cfg (activations.enter act fn) after ∧
      (activations.enter act fn) act = some fn ∧
      (runtimeDeclarations cfg activations).Extends
        (runtimeDeclarations cfg (activations.enter act fn)) := by
  simp only [Goose.Core.freshAct, Res.ok.injEq] at allocated
  obtain ⟨rfl, rfl⟩ := allocated
  have fresh := typed.1 before.nextAct (Nat.le_refl _)
  have extension := runtimeDeclarations_enter_extends (cfg := cfg) (fn := fn) fresh
  refine ⟨⟨?_, typed.2.mono extension⟩, ?_, extension⟩
  · intro other bound
    change before.nextAct + 1 ≤ other at bound
    have different : other ≠ before.nextAct := Nat.ne_of_gt (Nat.lt_of_succ_le bound)
    simp only [ActivationTypes.enter, different, ↓reduceIte]
    exact typed.1 other (Nat.le_trans (Nat.le_succ _) bound)
  · simp [ActivationTypes.enter]

def WeakViewTy (roots : RootDeclarations) (view : ViewVal) (element : Ty) : Prop :=
  (∃ count, DeclaredLocation roots view.loc (.arr element count)) ∨
  DeclaredLocation roots view.loc (.grow element) ∨
  DeclaredLocation roots view.loc (.growshrink element) ∨
  (∃ capacity, DeclaredLocation roots view.loc (.limited element capacity))

def WeakCellTy (roots : RootDeclarations) : RVal → VTy → Prop
  | .val value, .data ty => WeakValueTy roots value ty
  | .view view, .view _ element => WeakViewTy roots view element
  | _, _ => False

def WeakFrameTy (roots : RootDeclarations) (types : Array (Option VTy)) (fr : Frame) : Prop :=
  ∀ (id : ValueId) (cell : RVal) (ty : VTy), types[id]? = some (some ty) → fr.vals[id]? = some cell →
    WeakCellTy roots cell ty

def RuntimeFrameTy (cfg : GCfg) (fn : Func) (activations : ActivationTypes)
    (fr : Frame) (state : St) : Prop :=
  RuntimeStateTy cfg activations state ∧ activations fr.act = some fn ∧
    WeakFrameTy (runtimeDeclarations cfg activations) (fn.valueTypes cfg.mod) fr

theorem WeakFrameTy.empty (roots : RootDeclarations) (types : Array (Option VTy))
    (act depth : Nat) : WeakFrameTy roots types ⟨act, [], {}, depth⟩ := by
  intro id cell ty metadata present
  simp at present

theorem WeakFrameTy.ofVals {roots : RootDeclarations} {types : Array (Option VTy)}
    {before after : Frame} (typed : WeakFrameTy roots types before)
    (same : before.vals = after.vals) : WeakFrameTy roots types after := by
  intro id cell ty metadata present
  exact typed id cell ty metadata (same ▸ present)

theorem WeakCellTy.int {roots : RootDeclarations} {cell : RVal} {ty : IntTy}
    (typed : WeakCellTy roots cell (.data (.int ty))) :
    ∃ n, cell = .val (.int ty n) := by
  cases cell with
  | val value =>
    obtain ⟨n, rfl⟩ := WeakValueTy.int (roots := roots) typed
    exact ⟨n, rfl⟩
  | view view => exact False.elim typed

theorem WeakFrameTy.int {roots : RootDeclarations} {types : Array (Option VTy)}
    {fr : Frame} {id : ValueId} {ty : IntTy} {cell : RVal}
    (typed : WeakFrameTy roots types fr) (metadata : types[id]? = some (some (.data (.int ty))))
    (present : fr.vals[id]? = some cell) :
    ∃ n, fr.vals[id]? = some (.val (.int ty n)) := by
  obtain ⟨n, same⟩ := (typed id cell _ metadata present).int
  exact ⟨n, same ▸ present⟩

theorem WeakFrameTy.set {roots : RootDeclarations} {types : Array (Option VTy)}
    {fr : Frame} {id : ValueId} {cell : RVal} {ty : VTy}
    (typed : WeakFrameTy roots types fr) (metadata : types[id]? = some (some ty))
    (valueTyped : WeakCellTy roots cell ty) : WeakFrameTy roots types (fr.set id cell) := by
  intro other value otherTy otherMetadata present
  simp only [Frame.set, Std.HashMap.getElem?_insert] at present
  split at present
  · rename_i same
    have sameId : id = other := eq_of_beq same
    subst other
    cases present
    have sameTy : otherTy = ty := Option.some.inj (Option.some.inj
      (otherMetadata.symm.trans metadata))
    subst otherTy
    exact valueTyped
  · exact typed other value otherTy otherMetadata present

theorem WeakFrameTy.getVal {roots : RootDeclarations} {types : Array (Option VTy)}
    {fr : Frame} {id : ValueId} {ty : Ty} {value : Val} {before after : St}
    (typed : WeakFrameTy roots types fr) (metadata : types[id]? = some (some (.data ty)))
    (read : getVal fr id before = .ok value after) :
    WeakValueTy roots value ty ∧ after = before := by
  unfold Goose.GIR.getVal getCell at read
  cases present : fr.vals[id]? with
  | none => simp [present, bind_apply, fault, M.stop] at read
  | some cell =>
    cases cell with
    | view view => simp [present, bind_apply, pure_apply, fault, M.stop] at read
    | val found =>
      simp only [present, bind_apply, pure_apply, Res.ok.injEq] at read
      obtain ⟨rfl, rfl⟩ := read
      exact ⟨typed id (.val found) (.data ty) metadata present, rfl⟩

theorem WeakFrameTy.getView {roots : RootDeclarations} {types : Array (Option VTy)}
    {fr : Frame} {id : ValueId} {permission : Mutability} {element : Ty} {view : ViewVal}
    {before after : St} (typed : WeakFrameTy roots types fr)
    (metadata : types[id]? = some (some (.view permission element)))
    (read : Goose.GIR.getView fr id before = .ok view after) :
    WeakViewTy roots view element ∧ after = before := by
  unfold Goose.GIR.getView at read
  obtain ⟨cell, middle, lookup, read⟩ := m_bind_ok read
  obtain ⟨present, sameState⟩ := getCell_success lookup
  subst middle
  cases cell with
  | val value => simp [fault, M.stop] at read
  | view found =>
    simp only [pure_apply, Res.ok.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    exact ⟨typed id (.view found) _ metadata present, rfl⟩

theorem WeakFrameTy.getVals {roots : RootDeclarations} {types : Array (Option VTy)}
    {fr : Frame} {ids : List ValueId} {ty : Ty} {values : List Val} {before after : St}
    (typed : WeakFrameTy roots types fr)
    (metadata : ∀ id ∈ ids, types[id]? = some (some (.data ty)))
    (read : mapList (Goose.GIR.getVal fr) ids before = .ok values after) :
    (∀ value ∈ values, WeakValueTy roots value ty) ∧ values.length = ids.length ∧ after = before := by
  induction ids generalizing values before after with
  | nil =>
    simp only [mapList, pure_apply, Res.ok.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    exact ⟨by simp, rfl, rfl⟩
  | cons id ids ih =>
    simp only [mapList] at read
    obtain ⟨value, middle, found, read⟩ := m_bind_ok read
    obtain ⟨headTyped, sameState⟩ := typed.getVal (metadata id (by simp)) found
    subst middle
    obtain ⟨tail, middle, foundTail, read⟩ := m_bind_ok read
    obtain ⟨tailTyped, size, sameState⟩ := ih
      (fun other present => metadata other (List.mem_cons_of_mem _ present)) foundTail
    subst middle
    simp only [pure_apply, Res.ok.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    refine ⟨?_, by simp [size], rfl⟩
    intro other present
    rcases List.mem_cons.mp present with rfl | present
    · exact headTyped
    · exact tailTyped other present

inductive FlatOperands (types : Array (Option VTy)) : List ValueId → TyList → Prop
  | nil : FlatOperands types [] .nil
  | cons {id ty ids rest}
      (metadata : types[id]? = some (some (.data ty))) (flat : ty.flat = true)
      (tail : FlatOperands types ids rest) : FlatOperands types (id :: ids) (.cons ty rest)

theorem WeakFrameTy.getFields {roots : RootDeclarations} {types : Array (Option VTy)}
    {fr : Frame} {ids : List ValueId} {fields : TyList} {values : List Val} {before after : St}
    (typed : WeakFrameTy roots types fr) (operands : FlatOperands types ids fields)
    (read : mapList (Goose.GIR.getVal fr) ids before = .ok values after) :
    FieldsTy fields values ∧ after = before := by
  induction operands generalizing values before after with
  | nil =>
    simp only [mapList, pure_apply, Res.ok.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    exact ⟨True.intro, rfl⟩
  | cons metadata flat tail ih =>
    simp only [mapList] at read
    obtain ⟨value, middle, found, read⟩ := m_bind_ok read
    obtain ⟨headTyped, sameState⟩ := typed.getVal metadata found
    subst middle
    obtain ⟨tail, middle, foundTail, read⟩ := m_bind_ok read
    obtain ⟨tailTyped, sameState⟩ := ih foundTail
    subst middle
    simp only [pure_apply, Res.ok.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    exact ⟨⟨headTyped.flat flat, tailTyped⟩, rfl⟩

theorem WeakViewTy.mono {before after : RootDeclarations} {view : ViewVal} {element : Ty}
    (extension : before.Extends after) (typed : WeakViewTy before view element) :
    WeakViewTy after view element := by
  rcases typed with ⟨count, declared⟩ | declared | declared | ⟨capacity, declared⟩
  · exact Or.inl ⟨count, declared.mono extension⟩
  · exact Or.inr (Or.inl (declared.mono extension))
  · exact Or.inr (Or.inr (Or.inl (declared.mono extension)))
  · exact Or.inr (Or.inr (Or.inr ⟨capacity, declared.mono extension⟩))

theorem WeakViewTy.element {roots : RootDeclarations} {view : ViewVal} {element : Ty}
    (typed : WeakViewTy roots view element) (index : Nat) :
    DeclaredLocation roots ⟨view.loc.root, view.loc.path ++ [view.start + index]⟩ element := by
  rcases typed with ⟨count, declared⟩ | declared | declared | ⟨capacity, declared⟩
  · exact declared.append (.fixed (.root element))
  · exact declared.append (.grow (.root element))
  · exact declared.append (.shrink (.root element))
  · exact declared.append (.limited (.root element))

theorem WeakValueTy.arrayElements {roots : RootDeclarations} {value : Val} {ty element : Ty}
    (typed : WeakValueTy roots value ty) (arrayType : arrayElem? ty = some element) :
    ∃ values, value.elems? = some values ∧
      ∀ (i : Nat) (child : Val), values[i]? = some child → WeakValueTy roots child element := by
  cases ty <;> simp only [arrayElem?] at arrayType <;> try contradiction
  all_goals simp only [Option.some.injEq] at arrayType; subst element
  all_goals cases value <;> simp only [WeakValueTy] at typed <;> try contradiction
  case arr.fixed => exact ⟨_, rfl, typed.2⟩
  case grow.resizable => exact ⟨_, rfl, typed.2⟩
  case growshrink.resizable => exact ⟨_, rfl, typed.2⟩
  case limited.limited => exact ⟨_, rfl, typed.2.2.2.2⟩


theorem WeakCellTy.mono {before after : RootDeclarations} {cell : RVal} {ty : VTy}
    (extension : before.Extends after) (typed : WeakCellTy before cell ty) :
    WeakCellTy after cell ty := by
  cases cell <;> cases ty
  · exact WeakValueTy.mono extension typed
  · exact typed
  · exact typed
  · exact WeakViewTy.mono extension typed

theorem WeakFrameTy.mono {before after : RootDeclarations} {types : Array (Option VTy)}
    {fr : Frame} (extension : before.Extends after) (typed : WeakFrameTy before types fr) :
    WeakFrameTy after types fr := by
  intro id cell ty metadata present
  exact (typed id cell ty metadata present).mono extension

theorem execPure_slotAddr_typed {activations : ActivationTypes} {cx : FnCtx} {fr : Frame}
    {id : SlotId} {slot : Slot} {before after : St} {cell : RVal}
    (current : activations fr.act = some cx.fn) (lookup : cx.fn.slots[id]? = some slot)
    (evaluated : execPure cx fr (.slotAddr id) before = .ok cell after)
    (permission : Mutability) :
    WeakCellTy (runtimeDeclarations cx.cfg activations) cell (.data (.ref permission slot.ty)) ∧
      after = before := by
  simp only [execPure, slotRoot, lookup] at evaluated
  cases scope : fr.scopes.lookup slot.scope with
  | none => simp [scope, bind_apply, fault, M.stop] at evaluated
  | some scopeInstance =>
    simp only [scope, pure_bind, pure_apply, Res.ok.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    refine ⟨⟨_, rfl, slot.ty, ?_, .root slot.ty⟩, rfl⟩
    simp [runtimeDeclarations, current, lookup]

theorem execPure_globalAddr_typed {activations : ActivationTypes} {cx : FnCtx} {fr : Frame}
    {id : GlobalId} {global : GIR.Global} {before after : St} {cell : RVal}
    (lookup : cx.cfg.mod.globals[id]? = some global)
    (evaluated : execPure cx fr (.globalAddr id) before = .ok cell after)
    (permission : Mutability) :
    WeakCellTy (runtimeDeclarations cx.cfg activations) cell (.data (.ref permission global.ty)) ∧
      after = before := by
  simp only [execPure, pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  refine ⟨⟨_, rfl, global.ty, ?_, .root global.ty⟩, rfl⟩
  simp [runtimeDeclarations, lookup]

theorem execPure_next_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {id : ValueId} {ty : IntTy} {before after : St} {cell : RVal}
    (frameTyped : WeakFrameTy roots types fr)
    (metadata : types[id]? = some (some (.data (.int ty))))
    (evaluated : execPure cx fr (.next ty id) before = .ok cell after) :
    WeakCellTy roots cell (.data (.int ty)) ∧ after = before := by
  unfold execPure at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.getVal metadata read
  subst middle
  obtain ⟨n, rfl⟩ := valueTyped.int
  simp only [expectInt, pure_bind, pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  exact ⟨rfl, rfl⟩

theorem execPure_un_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {id : ValueId} {ty : IntTy} {operation : UnOp}
    {org : Option OriginId} {before after : St} {cell : RVal}
    (frameTyped : WeakFrameTy roots types fr)
    (metadata : types[id]? = some (some (.data (.int ty))))
    (evaluated : execPure cx fr (.un operation ty id org) before = .ok cell after) :
    WeakCellTy roots cell (.data (.int ty)) ∧ after = before := by
  unfold execPure at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.getVal metadata read
  subst middle
  obtain ⟨n, rfl⟩ := valueTyped.int
  simp only [expectInt, pure_bind] at evaluated
  cases result : evalUn cx.cfg.profile operation ty n with
  | error abort =>
    cases org <;> simp [result, abortAtOrg, abortAt, fault, M.stop] at evaluated
  | ok n' =>
    simp only [result, pure_apply, Res.ok.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    exact ⟨rfl, rfl⟩

theorem execPure_bin_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {left right : ValueId} {ty : IntTy} {operation : BinOp}
    {org : Option OriginId} {before after : St} {cell : RVal}
    (frameTyped : WeakFrameTy roots types fr)
    (leftMetadata : types[left]? = some (some (.data (.int ty))))
    (rightMetadata : types[right]? = some (some (.data (.int ty))))
    (evaluated : execPure cx fr (.bin operation ty left right org) before = .ok cell after) :
    WeakCellTy roots cell (.data (.int ty)) ∧ after = before := by
  unfold execPure at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.getVal leftMetadata read
  subst middle
  obtain ⟨n, rfl⟩ := valueTyped.int
  simp only [expectInt, pure_bind] at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.getVal rightMetadata read
  subst middle
  obtain ⟨m, rfl⟩ := valueTyped.int
  simp only [pure_bind, expectSameTy, ↓reduceIte] at evaluated
  cases result : evalBin cx.cfg.profile operation ty n m with
  | error abort =>
    cases org <;> simp [result, abortAtOrg, abortAt, fault, M.stop] at evaluated
  | ok n' =>
    simp only [result, pure_apply, Res.ok.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    exact ⟨rfl, rfl⟩

theorem execPure_conv_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {id : ValueId} {source target : IntTy} {conversion : ConvKind}
    {org : Option OriginId} {before after : St} {cell : RVal}
    (frameTyped : WeakFrameTy roots types fr)
    (metadata : types[id]? = some (some (.data (.int source))))
    (evaluated : execPure cx fr (.conv conversion source target id org) before = .ok cell after) :
    WeakCellTy roots cell (.data (.int target)) ∧ after = before := by
  unfold execPure at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.getVal metadata read
  subst middle
  obtain ⟨n, rfl⟩ := valueTyped.int
  simp only [expectInt, pure_bind] at evaluated
  cases result : evalConv cx.cfg.profile conversion source target n with
  | error abort =>
    cases org <;> simp [result, abortAtOrg, abortAt, fault, M.stop] at evaluated
  | ok n' =>
    simp only [result, pure_apply, Res.ok.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    exact ⟨rfl, rfl⟩

theorem execPure_boolNot_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {id : ValueId} {before after : St} {cell : RVal}
    (frameTyped : WeakFrameTy roots types fr)
    (metadata : types[id]? = some (some (.data .bool)))
    (evaluated : execPure cx fr (.boolNot id) before = .ok cell after) :
    WeakCellTy roots cell (.data .bool) ∧ after = before := by
  unfold execPure at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.getVal metadata read
  subst middle
  obtain ⟨b, rfl⟩ := valueTyped.bool
  simp only [expectBool, pure_bind, pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  exact ⟨True.intro, rfl⟩

theorem expectComparable_state {left right : Val} {before after : St} {pair : Int × Int}
    (compared : expectComparable left right before = .ok pair after) : after = before := by
  cases left <;> cases right <;> simp only [expectComparable] at compared
  all_goals try (simp [fault, M.stop] at compared)
  all_goals try (simp only [pure_apply, Res.ok.injEq] at compared; exact compared.2.symm)
  rw [← bind_pure_comp] at compared
  unfold expectSameTy at compared
  split at compared
  · simp only [pure_bind, pure_apply, Res.ok.injEq] at compared
    exact compared.2.symm
  · simp [bind_apply, fault, M.stop] at compared

theorem execPure_cmp_typed {roots : RootDeclarations} {cx : FnCtx} {fr : Frame}
    {left right : ValueId} {ty : IntTy} {comparison : CmpOp} {before after : St} {cell : RVal}
    (evaluated : execPure cx fr (.cmp comparison ty left right) before = .ok cell after) :
    WeakCellTy roots cell (.data .bool) ∧ after = before := by
  unfold execPure at evaluated
  obtain ⟨leftValue, middle, read, evaluated⟩ := m_bind_ok evaluated
  have sameState := (getVal_success read).2
  subst middle
  obtain ⟨rightValue, middle, read, evaluated⟩ := m_bind_ok evaluated
  have sameState := (getVal_success read).2
  subst middle
  obtain ⟨pair, middle, compared, evaluated⟩ := m_bind_ok evaluated
  have sameState := expectComparable_state compared
  subst middle
  simp only [pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  exact ⟨True.intro, rfl⟩

theorem expectRef_state {value : Val} {before after : St} {location : Loc}
    (read : expectRef value before = .ok location after) : after = before := by
  cases value <;> simp [expectRef, fault, M.stop, pure_apply] at read
  exact read.2.symm

theorem expectBool_state {value : Val} {before after : St} {result : Bool}
    (read : expectBool value before = .ok result after) : after = before := by
  cases value <;> simp [expectBool, fault, M.stop, pure_apply] at read
  exact read.2.symm

theorem condition_state {fr : Frame} {id : ValueId} {before after : St} {result : Bool}
    (tested : (getVal fr id >>= expectBool) before = .ok result after) : after = before := by
  obtain ⟨value, middle, read, tested⟩ := m_bind_ok tested
  have sameState := (getVal_success read).2
  subst middle
  exact expectBool_state tested

theorem expectArray_state {value : Val} {before after : St} {shape : Nat × Bool}
    (read : expectArray value before = .ok shape after) : after = before := by
  cases value <;> simp [expectArray, fault, M.stop, pure_apply] at read
  all_goals exact read.2.symm

theorem readLoc_state {before after : St} {location : Loc} {value : Val}
    (read : Goose.Core.readLoc location before = .ok value after) : after = before := by
  unfold Goose.Core.readLoc at read
  cases stored : before.store.read location <;> simp [stored] at read
  exact read.2.symm

theorem lengthLoc_state {before after : St} {location : Loc} {len : Nat}
    (read : lengthLoc location before = .ok len after) : after = before := by
  unfold lengthLoc at read
  cases stored : before.store.length location <;> simp [stored] at read
  exact read.2.symm

theorem getView_state {fr : Frame} {id : ValueId} {before after : St} {view : ViewVal}
    (read : Goose.GIR.getView fr id before = .ok view after) : after = before := by
  unfold Goose.GIR.getView at read
  obtain ⟨cell, middle, lookup, read⟩ := m_bind_ok read
  have sameState := (getCell_success lookup).2
  subst middle
  cases cell <;> simp [fault, M.stop, pure_apply] at read
  exact read.2.symm

theorem WeakViewTy.readRun {roots : RootDeclarations} {view : ViewVal} {element : Ty}
    {before after : St} {values : Array Val} (viewTyped : WeakViewTy roots view element)
    (storeTyped : WeakStoreTy roots before.store)
    (evaluated : Goose.Core.readRun view before = .ok values after) :
    (∀ (i : Nat) (value : Val), values[i]? = some value → WeakValueTy roots value element) ∧
      after = before := by
  unfold Goose.Core.readRun at evaluated
  obtain ⟨old, middle, read, evaluated⟩ := m_bind_ok evaluated
  have sameState := readLoc_state read
  subst middle
  have children : ∃ elements, old.elems? = some elements ∧
      ∀ (i : Nat) (child : Val), elements[i]? = some child → WeakValueTy roots child element := by
    rcases viewTyped with ⟨count, declared⟩ | declared | declared | ⟨capacity, declared⟩
    all_goals exact ((storeTyped.readLoc declared read).1).arrayElements rfl
  obtain ⟨elements, shape, elementsTyped⟩ := children
  cases old <;> simp only [Val.elems?] at shape <;> try contradiction
  all_goals simp only [Option.some.injEq] at shape; subst elements
  all_goals simp only at evaluated
  all_goals split at evaluated
  all_goals first
    | (simp [fault, M.stop] at evaluated; done)
    | (simp only [pure_apply, Res.ok.injEq] at evaluated
       obtain ⟨rfl, rfl⟩ := evaluated
       exact ⟨elements_extract elementsTyped _ _, rfl⟩)


theorem checkCapacityAtOrg_state {location : Loc} {count : Nat} {org : Option OriginId}
    {before after : St} {result : Unit}
    (checked : checkCapacityAtOrg location count org before = .ok result after) : after = before := by
  unfold checkCapacityAtOrg at checked
  obtain ⟨value, middle, read, checked⟩ := m_bind_ok checked
  have sameState := readLoc_state read
  subst middle
  cases value <;> simp only at checked
  all_goals first
    | (simp [fault, M.stop] at checked; done)
    | (simp only [pure_apply, Res.ok.injEq] at checked; exact checked.2.symm)
    | (split at checked
       · cases org <;> simp [abortAtOrg, abortAt, fault, M.stop] at checked
       · simp only [pure_apply, Res.ok.injEq] at checked
         exact checked.2.symm)

theorem execPure_viewLen_typed {roots : RootDeclarations} {cx : FnCtx} {fr : Frame}
    {id : ValueId} {before after : St} {cell : RVal}
    (evaluated : execPure cx fr (.viewLen id) before = .ok cell after) :
    WeakCellTy roots cell (.data (.int .i64)) ∧ after = before := by
  unfold execPure at evaluated
  obtain ⟨view, middle, read, evaluated⟩ := m_bind_ok evaluated
  have sameState := getView_state read
  subst middle
  simp only [pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  exact ⟨rfl, rfl⟩

theorem execPure_arrayLen_typed {roots : RootDeclarations} {cx : FnCtx} {fr : Frame}
    {id : ValueId} {before after : St} {cell : RVal}
    (evaluated : execPure cx fr (.arrayLen id) before = .ok cell after) :
    WeakCellTy roots cell (.data (.int .i64)) ∧ after = before := by
  unfold execPure at evaluated
  obtain ⟨reference, middle, read, evaluated⟩ := m_bind_ok evaluated
  have sameState := (getVal_success read).2
  subst middle
  obtain ⟨location, middle, read, evaluated⟩ := m_bind_ok evaluated
  have sameState := expectRef_state read
  subst middle
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  have sameState := readLoc_state read
  subst middle
  obtain ⟨shape, middle, read, evaluated⟩ := m_bind_ok evaluated
  have sameState := expectArray_state read
  subst middle
  simp only [pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  exact ⟨rfl, rfl⟩

theorem execPure_boolCmp_typed {roots : RootDeclarations} {cx : FnCtx} {fr : Frame}
    {left right : ValueId} {comparison : CmpOp} {before after : St} {cell : RVal}
    (evaluated : execPure cx fr (.boolCmp comparison left right) before = .ok cell after) :
    WeakCellTy roots cell (.data .bool) ∧ after = before :=
  execPure_cmp_typed (cx := cx) (ty := .i64) evaluated

theorem execPure_constInt_typed {roots : RootDeclarations} {cx : FnCtx} {fr : Frame}
    {ty : IntTy} {n : Int} {before after : St} {cell : RVal}
    (evaluated : execPure cx fr (.constInt ty n) before = .ok cell after) :
    WeakCellTy roots cell (.data (.int ty)) ∧ after = before := by
  simp only [execPure, pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  exact ⟨rfl, rfl⟩

theorem execPure_constBool_typed {roots : RootDeclarations} {cx : FnCtx} {fr : Frame}
    {b : Bool} {before after : St} {cell : RVal}
    (evaluated : execPure cx fr (.constBool b) before = .ok cell after) :
    WeakCellTy roots cell (.data .bool) ∧ after = before := by
  simp only [execPure, pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  exact ⟨True.intro, rfl⟩

theorem execPure_constUnit_typed {roots : RootDeclarations} {cx : FnCtx} {fr : Frame}
    {before after : St} {cell : RVal}
    (evaluated : execPure cx fr .constUnit before = .ok cell after) :
    WeakCellTy roots cell (.data .unit) ∧ after = before := by
  simp only [execPure, pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  exact ⟨rfl, rfl⟩

theorem execPure_refFreeze_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {id : ValueId} {permission : Mutability} {ty : Ty}
    {before after : St} {cell : RVal} (frameTyped : WeakFrameTy roots types fr)
    (metadata : types[id]? = some (some (.data (.ref permission ty))))
    (evaluated : execPure cx fr (.refFreeze id) before = .ok cell after) :
    WeakCellTy roots cell (.data (.ref .readOnly ty)) ∧ after = before := by
  unfold execPure at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.getVal metadata read
  subst middle
  obtain ⟨location, rfl, declared⟩ := valueTyped
  simp only [expectRef, pure_bind, pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  exact ⟨⟨location, rfl, declared⟩, rfl⟩

theorem execPure_fieldAddr_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {id : ValueId} {permission fieldPermission : Mutability}
    {sid : StructId} {fields : TyList} {index : Nat} {fieldTy : Ty}
    {before after : St} {cell : RVal} (frameTyped : WeakFrameTy roots types fr)
    (metadata : types[id]? = some (some (.data (.ref permission (.structT sid fields)))))
    (selector : fields.toList[index]? = some fieldTy)
    (evaluated : execPure cx fr (.fieldAddr id index) before = .ok cell after) :
    WeakCellTy roots cell (.data (.ref fieldPermission fieldTy)) ∧ after = before := by
  unfold execPure at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.getVal metadata read
  subst middle
  obtain ⟨location, rfl, declared⟩ := valueTyped
  simp only [expectRef, pure_bind, pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  exact ⟨⟨_, rfl, declared.append (.field selector (.root fieldTy))⟩, rfl⟩

theorem execPure_arrFill_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {id : ValueId} {element : Ty} {count : Nat}
    {before after : St} {cell : RVal} (frameTyped : WeakFrameTy roots types fr)
    (metadata : types[id]? = some (some (.data element)))
    (evaluated : execPure cx fr (.arrFill (.arr element count) id) before = .ok cell after) :
    WeakCellTy roots cell (.data (.arr element count)) ∧ after = before := by
  simp only [execPure, expectFixedCount, pure_bind] at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.getVal metadata read
  subst middle
  simp only [pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  refine ⟨⟨by simp, ?_⟩, rfl⟩
  intro index selected present
  rw [Array.getElem?_replicate] at present
  split at present
  · cases present
    exact valueTyped
  · contradiction

theorem execPure_indexProven_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {viewId indexId : ValueId} {permission : Mutability}
    {element : Ty} {indexTy : IntTy} {before after : St} {cell : RVal}
    (frameTyped : WeakFrameTy roots types fr)
    (viewMetadata : types[viewId]? = some (some (.view permission element)))
    (indexMetadata : types[indexId]? = some (some (.data (.int indexTy))))
    (evaluated : execPure cx fr (.indexProven viewId indexId) before = .ok cell after) :
    WeakCellTy roots cell (.data (.ref permission element)) ∧ after = before := by
  unfold execPure at evaluated
  obtain ⟨view, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨viewTyped, sameState⟩ := frameTyped.getView viewMetadata read
  subst middle
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.getVal indexMetadata read
  subst middle
  obtain ⟨index, rfl⟩ := valueTyped.int
  simp only [expectInt, pure_bind, pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  exact ⟨⟨_, rfl, viewTyped.element index.toNat⟩, rfl⟩

theorem execPure_arrLit_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {ids : List ValueId} {ty element : Ty}
    {before after : St} {cell : RVal} (frameTyped : WeakFrameTy roots types fr)
    (metadata : ∀ id ∈ ids, types[id]? = some (some (.data element)))
    (arrayType : arrayElem? ty = some element)
    (fixedCount : ∀ e count, ty = .arr e count → ids.length = count)
    (evaluated : execPure cx fr (.arrLit ty ids) before = .ok cell after) :
    WeakCellTy roots cell (.data ty) ∧ after = before := by
  unfold execPure at evaluated
  obtain ⟨values, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valuesTyped, size, sameState⟩ := frameTyped.getVals metadata read
  subst middle
  have elementsTyped : ∀ (i : Nat) (value : Val), values.toArray[i]? = some value → WeakValueTy roots value element := by
    intro i value present
    have member : value ∈ values := by simpa using Array.mem_of_getElem? present
    exact valuesTyped value member
  cases ty with
  | arr e count =>
    simp only [arrayElem?, Option.some.injEq] at arrayType
    subst e
    simp only [expectArrayLit, pure_bind, pure_apply, Res.ok.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    exact ⟨⟨by simp [size, fixedCount element count rfl], elementsTyped⟩, rfl⟩
  | grow e | growshrink e =>
    simp only [arrayElem?, Option.some.injEq] at arrayType
    subst e
    simp only [expectArrayLit, pure_bind, pure_apply, Res.ok.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    exact ⟨⟨rfl, elementsTyped⟩, rfl⟩
  | limited e capacity =>
    simp only [arrayElem?, Option.some.injEq] at arrayType
    subst e
    simp only [expectArrayLit] at evaluated
    split at evaluated
    · rename_i capacityBound
      simp only [pure_bind, pure_apply, Res.ok.injEq] at evaluated
      obtain ⟨rfl, rfl⟩ := evaluated
      exact ⟨⟨rfl, rfl, capacityBound, Nat.le_refl _, elementsTyped⟩, rfl⟩
    · simp [bind_apply, fault, M.stop] at evaluated
  | _ => simp [arrayElem?] at arrayType

theorem execPure_structLit_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {ids : List ValueId} {sid : StructId} {fields : TyList}
    {before after : St} {cell : RVal} (frameTyped : WeakFrameTy roots types fr)
    (operands : FlatOperands types ids fields)
    (evaluated : execPure cx fr (.structLit (.structT sid fields) ids) before = .ok cell after) :
    WeakCellTy roots cell (.data (.structT sid fields)) ∧ after = before := by
  simp only [execPure] at evaluated
  obtain ⟨values, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨fieldsTyped, sameState⟩ := frameTyped.getFields operands read
  subst middle
  simp only [pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  exact ⟨⟨rfl, by simpa using WeakFieldsTy.ofFlat (roots := roots) fieldsTyped⟩, rfl⟩

theorem pushAppend_typed {cfg : GCfg} {activations : ActivationTypes}
    {location : Loc} {value : Val} {owner element : Ty} {before after : St} {cell : RVal}
    (stateTyped : RuntimeStateTy cfg activations before)
    (target : DeclaredLocation (runtimeDeclarations cfg activations) location owner)
    (ownerType : owner.ownerElem? = some element)
    (valueTyped : WeakValueTy (runtimeDeclarations cfg activations) value element)
    (evaluated : (appendLoc location #[value] >>= fun index =>
      pure (RVal.val (.ref { location with path := location.path ++ [index] }))) before = .ok cell after) :
    WeakCellTy (runtimeDeclarations cfg activations) cell (.data (.ref .mutable element)) ∧
      RuntimeStateTy cfg activations after := by
  obtain ⟨index, middle, appended, evaluated⟩ := m_bind_ok evaluated
  simp only [pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  unfold appendLoc at appended
  cases changed : before.store.append location #[value] with
  | error fault => simp [changed] at appended
  | ok result =>
    obtain ⟨store, start⟩ := result
    simp only [changed, Res.ok.injEq] at appended
    obtain ⟨rfl, sameState⟩ := appended
    subst middle
    refine ⟨⟨_, rfl, target.ownerElement ownerType start⟩,
      stateTyped.1, stateTyped.2.appendOwner target ownerType ?_ changed⟩
    intro index selected present
    simp only [Array.getElem?_singleton] at present
    split at present
    · cases present
      exact valueTyped
    · contradiction

theorem execPure_push_typed {cfg : GCfg} {activations : ActivationTypes} {fn : Func}
    {fr : Frame} {targetId valueId : ValueId} {permission : Mutability} {owner element : Ty}
    {org : Option OriginId} {before after : St} {cell : RVal}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (targetMetadata : (fn.valueTypes cfg.mod)[targetId]? = some (some (.data (.ref permission owner))))
    (valueMetadata : (fn.valueTypes cfg.mod)[valueId]? = some (some (.data element)))
    (ownerType : owner.ownerElem? = some element)
    (evaluated : execPure ⟨cfg, fn⟩ fr (.push targetId valueId org) before = .ok cell after) :
    WeakCellTy (runtimeDeclarations cfg activations) cell (.data (.ref .mutable element)) ∧
      RuntimeStateTy cfg activations after := by
  unfold execPure at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨targetTyped, sameState⟩ := frameTyped.2.2.getVal targetMetadata read
  subst middle
  obtain ⟨location, rfl, target⟩ := targetTyped
  simp only [expectRef, pure_bind] at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.2.2.getVal valueMetadata read
  subst middle
  cases org with
  | none => exact pushAppend_typed frameTyped.1 target ownerType valueTyped evaluated
  | some origin =>
    obtain ⟨result, middle, checked, evaluated⟩ := m_bind_ok evaluated
    have sameState := checkCapacityAtOrg_state checked
    subst middle
    exact pushAppend_typed frameTyped.1 target ownerType valueTyped evaluated

theorem releaseSlots_typed {roots : RootDeclarations} {fn : Func} {act : ActId}
    {scope : ScopeId} {instanceId : ScopeInst} (count : Nat) {store : Store}
    (typed : WeakStoreTy roots store) :
    WeakStoreTy roots (releaseSlots fn act scope instanceId count store) := by
  induction count generalizing store with
  | zero => exact typed
  | succ count ih =>
    simp only [releaseSlots]
    cases lookup : fn.slots[count]? with
    | none => simpa only [lookup] using ih typed
    | some slot =>
      simp only
      split
      · exact ih typed.release
      · exact ih typed

theorem execEff_slotInit_typed {activations : ActivationTypes} {fn : Func} {cfg : GCfg}
    {fr fr' : Frame} {slotId : SlotId} {valueId : ValueId} {slot : Slot}
    {org : Option OriginId} {before after : St}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (lookup : fn.slots[slotId]? = some slot)
    (metadata : (fn.valueTypes cfg.mod)[valueId]? = some (some (.data slot.ty)))
    (evaluated : execEff fn fr (.slotInit slotId valueId org) before = .ok fr' after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  simp only [execEff, slotRoot, lookup] at evaluated
  cases scopeLookup : fr.scopes.lookup slot.scope with
  | none => simp [scopeLookup, bind_apply, fault, M.stop] at evaluated
  | some instanceId =>
    simp only [scopeLookup, pure_bind] at evaluated
    obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
    obtain ⟨valueTyped, sameState⟩ := frameTyped.2.2.getVal metadata read
    subst middle
    simp only [bindRoot, bind_apply, pure_apply, Res.ok.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    refine ⟨⟨frameTyped.1.1, frameTyped.1.2.introduce ?_ valueTyped⟩, frameTyped.2⟩
    simp [runtimeDeclarations, frameTyped.2.1, lookup]

theorem truncateEffect_typed {cfg : GCfg} {fn : Func} {activations : ActivationTypes}
    {fr fr' : Frame} {location : Loc} {owner element : Ty} {len : Nat} {before after : St}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (target : DeclaredLocation (runtimeDeclarations cfg activations) location owner)
    (ownerType : owner.ownerElem? = some element)
    (evaluated : (truncateLoc location len >>= fun _ => pure fr) before = .ok fr' after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  obtain ⟨result, middle, shortened, evaluated⟩ := m_bind_ok evaluated
  simp only [pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  unfold truncateLoc at shortened
  cases changed : before.store.truncate location len with
  | error fault => simp [changed] at shortened
  | ok store =>
    simp only [changed, Res.ok.injEq] at shortened
    obtain ⟨_, sameState⟩ := shortened
    subst middle
    exact ⟨⟨frameTyped.1.1, frameTyped.1.2.truncateOwner target ownerType changed⟩, frameTyped.2⟩

theorem appendEffect_typed {cfg : GCfg} {fn : Func} {activations : ActivationTypes}
    {fr fr' : Frame} {location : Loc} {owner element : Ty} {values : Array Val} {before after : St}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (target : DeclaredLocation (runtimeDeclarations cfg activations) location owner)
    (ownerType : owner.ownerElem? = some element)
    (valuesTyped : ∀ (i : Nat) (value : Val), values[i]? = some value →
      WeakValueTy (runtimeDeclarations cfg activations) value element)
    (evaluated : (appendLoc location values >>= fun _ => pure fr) before = .ok fr' after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  obtain ⟨index, middle, appended, evaluated⟩ := m_bind_ok evaluated
  simp only [pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  unfold appendLoc at appended
  cases changed : before.store.append location values with
  | error fault => simp [changed] at appended
  | ok result =>
    obtain ⟨store, start⟩ := result
    simp only [changed, Res.ok.injEq] at appended
    obtain ⟨rfl, sameState⟩ := appended
    subst middle
    exact ⟨⟨frameTyped.1.1, frameTyped.1.2.appendOwner target ownerType valuesTyped changed⟩,
      frameTyped.2⟩

theorem writeEffect_typed {cfg : GCfg} {fn : Func} {activations : ActivationTypes}
    {fr fr' : Frame} {location : Loc} {ty : Ty} {value : Val} {before after : St}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (target : DeclaredLocation (runtimeDeclarations cfg activations) location ty)
    (valueTyped : WeakValueTy (runtimeDeclarations cfg activations) value ty)
    (evaluated : (writeLoc location value >>= fun _ => pure fr) before = .ok fr' after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  obtain ⟨result, middle, written, evaluated⟩ := m_bind_ok evaluated
  simp only [pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  unfold writeLoc at written
  cases changed : before.store.write location value with
  | error fault => simp [changed] at written
  | ok store =>
    simp only [changed, Res.ok.injEq] at written
    obtain ⟨_, sameState⟩ := written
    subst middle
    exact ⟨⟨frameTyped.1.1, frameTyped.1.2.write target valueTyped changed⟩, frameTyped.2⟩

theorem execEff_clear_typed {activations : ActivationTypes} {fn : Func} {cfg : GCfg}
    {fr fr' : Frame} {targetId : ValueId} {permission : Mutability} {owner element : Ty}
    {org : Option OriginId} {before after : St}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (metadata : (fn.valueTypes cfg.mod)[targetId]? = some (some (.data (.ref permission owner))))
    (ownerType : owner.ownerElem? = some element)
    (evaluated : execEff fn fr (.clear targetId org) before = .ok fr' after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  unfold execEff at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨targetTyped, sameState⟩ := frameTyped.2.2.getVal metadata read
  subst middle
  obtain ⟨location, rfl, target⟩ := targetTyped
  simp only [expectRef, pure_bind] at evaluated
  exact truncateEffect_typed frameTyped target ownerType evaluated

theorem execEff_popN_typed {activations : ActivationTypes} {fn : Func} {cfg : GCfg}
    {fr fr' : Frame} {targetId countId : ValueId} {permission : Mutability} {owner element : Ty}
    {countTy : IntTy} {org : Option OriginId} {before after : St}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (targetMetadata : (fn.valueTypes cfg.mod)[targetId]? = some (some (.data (.ref permission owner))))
    (countMetadata : (fn.valueTypes cfg.mod)[countId]? = some (some (.data (.int countTy))))
    (ownerType : owner.ownerElem? = some element)
    (evaluated : execEff fn fr (.popN targetId countId org) before = .ok fr' after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  unfold execEff at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨targetTyped, sameState⟩ := frameTyped.2.2.getVal targetMetadata read
  subst middle
  obtain ⟨location, rfl, target⟩ := targetTyped
  simp only [expectRef, pure_bind] at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨countTyped, sameState⟩ := frameTyped.2.2.getVal countMetadata read
  subst middle
  obtain ⟨count, rfl⟩ := countTyped.int
  simp only [expectInt, pure_bind] at evaluated
  obtain ⟨len, middle, measured, evaluated⟩ := m_bind_ok evaluated
  have sameState := lengthLoc_state measured
  subst middle
  split at evaluated
  · cases org <;> simp [abortAtOrg, abortAt, fault, M.stop] at evaluated
  · exact truncateEffect_typed frameTyped target ownerType evaluated

theorem execEff_replace_typed {activations : ActivationTypes} {fn : Func} {cfg : GCfg}
    {fr fr' : Frame} {targetId valueId : ValueId} {permission : Mutability} {owner : Ty}
    {org : Option OriginId} {before after : St}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (targetMetadata : (fn.valueTypes cfg.mod)[targetId]? = some (some (.data (.ref permission owner))))
    (valueMetadata : (fn.valueTypes cfg.mod)[valueId]? = some (some (.data owner)))
    (evaluated : execEff fn fr (.replace targetId valueId org) before = .ok fr' after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  unfold execEff at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨targetTyped, sameState⟩ := frameTyped.2.2.getVal targetMetadata read
  subst middle
  obtain ⟨location, rfl, target⟩ := targetTyped
  simp only [expectRef, pure_bind] at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.2.2.getVal valueMetadata read
  subst middle
  cases value <;> simp only at evaluated
  all_goals first
    | (simp [bind_apply, fault, M.stop] at evaluated; done)
    | exact writeEffect_typed frameTyped target valueTyped evaluated

theorem execEff_append_typed {activations : ActivationTypes} {fn : Func} {cfg : GCfg}
    {fr fr' : Frame} {targetId viewId : ValueId} {permission viewPermission : Mutability}
    {owner element : Ty} {org : Option OriginId} {before after : St}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (targetMetadata : (fn.valueTypes cfg.mod)[targetId]? = some (some (.data (.ref permission owner))))
    (viewMetadata : (fn.valueTypes cfg.mod)[viewId]? = some (some (.view viewPermission element)))
    (ownerType : owner.ownerElem? = some element)
    (evaluated : execEff fn fr (.append targetId viewId org) before = .ok fr' after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  unfold execEff at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨targetTyped, sameState⟩ := frameTyped.2.2.getVal targetMetadata read
  subst middle
  obtain ⟨location, rfl, target⟩ := targetTyped
  simp only [expectRef, pure_bind] at evaluated
  obtain ⟨view, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨viewTyped, sameState⟩ := frameTyped.2.2.getView viewMetadata read
  subst middle
  obtain ⟨values, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valuesTyped, sameState⟩ := viewTyped.readRun frameTyped.1.2 read
  subst middle
  obtain ⟨result, middle, checked, evaluated⟩ := m_bind_ok evaluated
  have sameState := checkCapacityAtOrg_state checked
  subst middle
  exact appendEffect_typed frameTyped target ownerType valuesTyped evaluated

theorem resizeTail_typed {cfg : GCfg} {fn : Func} {activations : ActivationTypes}
    {fr fr' : Frame} {location : Loc} {owner element : Ty} {size : Int} {fill : Option Val}
    {org : Option OriginId} {before after : St}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (target : DeclaredLocation (runtimeDeclarations cfg activations) location owner)
    (ownerType : owner.ownerElem? = some element)
    (fillTyped : ∀ value, fill = some value → WeakValueTy (runtimeDeclarations cfg activations) value element)
    (evaluated : (do
      let len ← lengthLoc location
      let size := wrap .i64 size
      if size < 0 then abortAtOrg .resizeNegative org
      else if size.toNat < len then
        truncateLoc location size.toNat
        pure fr
      else if size.toNat == len then pure fr
      else
        match fill with
        | none => abortAtOrg .resizeFill org
        | some value => do
          checkCapacityAtOrg location (size.toNat - len) org
          let _ ← appendLoc location (Array.replicate (size.toNat - len) value)
          pure fr) before = .ok fr' after) : RuntimeFrameTy cfg fn activations fr' after := by
  obtain ⟨len, middle, measured, evaluated⟩ := m_bind_ok evaluated
  have sameState := lengthLoc_state measured
  subst middle
  dsimp only at evaluated
  split at evaluated
  · cases org <;> simp [abortAtOrg, abortAt, fault, M.stop] at evaluated
  · split at evaluated
    · exact truncateEffect_typed frameTyped target ownerType evaluated
    · split at evaluated
      · simp only [pure_apply, Res.ok.injEq] at evaluated
        obtain ⟨rfl, rfl⟩ := evaluated
        exact frameTyped
      · cases fill with
        | none => cases org <;> simp [abortAtOrg, abortAt, fault, M.stop] at evaluated
        | some value =>
          obtain ⟨result, middle, checked, evaluated⟩ := m_bind_ok evaluated
          have sameState := checkCapacityAtOrg_state checked
          subst middle
          apply appendEffect_typed frameTyped target ownerType _ evaluated
          intro index selected present
          rw [Array.getElem?_replicate] at present
          split at present
          · cases present
            exact fillTyped value rfl
          · contradiction

theorem execEff_resize_typed {activations : ActivationTypes} {fn : Func} {cfg : GCfg}
    {fr fr' : Frame} {targetId sizeId : ValueId} {permission : Mutability} {owner element : Ty}
    {sizeTy : IntTy} {fillId : Option ValueId} {org : Option OriginId} {before after : St}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (targetMetadata : (fn.valueTypes cfg.mod)[targetId]? = some (some (.data (.ref permission owner))))
    (sizeMetadata : (fn.valueTypes cfg.mod)[sizeId]? = some (some (.data (.int sizeTy))))
    (fillMetadata : ∀ id, fillId = some id → (fn.valueTypes cfg.mod)[id]? = some (some (.data element)))
    (ownerType : owner.ownerElem? = some element)
    (evaluated : execEff fn fr (.resize targetId sizeId fillId org) before = .ok fr' after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  unfold execEff at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨targetTyped, sameState⟩ := frameTyped.2.2.getVal targetMetadata read
  subst middle
  obtain ⟨location, rfl, target⟩ := targetTyped
  simp only [expectRef, pure_bind] at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨sizeTyped, sameState⟩ := frameTyped.2.2.getVal sizeMetadata read
  subst middle
  obtain ⟨size, rfl⟩ := sizeTyped.int
  simp only [expectInt, pure_bind] at evaluated
  cases fillId with
  | none =>
    simp only at evaluated
    exact resizeTail_typed (size := size) (fill := none) (org := org) frameTyped target ownerType (by simp) evaluated
  | some id =>
    simp only at evaluated
    obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
    obtain ⟨valueTyped, sameState⟩ := frameTyped.2.2.getVal (fillMetadata id rfl) read
    subst middle
    apply resizeTail_typed (size := size) (fill := some value) (org := org) frameTyped target ownerType _ evaluated
    intro other same
    cases same
    exact valueTyped

theorem render_state {value : Val} {before after : St} {output : String}
    (rendered : Goose.Core.render value before = .ok output after) : after = before := by
  cases value <;> simp [Goose.Core.render, fault, M.stop, pure_apply] at rendered
  all_goals first
    | exact rendered.2.symm
    | (rename_i b
       cases b <;> simp only [pure_apply, Res.ok.injEq] at rendered <;> exact rendered.2.symm)

theorem renderPart_state {fr : Frame} {part : PrintPart} {before after : St} {output : String}
    (rendered : renderPart fr part before = .ok output after) : after = before := by
  cases part with
  | text text =>
    simp only [renderPart, pure_apply, Res.ok.injEq] at rendered
    exact rendered.2.symm
  | val id =>
    unfold renderPart at rendered
    obtain ⟨value, middle, read, rendered⟩ := m_bind_ok rendered
    have sameState := (getVal_success read).2
    subst middle
    exact render_state rendered

theorem execEff_print_typed {activations : ActivationTypes} {fn : Func} {cfg : GCfg}
    {fr fr' : Frame} {parts : List PrintPart} {org : Option OriginId} {before after : St}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (evaluated : execEff fn fr (.print parts org) before = .ok fr' after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  unfold execEff at evaluated
  obtain ⟨strings, middle, rendered, evaluated⟩ := m_bind_ok evaluated
  have sameState := mapList_state (fun _ _ _ _ read => renderPart_state read) rendered
  subst middle
  simp only [emit, bind_apply, pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  exact ⟨frameTyped.1, frameTyped.2⟩

theorem execEff_store_typed {activations : ActivationTypes} {fn : Func} {cfg : GCfg}
    {fr fr' : Frame} {targetId valueId : ValueId} {permission : Mutability} {ty : Ty}
    {org : Option OriginId} {before after : St}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (targetMetadata : (fn.valueTypes cfg.mod)[targetId]? = some (some (.data (.ref permission ty))))
    (valueMetadata : (fn.valueTypes cfg.mod)[valueId]? = some (some (.data ty)))
    (evaluated : execEff fn fr (.store targetId valueId org) before = .ok fr' after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  unfold execEff at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨targetTyped, sameState⟩ := frameTyped.2.2.getVal targetMetadata read
  subst middle
  obtain ⟨location, rfl, target⟩ := targetTyped
  simp only [expectRef, pure_bind] at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameState⟩ := frameTyped.2.2.getVal valueMetadata read
  subst middle
  exact writeEffect_typed frameTyped target valueTyped evaluated

theorem execEff_enter_typed {activations : ActivationTypes} {fn : Func} {cfg : GCfg}
    {fr fr' : Frame} {scope : ScopeId} {before after : St}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (evaluated : execEff fn fr (.enter scope) before = .ok fr' after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  simp only [execEff, freshScope, bind_apply, pure_apply, Res.ok.injEq] at evaluated
  obtain ⟨rfl, rfl⟩ := evaluated
  exact ⟨frameTyped.1, frameTyped.2.1, frameTyped.2.2⟩

theorem execEff_leave_typed {activations : ActivationTypes} {fn : Func} {cfg : GCfg}
    {fr fr' : Frame} {scope : ScopeId} {before after : St}
    (frameTyped : RuntimeFrameTy cfg fn activations fr before)
    (evaluated : execEff fn fr (.leave scope) before = .ok fr' after) :
    RuntimeFrameTy cfg fn activations fr' after := by
  simp only [execEff] at evaluated
  cases scopes : fr.scopes with
  | nil => simp [scopes, fault, M.stop] at evaluated
  | cons top rest =>
    obtain ⟨currentScope, instanceId⟩ := top
    simp only [scopes] at evaluated
    split at evaluated
    · simp only [Goose.GIR.releaseScope, bind_apply, pure_apply, Res.ok.injEq] at evaluated
      obtain ⟨rfl, rfl⟩ := evaluated
      exact ⟨⟨frameTyped.1.1, releaseSlots_typed fn.slots.size frameTyped.1.2⟩,
        frameTyped.2.1, frameTyped.2.2⟩
    · simp [fault, M.stop] at evaluated

theorem execPure_load_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {id : ValueId} {permission : Mutability} {ty : Ty}
    {before after : St} {cell : RVal}
    (frameTyped : WeakFrameTy roots types fr)
    (metadata : types[id]? = some (some (.data (.ref permission ty))))
    (storeTyped : WeakStoreTy roots before.store)
    (evaluated : execPure cx fr (.load id) before = .ok cell after) :
    WeakCellTy roots cell (.data ty) ∧ after = before := by
  unfold execPure at evaluated
  cases read : getVal fr id before with
  | stop outcome state => simp [bind_apply, read] at evaluated
  | ok value state =>
    obtain ⟨valueTyped, rfl⟩ := frameTyped.getVal metadata read
    obtain ⟨location, rfl, declared⟩ := valueTyped
    simp only [bind_apply, read, expectRef, pure_apply] at evaluated
    unfold readLoc at evaluated
    cases stored : state.store.read location with
    | error fault => simp [stored] at evaluated
    | ok value =>
      simp only [stored, Res.ok.injEq] at evaluated
      obtain ⟨rfl, rfl⟩ := evaluated
      exact ⟨storeTyped.read declared stored, rfl⟩

theorem execPure_pop_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {cx : FnCtx} {fr : Frame} {id : ValueId} {permission : Mutability} {owner element : Ty}
    {org : Option OriginId} {before after : St} {cell : RVal}
    (frameTyped : WeakFrameTy roots types fr)
    (metadata : types[id]? = some (some (.data (.ref permission owner))))
    (ownerType : owner.ownerElem? = some element) (storeTyped : WeakStoreTy roots before.store)
    (evaluated : execPure cx fr (.pop id org) before = .ok cell after) :
    WeakCellTy roots cell (.data element) ∧ WeakStoreTy roots after.store := by
  unfold execPure at evaluated
  obtain ⟨value, middle, read, evaluated⟩ := m_bind_ok evaluated
  obtain ⟨valueTyped, sameReadState⟩ := frameTyped.getVal metadata read
  subst middle
  obtain ⟨location, rfl, target⟩ := valueTyped
  simp only [expectRef, pure_bind] at evaluated
  obtain ⟨len, middle, measured, evaluated⟩ := m_bind_ok evaluated
  have sameState : middle = before := by
    unfold lengthLoc at measured
    cases size : before.store.length location <;> simp [size] at measured
    exact measured.2.symm
  subst middle
  split at evaluated
  · cases org <;> simp [abortAtOrg, abortAt, fault, M.stop] at evaluated
  · obtain ⟨selected, middle, loaded, evaluated⟩ := m_bind_ok evaluated
    have elementTarget := target.ownerElement ownerType (len - 1)
    obtain ⟨selectedTyped, sameLoadState⟩ := storeTyped.readLoc elementTarget loaded
    subst middle
    obtain ⟨result, finalState, shortened, evaluated⟩ := m_bind_ok evaluated
    simp only [pure_apply, Res.ok.injEq] at evaluated
    obtain ⟨rfl, rfl⟩ := evaluated
    unfold truncateLoc at shortened
    cases shrunk : before.store.truncate location (len - 1) with
    | error fault => simp [shrunk] at shortened
    | ok store =>
      simp only [shrunk, Res.ok.injEq] at shortened
      obtain ⟨_, sameState⟩ := shortened
      subst finalState
      exact ⟨selectedTyped, storeTyped.truncateOwner target ownerType shrunk⟩

inductive ParamValuesTy (roots : RootDeclarations) : List (ValueId × VTy) → List RVal → Prop
  | nil : ParamValuesTy roots [] []
  | cons {param arg params args}
      (head : WeakCellTy roots arg param.2) (tail : ParamValuesTy roots params args) :
      ParamValuesTy roots (param :: params) (arg :: args)

inductive CallValuesTy (roots : RootDeclarations) : List Ty → List Val → Prop
  | nil : CallValuesTy roots [] []
  | cons {ty value types values}
      (head : WeakValueTy roots value ty) (tail : CallValuesTy roots types values) :
      CallValuesTy roots (ty :: types) (value :: values)

theorem CallValuesTy.entry {roots : RootDeclarations} {types : List Ty} {values : List Val}
    {params : List (ValueId × VTy)} (typed : CallValuesTy roots types values)
    (sameTypes : params.map Prod.snd = types.map VTy.data) :
    ParamValuesTy roots params (values.map RVal.val) := by
  induction typed generalizing params with
  | nil =>
    cases params <;> simp_all
    exact .nil
  | @cons ty value types values head tail ih =>
    cases params with
    | nil => simp at sameTypes
    | cons param params =>
      simp only [List.map_cons, List.cons.injEq] at sameTypes
      apply ParamValuesTy.cons
      · rw [sameTypes.1]
        exact head
      · exact ih sameTypes.2

theorem WeakFrameTy.callArgs {roots : RootDeclarations} {types : Array (Option VTy)}
    {fr : Frame} {params : List Ty} {ids : List ValueId} {values : List Val} {before after : St}
    (typed : WeakFrameTy roots types fr) (arity : params.length = ids.length)
    (metadata : ∀ pair ∈ params.zip ids, ∃ source,
      types[pair.2]? = some (some (.data source)) ∧ source.passableTo pair.1 = true)
    (read : mapList (Goose.GIR.getVal fr) ids before = .ok values after) :
    CallValuesTy roots params values ∧ after = before := by
  induction params generalizing ids values before after with
  | nil =>
    have empty : ids = [] := List.length_eq_zero_iff.mp arity.symm
    subst ids
    simp only [mapList, pure_apply, Res.ok.injEq] at read
    obtain ⟨rfl, rfl⟩ := read
    exact ⟨.nil, rfl⟩
  | cons param params ih =>
    cases ids with
    | nil => simp at arity
    | cons id ids =>
      simp only [List.length_cons, Nat.succ.injEq] at arity
      obtain ⟨source, headMetadata, passing⟩ := metadata (param, id) (by simp)
      simp only [mapList] at read
      obtain ⟨value, middle, found, read⟩ := m_bind_ok read
      obtain ⟨headTyped, sameState⟩ := typed.getVal headMetadata found
      subst middle
      obtain ⟨tail, middle, foundTail, read⟩ := m_bind_ok read
      obtain ⟨tailTyped, sameState⟩ := ih arity
        (fun pair present => metadata pair (List.mem_cons_of_mem _ present)) foundTail
      subst middle
      simp only [pure_apply, Res.ok.injEq] at read
      obtain ⟨rfl, rfl⟩ := read
      exact ⟨.cons (headTyped.passable passing) tailTyped, rfl⟩

theorem WeakFrameTy.branchArgs {roots : RootDeclarations} {types : Array (Option VTy)}
    {fr : Frame} {params : List (ValueId × VTy)} {ids : List ValueId} {values : List RVal}
    {before after : St} (typed : WeakFrameTy roots types fr)
    (metadata : ids.map (fun id => types[id]?) = params.map (fun param => some (some param.2)))
    (read : mapList (getCell fr) ids before = .ok values after) :
    ParamValuesTy roots params values ∧ after = before := by
  induction params generalizing ids values before after with
  | nil =>
    cases ids with
    | cons id ids => simp at metadata
    | nil =>
      simp only [mapList, pure_apply, Res.ok.injEq] at read
      obtain ⟨rfl, rfl⟩ := read
      exact ⟨.nil, rfl⟩
  | cons param params ih =>
    cases ids with
    | nil => simp at metadata
    | cons id ids =>
      simp only [List.map_cons, List.cons.injEq] at metadata
      simp only [mapList] at read
      obtain ⟨value, middle, found, read⟩ := m_bind_ok read
      obtain ⟨present, sameState⟩ := getCell_success found
      subst middle
      have headTyped := typed id value param.2 metadata.1 present
      obtain ⟨tail, middle, foundTail, read⟩ := m_bind_ok read
      obtain ⟨tailTyped, sameState⟩ := ih metadata.2 foundTail
      subst middle
      simp only [pure_apply, Res.ok.injEq] at read
      obtain ⟨rfl, rfl⟩ := read
      exact ⟨.cons headTyped tailTyped, rfl⟩

theorem ParamValuesTy.mono {before after : RootDeclarations} {params : List (ValueId × VTy)}
    {args : List RVal} (extension : before.Extends after) (typed : ParamValuesTy before params args) :
    ParamValuesTy after params args := by
  induction typed with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.mono extension) ih

theorem bindParams_act {params : List (ValueId × VTy)} {args : List RVal} {fr fr' : Frame}
    {before after : St} (bound : bindParams fr params args before = .ok fr' after) :
    fr'.act = fr.act := by
  induction params generalizing args fr with
  | nil =>
    simp only [bindParams, pure_apply, Res.ok.injEq] at bound
    exact congrArg Frame.act bound.1.symm
  | cons param params ih =>
    cases args with
    | nil =>
      simp only [bindParams, pure_apply, Res.ok.injEq] at bound
      exact congrArg Frame.act bound.1.symm
    | cons arg args =>
      simp only [bindParams, setCell, pure_bind] at bound
      exact ih (fr := { fr with vals := fr.vals.insert param.1 arg }) bound

theorem enterBlock_act {fn : Func} {fr fr' : Frame} {block : BlockId} {args : List RVal}
    {before after : St} {insts : List Inst}
    (entered : enterBlock fn fr block args before = .ok (insts, fr') after) : fr'.act = fr.act := by
  unfold enterBlock at entered
  cases lookup : fn.blocks[block]? with
  | none => simp [lookup, fault, M.stop] at entered
  | some destination =>
    simp only [lookup] at entered
    split at entered
    · obtain ⟨frame, middle, bound, entered⟩ := m_bind_ok entered
      simp only [pure_apply, Res.ok.injEq, Prod.mk.injEq] at entered
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := entered
      exact bindParams_act bound
    · simp [fault, M.stop] at entered

theorem bindParams_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {params : List (ValueId × VTy)} {args : List RVal} {fr fr' : Frame} {before after : St}
    (frameTyped : WeakFrameTy roots types fr)
    (metadata : ∀ param ∈ params, types[param.1]? = some (some param.2))
    (argsTyped : ParamValuesTy roots params args)
    (bound : bindParams fr params args before = .ok fr' after) :
    WeakFrameTy roots types fr' ∧ after = before := by
  induction argsTyped generalizing fr with
  | nil =>
    simp only [bindParams, pure_apply, Res.ok.injEq] at bound
    obtain ⟨rfl, rfl⟩ := bound
    exact ⟨frameTyped, rfl⟩
  | @cons param arg params args argTyped restTyped ih =>
    simp only [bindParams, setCell, pure_bind] at bound
    apply ih (fr := fr.set param.1 arg)
    · exact frameTyped.set (metadata param (by simp)) argTyped
    · intro other present
      exact metadata other (List.mem_cons_of_mem _ present)
    · exact bound

theorem enterBlock_typed {roots : RootDeclarations} {types : Array (Option VTy)}
    {fn : Func} {block : GIR.Block} {id : BlockId} {args : List RVal} {fr fr' : Frame}
    {before after : St} {insts : List Inst}
    (lookup : fn.blocks[id]? = some block) (frameTyped : WeakFrameTy roots types fr)
    (metadata : ∀ param ∈ block.params, types[param.1]? = some (some param.2))
    (argsTyped : ParamValuesTy roots block.params args)
    (entered : enterBlock fn fr id args before = .ok (insts, fr') after) :
    WeakFrameTy roots types fr' ∧ after = before := by
  simp only [enterBlock, lookup] at entered
  split at entered
  · cases bound : bindParams fr block.params args before with
    | stop outcome state => simp [bind_apply, bound] at entered
    | ok frame state =>
      simp only [bind_apply, bound, pure_apply, Res.ok.injEq, Prod.mk.injEq] at entered
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := entered
      exact bindParams_typed frameTyped metadata argsTyped bound
  · simp [fault, M.stop] at entered

theorem FunctionEntry.typed {cfg : GCfg} {activations : ActivationTypes} {fn : Func}
    {depth : Nat} {args : List Val} {before after : St} {fr : Frame} {entryBlock : GIR.Block}
    (stateTyped : RuntimeStateTy cfg activations before) (lookup : fn.blocks[0]? = some entryBlock)
    (metadata : ∀ param ∈ entryBlock.params,
      (fn.valueTypes cfg.mod)[param.1]? = some (some param.2))
    (argsTyped : ParamValuesTy (runtimeDeclarations cfg activations) entryBlock.params
      (args.map RVal.val))
    (entry : FunctionEntry fn depth args before fr after) :
    ∃ extended, (runtimeDeclarations cfg activations).Extends (runtimeDeclarations cfg extended) ∧
      RuntimeFrameTy cfg fn extended fr after := by
  obtain ⟨arity, act, fresh, allocated, entered⟩ := entry
  obtain ⟨freshTyped, owner, extension⟩ := stateTyped.freshAct fn allocated
  obtain ⟨frameTyped, sameState⟩ := enterBlock_typed lookup
    (WeakFrameTy.empty _ _ act depth) metadata (argsTyped.mono extension) entered
  have current := enterBlock_act entered
  change fr.act = act at current
  refine ⟨activations.enter act fn, extension, ?_⟩
  refine ⟨sameState ▸ freshTyped, ?_, frameTyped⟩
  rw [current]
  exact owner

end Goose.Evidence
