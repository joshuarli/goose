import Goose.Lower.Claims
import Goose.Core.Sound.Retain
import Goose.Core.Sound.Lemmas

namespace Goose.Lower

open Goose.Core Goose.GIR

def ValueAliasAt (m : Core.Module) (world : Core.Sound.World) (env : Env) (store : Store)
    (frame : GIR.Frame) (value : ValueId) (alias : RetainedAlias) : Prop :=
  ∃ v, frame.vals[value]? = some (.val v) ∧ Core.Sound.AliasAt m world env store alias v

def SliceRunAliasAt (m : Core.Module) (world : Core.Sound.World) (env : Env) (store : Store)
    (frame : GIR.Frame) (value : ValueId) (alias : RetainedAlias) : Prop :=
  ∃ view mu element, frame.vals[value]? = some (.view view) ∧
    alias.ty = .slice mu element ∧
    Core.Sound.AliasAt m world env store alias (.slice view.loc view.start view.len)

def LimitedRunAliasAt (m : Core.Module) (world : Core.Sound.World) (env : Env) (store : Store)
    (frame : GIR.Frame) (value : ValueId) (alias : RetainedAlias) : Prop :=
  ∃ view mu element capacity, frame.vals[value]? = some (.view view) ∧
    alias.ty = .ref mu (.limited element capacity) ∧
    Core.Sound.AliasAt m world env store alias (.ref view.loc) ∧
    Core.Sound.SliceTy store view.loc view.start view.len element

def RunAliasAt (m : Core.Module) (world : Core.Sound.World) (env : Env) (store : Store)
    (frame : GIR.Frame) (value : ValueId) (alias : RetainedAlias) : Prop :=
  SliceRunAliasAt m world env store frame value alias ∨
    LimitedRunAliasAt m world env store frame value alias

theorem ValueAliasAt.of_post {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls ls' : LS} {fr fr' : GIR.Frame} {pt : Pt} {cells : List (ValueId × RVal)}
    (hpost : Post cfg env cx ls fr ls' fr' pt cells) {value : ValueId} {v : Val}
    (hcell : (value, .val v) ∈ cells) {world : Core.Sound.World} {store : Store} {alias : RetainedAlias}
    (halias : Core.Sound.AliasAt cfg.mod world env store alias v) :
    ValueAliasAt cfg.mod world env store fr' value alias :=
  ⟨v, hpost.has (value, .val v) hcell, halias⟩

theorem SliceRunAliasAt.of_post {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls ls' : LS} {fr fr' : GIR.Frame} {pt : Pt} {cells : List (ValueId × RVal)}
    (hpost : Post cfg env cx ls fr ls' fr' pt cells) {value : ValueId} {view : ViewVal}
    (hcell : (value, .view view) ∈ cells) {world : Core.Sound.World} {store : Store}
    {alias : RetainedAlias} {mu : Mutability} {element : Ty}
    (htype : alias.ty = .slice mu element)
    (halias : Core.Sound.AliasAt cfg.mod world env store alias
      (.slice view.loc view.start view.len)) :
    SliceRunAliasAt cfg.mod world env store fr' value alias :=
  ⟨view, mu, element, hpost.has (value, .view view) hcell, htype, halias⟩

theorem LimitedRunAliasAt.of_post {cfg : Cfg} {env : Env} {cx : FnCtx}
    {ls ls' : LS} {fr fr' : GIR.Frame} {pt : Pt} {cells : List (ValueId × RVal)}
    (hpost : Post cfg env cx ls fr ls' fr' pt cells) {value : ValueId} {view : ViewVal}
    (hcell : (value, .view view) ∈ cells) {world : Core.Sound.World} {store : Store}
    {alias : RetainedAlias} {mu : Mutability} {element : Ty} {capacity : Nat}
    (htype : alias.ty = .ref mu (.limited element capacity))
    (halias : Core.Sound.AliasAt cfg.mod world env store alias (.ref view.loc))
    (hrun : Core.Sound.SliceTy store view.loc view.start view.len element) :
    LimitedRunAliasAt cfg.mod world env store fr' value alias :=
  ⟨view, mu, element, capacity, hpost.has (value, .view view) hcell, htype, halias, hrun⟩

theorem ValueAliasAt.retained {m : Core.Module} {world : Core.Sound.World} {env : Env}
    {store store' : Store} {fr fr' : GIR.Frame} {value frontier : ValueId} {alias : RetainedAlias}
    (h : ValueAliasAt m world env store fr value alias)
    (hsame : Same frontier fr fr') (hvalue : value < frontier)
    (hretains : Core.Sound.RetainsAlias m world env store store' alias) :
    ValueAliasAt m world env store' fr' value alias := by
  obtain ⟨v, hcell, halias⟩ := h
  exact ⟨v, (hsame value hvalue).trans hcell, hretains.typed v halias⟩

theorem SliceRunAliasAt.retained {m : Core.Module} {world : Core.Sound.World} {env : Env}
    {store store' : Store} {fr fr' : GIR.Frame} {value frontier : ValueId} {alias : RetainedAlias}
    (h : SliceRunAliasAt m world env store fr value alias)
    (hsame : Same frontier fr fr') (hvalue : value < frontier)
    (hretains : Core.Sound.RetainsAlias m world env store store' alias) :
    SliceRunAliasAt m world env store' fr' value alias := by
  obtain ⟨view, mu, element, hcell, htype, halias⟩ := h
  exact ⟨view, mu, element, (hsame value hvalue).trans hcell, htype,
    hretains.typed (.slice view.loc view.start view.len) halias⟩

theorem LimitedRunAliasAt.retained {m : Core.Module} {world : Core.Sound.World} {env : Env}
    {store store' : Store} {fr fr' : GIR.Frame} {value frontier : ValueId} {alias : RetainedAlias}
    (h : LimitedRunAliasAt m world env store fr value alias)
    (hsame : Same frontier fr fr') (hvalue : value < frontier)
    (hretains : Core.Sound.RetainsAlias m world env store store' alias) :
    LimitedRunAliasAt m world env store' fr' value alias := by
  obtain ⟨view, mu, element, capacity, hcell, htype, halias, hslice⟩ := h
  exact ⟨view, mu, element, capacity, (hsame value hvalue).trans hcell, htype,
    hretains.typed (.ref view.loc) halias,
    hretains.physicalLimited mu element capacity view.loc view.start view.len htype halias hslice⟩

theorem RunAliasAt.retained {m : Core.Module} {world : Core.Sound.World} {env : Env}
    {store store' : Store} {fr fr' : GIR.Frame} {value frontier : ValueId} {alias : RetainedAlias}
    (h : RunAliasAt m world env store fr value alias)
    (hsame : Same frontier fr fr') (hvalue : value < frontier)
    (hretains : Core.Sound.RetainsAlias m world env store store' alias) :
    RunAliasAt m world env store' fr' value alias :=
  h.elim (fun h => Or.inl (h.retained hsame hvalue hretains))
    (fun h => Or.inr (h.retained hsame hvalue hretains))

def RetainedOperandsAt (m : Core.Module) (world : Core.Sound.World) (env : Env) (store : Store)
    (frame : GIR.Frame) (values runs : List (ValueId × RetainedAlias)) : Prop :=
  (∀ cell ∈ values, ValueAliasAt m world env store frame cell.1 cell.2) ∧
  (∀ cell ∈ runs, RunAliasAt m world env store frame cell.1 cell.2)

theorem RetainedOperandsAt.retained {m : Core.Module} {world : Core.Sound.World} {env : Env}
    {store store' : Store} {fr fr' : GIR.Frame} {frontier : ValueId}
    {values runs : List (ValueId × RetainedAlias)}
    (h : RetainedOperandsAt m world env store fr values runs)
    (hsame : Same frontier fr fr')
    (hvalues : ∀ cell ∈ values, cell.1 < frontier)
    (hruns : ∀ cell ∈ runs, cell.1 < frontier)
    (hretains : Core.Sound.RetainsAliases m world env store store'
      (values.map Prod.snd ++ runs.map Prod.snd)) :
    RetainedOperandsAt m world env store' fr' values runs := by
  constructor
  · intro cell hcell
    apply (h.1 cell hcell).retained hsame (hvalues cell hcell)
    exact hretains cell.2 (List.mem_append_left _ (List.mem_map.mpr ⟨cell, hcell, rfl⟩))
  · intro cell hcell
    apply (h.2 cell hcell).retained hsame (hruns cell hcell)
    exact hretains cell.2 (List.mem_append_right _ (List.mem_map.mpr ⟨cell, hcell, rfl⟩))

theorem Rel.demanded_slot {cfg : Cfg} {world : Core.Sound.World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {state : St} {future : List VarId} {cx : FnCtx} {fr : GIR.Frame} {ls : LS}
    (hrel : Rel cfg env cx fr ls)
    (hframe : Core.Sound.Frame cfg.mod world tenv penv env state future)
    {x : VarId} (hvisible : x ∈ tenv.visible) (hdemanded : x ∈ future) :
    ∃ lv si v, env.vars[x]? = some lv ∧ env.scopes.lookup lv.scope = some si ∧
      slotRoot cx.fn fr x = pure (.local env.act si x) ∧
      state.store.roots[RootInst.local env.act si x]? = some v ∧
      Core.Sound.HasTy cfg.mod world.G state.store v lv.ty := by
  obtain ⟨lv, si, v, hvar, hscope, _, hroot, htype⟩ := hframe.vis x hvisible hdemanded
  refine ⟨lv, si, v, hvar, hscope, ?_, hroot, htype⟩
  rw [slotRoot_eq hrel]
  simp [rootOf, hvar, hscope]

theorem Rel.demanded_slot_read {cfg : Cfg} {world : Core.Sound.World} {tenv : TEnv} {penv : PEnv}
    {env : Env} {state : St} {future : List VarId} {cx : FnCtx} {fr : GIR.Frame} {ls : LS}
    (hrel : Rel cfg env cx fr ls)
    (hframe : Core.Sound.Frame cfg.mod world tenv penv env state future)
    {x : VarId} (hvisible : x ∈ tenv.visible) (hdemanded : x ∈ future) :
    ∃ v, (slotRoot cx.fn fr x >>= fun root => readLoc ⟨root, []⟩) state = .ok v state := by
  obtain ⟨lv, si, v, _, _, hslot, hroot, _⟩ := hrel.demanded_slot hframe hvisible hdemanded
  refine ⟨v, ?_⟩
  rw [hslot, pure_bind]
  simp [readLoc, Core.Sound.read_root hroot]

private theorem readRun_of_slice {state : St} {view : ViewVal} {element : Ty}
    (h : Core.Sound.SliceTy state.store view.loc view.start view.len element) :
    ∃ values, readRun view state = .ok values state := by
  obtain ⟨v, values, hread, helements, hbound, _⟩ := h
  cases v <;> simp only [Val.elems?] at helements
  all_goals
    cases helements <;>
      refine ⟨values.extract view.start (view.start + view.len), ?_⟩ <;>
      simp [readRun, readLoc, hread, hbound, bind_apply, pure_apply]

theorem SliceRunAliasAt.read_safe {m : Core.Module} {world : Core.Sound.World} {env : Env}
    {state : St} {fr : GIR.Frame} {value : ValueId} {alias : RetainedAlias}
    (h : SliceRunAliasAt m world env state.store fr value alias) :
    ∃ values, (getView fr value >>= readRun) state = .ok values state := by
  obtain ⟨view, mu, element, hcell, htype, halias⟩ := h
  have htyped := halias.1
  rw [htype] at htyped
  obtain ⟨loc, start, len, heq, _, hslice⟩ := htyped
  cases heq
  obtain ⟨values, hread⟩ := readRun_of_slice hslice
  refine ⟨values, ?_⟩
  rw [getView_of hcell, pure_bind]
  exact hread

theorem LimitedRunAliasAt.read_safe {m : Core.Module} {world : Core.Sound.World} {env : Env}
    {state : St} {fr : GIR.Frame} {value : ValueId} {alias : RetainedAlias}
    (h : LimitedRunAliasAt m world env state.store fr value alias) :
    ∃ values, (getView fr value >>= readRun) state = .ok values state := by
  obtain ⟨view, _, element, _, hcell, _, _, hslice⟩ := h
  obtain ⟨values, hread⟩ := readRun_of_slice hslice
  refine ⟨values, ?_⟩
  rw [getView_of hcell, pure_bind]
  exact hread

theorem RunAliasAt.read_safe {m : Core.Module} {world : Core.Sound.World} {env : Env}
    {state : St} {fr : GIR.Frame} {value : ValueId} {alias : RetainedAlias}
    (h : RunAliasAt m world env state.store fr value alias) :
    ∃ values, (getView fr value >>= readRun) state = .ok values state :=
  h.elim SliceRunAliasAt.read_safe LimitedRunAliasAt.read_safe

end Goose.Lower
