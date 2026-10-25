import Goose.Lower.Leaf
import Goose.Proofs.Memory

namespace Goose.Lower

open Goose.Core Goose.GIR

def releaseScopes (env : Env) : List (ScopeId × ScopeInst) → M Unit
  | [] => pure ()
  | (scope, scopeInstance) :: rest => do
    Core.releaseScope env scope scopeInstance
    releaseScopes env rest

theorem releaseScope_same_activation {env env' : Env} (hvars : env.vars = env'.vars)
    (hact : env.act = env'.act) (scope : ScopeId) (scopeInstance : ScopeInst) :
    Core.releaseScope env scope scopeInstance = Core.releaseScope env' scope scopeInstance := by
  funext state
  simp only [Core.releaseScope, hvars, hact]

theorem releaseScopes_same_activation {env env' : Env} (hvars : env.vars = env'.vars)
    (hact : env.act = env'.act) (scopes : List (ScopeId × ScopeInst)) :
    releaseScopes env scopes = releaseScopes env' scopes := by
  induction scopes with
  | nil => rfl
  | cons scope rest ih =>
    simp only [releaseScopes, releaseScope_same_activation hvars hact scope.1 scope.2, ih]

theorem releaseScopes_entered (env : Env) (scope : ScopeId) (scopeInstance : ScopeInst) :
    releaseScopes { env with scopes := (scope, scopeInstance) :: env.scopes }
      ((scope, scopeInstance) :: env.scopes) =
    (Core.releaseScope env scope scopeInstance >>= fun _ => releaseScopes env env.scopes) := by
  rw [releaseScopes_same_activation
    (env := { env with scopes := (scope, scopeInstance) :: env.scopes }) (env' := env) rfl rfl]
  rfl

private theorem erase_absent (map : Std.HashMap RootInst Val) (root : RootInst)
    (h : map.contains root = false) : map.erase root = map := by
  cases map with
  | mk inner =>
    cases inner with
    | mk raw wf =>
      cases raw with
      | mk size buckets =>
        simp only [Std.HashMap.contains, Std.DHashMap.contains,
          Std.DHashMap.Internal.Raw₀.contains] at h
        simp only [Std.HashMap.erase, Std.DHashMap.erase,
          Std.DHashMap.Internal.Raw₀.erase]
        simp only [h, Bool.false_eq_true, ite_false]

theorem store_release_absent (store : Store) (root : RootInst) (h : store.roots[root]? = none) :
    store.release root = store := by
  have hcontains : store.roots.contains root = false := by
    simp [Std.HashMap.contains_eq_isSome_getElem?, h]
  cases store
  simp only [Store.release, Store.mk.injEq]
  exact erase_absent _ _ hcontains

theorem releaseVars_absent (vars : Array LocalVar) (act : ActId) (sc : Nat) (si : ScopeInst)
    (count : Nat) (store : Store)
    (h : ∀ root, Goose.Proofs.Memory.ScopeRoots vars act sc si root → store.roots[root]? = none) :
    releaseVars vars act sc si count store = store := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [releaseVars]
    cases hv : vars[count]? with
    | none => exact ih
    | some lv =>
      by_cases hs : lv.scope = sc
      · simp only [hs, beq_self_eq_true, ite_true]
        rw [store_release_absent store (.local act si count) (h _ ⟨count, lv, hv, hs, rfl⟩)]
        exact ih
      · simp only [beq_eq_false_iff_ne.mpr hs, Bool.false_eq_true, ite_false]
        exact ih

theorem releaseVars_idempotent (vars : Array LocalVar) (act : ActId) (sc : Nat) (si : ScopeInst)
    (store : Store) :
    releaseVars vars act sc si vars.size (releaseVars vars act sc si vars.size store) =
      releaseVars vars act sc si vars.size store := by
  exact releaseVars_absent vars act sc si vars.size _
    (Goose.Proofs.Memory.releaseScope_roots vars act sc si store).2

theorem releaseScope_idempotent (env : Env) (sc : Nat) (si : ScopeInst) :
    (Core.releaseScope env sc si >>= fun _ => Core.releaseScope env sc si) =
      Core.releaseScope env sc si := by
  funext state
  change Res.ok () { state with store := (releaseVars env.vars env.act sc si env.vars.size
      (releaseVars env.vars env.act sc si env.vars.size state.store)) } =
    Res.ok () { state with store := releaseVars env.vars env.act sc si env.vars.size state.store }
  rw [releaseVars_idempotent]

theorem releaseVars_preserves_absence (vars : Array LocalVar) (act : ActId) (sc : Nat)
    (si : ScopeInst) (count : Nat) (store : Store) (root : RootInst)
    (h : store.roots[root]? = none) :
    (releaseVars vars act sc si count store).roots[root]? = none := by
  rw [Goose.Proofs.Memory.releaseVars_roots]
  split <;> simp [h]

theorem releaseScopes_result (env : Env) (scopes : List (ScopeId × ScopeInst)) (state : St) :
    ∃ after, releaseScopes env scopes state = .ok () after ∧
      (∀ (root : RootInst), state.store.roots[root]? = none → after.store.roots[root]? = none) ∧
      (∀ scope ∈ scopes, ∀ (root : RootInst), Goose.Proofs.Memory.ScopeRoots env.vars env.act scope.1 scope.2 root →
        after.store.roots[root]? = none) := by
  induction scopes generalizing state with
  | nil => exact ⟨state, rfl, fun _ h => h, by simp⟩
  | cons scope rest ih =>
    let middle : St := { state with store :=
      (releaseVars env.vars env.act scope.1 scope.2 env.vars.size state.store) }
    obtain ⟨after, hrest, hmissing, hremoved⟩ := ih middle
    refine ⟨after, ?_, ?_, ?_⟩
    · simp [releaseScopes, Core.releaseScope, middle, bind_apply, hrest]
    · intro root hroot
      exact hmissing root (releaseVars_preserves_absence _ _ _ _ _ _ root hroot)
    · intro released hreleased root hroot
      rcases List.mem_cons.mp hreleased with rfl | hreleased
      · exact hmissing root
          ((Goose.Proofs.Memory.releaseScope_roots env.vars env.act released.1 released.2 state.store).2
            root hroot)
      · exact hremoved released hreleased root hroot

theorem releaseScopes_repeat (env : Env) (scopes : List (ScopeId × ScopeInst))
    (scope : ScopeId × ScopeInst) (hscope : scope ∈ scopes) :
    (releaseScopes env scopes >>= fun _ => Core.releaseScope env scope.1 scope.2) =
      releaseScopes env scopes := by
  funext state
  obtain ⟨after, hrun, _, hremoved⟩ := releaseScopes_result env scopes state
  rw [bind_apply, hrun]
  change Res.ok () { after with store :=
    (releaseVars env.vars env.act scope.1 scope.2 env.vars.size after.store) } = .ok () after
  rw [releaseVars_absent env.vars env.act scope.1 scope.2 env.vars.size after.store
    (hremoved scope hscope)]

theorem releaseScopes_repeat_subset (env : Env) (scopes repeated : List (ScopeId × ScopeInst))
    (hsubset : ∀ scope ∈ repeated, scope ∈ scopes) :
    (releaseScopes env scopes >>= fun _ => releaseScopes env repeated) = releaseScopes env scopes := by
  induction repeated with
  | nil => simp [releaseScopes, bind_pure]
  | cons scope rest ih =>
    simp only [releaseScopes]
    rw [← bind_assoc, releaseScopes_repeat env scopes scope (hsubset scope (by simp))]
    exact ih (fun scope hscope => hsubset scope (by simp [hscope]))

structure UnwindPost (ls : LS) (fr : GIR.Frame) (ls' : LS) (fr' : GIR.Frame)
    (suffix : List (ScopeId × ScopeInst)) (pt : Pt) : Prop where
  pp : ls'.pp = some pt
  values : fr'.vals = fr.vals
  activation : fr'.act = fr.act
  scopes : fr'.scopes = suffix
  depth : fr'.depth = fr.depth
  builderValues : ls'.vals = ls.vals
  lexicalStack : ls'.stack = ls.stack

theorem leaveAll_sim (env : Env) (cx : FnCtx)
    (hslots : cx.fn.slots = env.vars.mapIdx fun i lv => ⟨lv.ty, lv.kind, lv.scope, i⟩)
    (entered suffix : List (ScopeId × ScopeInst)) (le : LEnv) (ls ls' : LS) (r : Unit)
    (pt : Pt) (fr : GIR.Frame) (hact : fr.act = env.act)
    (hscopes : fr.scopes = entered ++ suffix)
    (hlow : leaveAll (entered.map Prod.fst) le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) :
    SimG cx pt fr (releaseScopes env entered)
      (fun _ pt' fr' => UnwindPost ls fr ls' fr' suffix pt') := by
  induction entered generalizing ls ls' r pt fr with
  | nil =>
    rw [List.map_nil, leaveAll, pure_run] at hlow
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hlow
    simp only [releaseScopes]
    exact SimG.ret ⟨hpp, rfl, rfl, by simpa using hscopes, rfl, rfl, rfl⟩
  | cons scope rest ih =>
    obtain ⟨sc, si⟩ := scope
    simp only [List.map_cons, leaveAll, bind_eq] at hlow
    obtain ⟨u, middle, hleave, hrest⟩ := hlow
    have hextMiddle := hext.of_adv (advB_leaveAll (rest.map Prod.fst) le middle r ls' hrest)
    obtain ⟨hvalSize, hstack, hppMiddle, hinst⟩ := emitEffect_facts hleave hpp hextMiddle
    have hvalues : middle.vals = ls.vals := by
      obtain ⟨_, hcur, _, _⟩ := LS.pp_some hpp
      rw [emitEffect_run _ _ hcur] at hleave
      obtain ⟨_, rfl⟩ := Prod.mk.inj hleave
      rfl
    have hrelease : GIR.releaseScope cx.fn fr.act sc si = Core.releaseScope env sc si := by
      funext state
      have hsize : cx.fn.slots.size = env.vars.size := by rw [hslots]; simp
      simp only [GIR.releaseScope, Core.releaseScope, hact, hsize]
      rw [releaseSlots_eq hslots]
    let after : GIR.Frame := { fr with scopes := rest ++ suffix }
    have heffect : execEff cx.fn fr (.leave sc) =
        Core.releaseScope env sc si >>= fun _ => pure after := by
      simp only [execEff, hscopes, List.cons_append, ↓reduceIte]
      rw [hrelease]
    simp only [releaseScopes]
    refine SimG.bind (SimG.eff_step (fun _ => after) hinst heffect)
      fun _ ptMiddle frMiddle ⟨hpt, hframe⟩ => ?_
    subst hpt
    subst hframe
    have hnext := ih middle ls' r (pt.1, pt.2 + 1) after hact rfl hrest hppMiddle hext
    refine hnext.mono fun _ pt' fr' hpost => ?_
    exact ⟨hpost.pp, hpost.values, hpost.activation, hpost.scopes, hpost.depth,
      hpost.builderValues.trans hvalues, hpost.lexicalStack.trans hstack⟩

theorem leaveTo_sim (cfg : Cfg) (env : Env) (cx : FnCtx) (le : LEnv)
    (depth : Nat) (ls ls' : LS) (r : Unit) (pt : Pt) (fr : GIR.Frame)
    (hrel : Rel cfg env cx fr ls)
    (hlow : leaveTo depth le ls = (r, ls'))
    (hpp : ls.pp = some pt) (hext : ExtT ls' cx.fn.blocks) :
    SimG cx pt fr
      (releaseScopes env (env.scopes.take (env.scopes.length - depth)))
      (fun _ pt' fr' => UnwindPost ls fr ls' fr'
        (env.scopes.drop (env.scopes.length - depth)) pt') := by
  simp only [leaveTo, bind_run, get_apply] at hlow
  have hstack : ls.stack.take (ls.stack.length - depth) =
      (env.scopes.take (env.scopes.length - depth)).map Prod.fst := by
    rw [hrel.stack, List.length_map, List.map_take]
  rw [hstack] at hlow
  apply leaveAll_sim env cx hrel.slots
    (env.scopes.take (env.scopes.length - depth))
    (env.scopes.drop (env.scopes.length - depth)) le ls ls' r pt fr hrel.act
      (by simpa using hrel.scopes) hlow hpp hext

end Goose.Lower
