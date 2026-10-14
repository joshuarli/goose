import Goose.Lower.Claims

namespace Goose.Lower

open Goose.Core Goose.GIR

def releaseScopes (env : Env) : List (ScopeId × ScopeInst) → M Unit
  | [] => pure ()
  | (scope, scopeInstance) :: rest => do
    Core.releaseScope env scope scopeInstance
    releaseScopes env rest

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
