import Goose.Core.Sound.Frame

namespace Goose.Core.Sound
open Goose.Proofs.Memory

theorem Frame.fixedArrayRoot_rejectsResizableValue
    {m : Module} {W : World} {tenv : TEnv} {penv : PEnv} {env : Env} {s : St}
    {future : List VarId} {x : VarId} {lv : LocalVar} {si : ScopeInst}
    {E : Ty} {count : Nat} {elements : Array Val}
    (h : Frame m W tenv penv env s future)
    (hvar : env.vars[x]? = some lv)
    (hlk : env.scopes.lookup lv.scope = some si)
    (hty : lv.ty = .arr E count)
    (hroot : s.store.roots[RootInst.local env.act si x]? = some (.resizable E elements)) :
    False := by
  have hnonref : lv.ty.isRefLike = false := by rw [hty]; rfl
  have hstorage : StorageRootTypes env (RootInst.local env.act si x) lv.ty :=
    ⟨x, lv, si, hvar, hlk, rfl, hnonref, rfl⟩
  have hloc := h.storage _ _ hstorage (.resizable E elements) hroot
  obtain ⟨value, hread, hflat⟩ := hloc
  obtain ⟨stored, hstored, hget⟩ := (read_ok_iff _ _ _).1 hread
  rw [get_nil] at hget
  cases hget
  have hstored' : s.store.roots[RootInst.local env.act si x]? = some value := by
    simpa using hstored
  have hvalue : value = .resizable E elements := Option.some.inj (hstored'.symm.trans hroot)
  rw [hty, hvalue] at hflat
  simp [FlatTy] at hflat

end Goose.Core.Sound
