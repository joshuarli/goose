import Goose.Lower.EachTyped
import Goose.Core.Sound.StepLoop

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Core.Sound Goose.Proofs.Memory

theorem eachIteration_block_success {n : Nat} {cfg : Cfg} {env : Env} {x : VarId}
    {idx : Option VarId} {byRef : Bool} {block : Core.Block} {vw : ViewVal} {i : Nat}
    {s state : St} {flow : Flow} {element : Ty}
    (hloc : LocTy s.store ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩ element)
    (hadvance : (∃ value, flow = .normal value) ∨ flow = .cont)
    (hsource : eachIterationCore n cfg env x idx byRef block vw i s = .ok flow state) :
    ∃ value,
      (if byRef then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
        else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) s = .ok value s ∧
      execBlock n cfg env (eachCorePre x idx value i) block s = .ok flow state := by
  obtain ⟨value, helement⟩ : ∃ value,
      (if byRef then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
        else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) s = .ok value s := by
    cases byRef with
    | true => exact ⟨_, rfl⟩
    | false =>
      obtain ⟨value, hread, _⟩ := hloc
      exact ⟨value, by simp [readLoc, hread]⟩
  refine ⟨value, helement, ?_⟩
  unfold eachIterationCore at hsource
  change M.bind' _ (fun ev => M.bind' (execBlock n cfg env (eachCorePre x idx ev i) block)
    (prepareReturn env)) s = .ok flow state at hsource
  simp only [M.bind', helement] at hsource
  cases hbody : execBlock n cfg env (eachCorePre x idx value i) block s with
  | stop reason bodyState => simp only [hbody] at hsource; cases hsource
  | ok bodyFlow bodyState =>
    simp only [hbody] at hsource
    cases bodyFlow with
    | normal bodyValue | cont | brk =>
      simp only [prepareReturn, pure_apply] at hsource
      exact hsource
    | ret bodyValue =>
      rcases hadvance with ⟨v, rfl⟩ | rfl
      all_goals
        unfold prepareReturn at hsource
        change M.bind' _ (fun _ => pure (Flow.ret bodyValue)) bodyState = _ at hsource
        cases hrelease : releaseScopes env env.scopes bodyState <;>
          simp only [M.bind', hrelease, pure_apply] at hsource <;> cases hsource

theorem eachIteration_retained_view {n : Nat} {m : Core.Module} {profile : NumProfile}
    {env : Env} {penv : PEnv} {world : World} {x : VarId} {idx : Option VarId}
    {byRef : Bool} {block : Core.Block} {source : View} {vw : ViewVal} {i : Nat}
    {s state : St} {flow : Flow} {element : Ty} {path : List Nat}
    {aliases : List RetainedAlias} {alias : RetainedAlias}
    (hview : EachViewOk s.store vw element)
    (hsourceAliases : ViewAliases m world penv env s.store source vw element)
    (hloc : LocTy s.store ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩ element)
    (hquery : EachAliasQuery penv.access path source alias) (hmember : alias ∈ aliases)
    (hblock : ∀ value,
      (if byRef then pure (Val.ref ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩)
        else readLoc ⟨vw.loc.root, vw.loc.path ++ [vw.start + i]⟩) s = .ok value s →
      Sat (execBlock n ⟨profile, m⟩ env (eachCorePre x idx value i) block) s
        (fun _ state => RetainsAliases m world env s.store state.store aliases))
    (hadvance : (∃ value, flow = .normal value) ∨ flow = .cont)
    (hsuccess : eachIterationCore n ⟨profile, m⟩ env x idx byRef block vw i s = .ok flow state) :
    EachViewOk state.store vw element ∧ ViewAliases m world penv env state.store source vw element := by
  obtain ⟨value, helement, hbody⟩ := eachIteration_block_success hloc hadvance hsuccess
  have hretained := hblock value helement
  unfold Sat at hretained
  rw [hbody] at hretained
  exact eachViewAfterBody hview hsourceAliases (hretained alias hmember) hquery

end Goose.Lower
