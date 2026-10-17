import Goose.Lower.TypedLists
import Goose.Lower.TypedTransfers
import Goose.Lower.FunctionTail
import Goose.GIR.Validate

namespace Goose.Lower.TypedTransferChecks

open Goose.Core Goose.GIR Goose.Proofs.Lower Goose.Core.Sound

def body : Core.Block := .mk 0 [.ret none 0] none

def implementation : Impl :=
  { name := "main", params := #[], results := #[], vars := #[], body := body,
    summary := .unknown }

def module (profile : ArtifactProfile) : Core.Module :=
  { profile := profile, files := #["typed-return.goose"], types := #[], globals := #[],
    impls := #[implementation], contexts := #[⟨0, "main", [], [], []⟩], entry := 0,
    origins := #[⟨0, 1, "return"⟩] }

def initialBuilder : LS := ⟨#[⟨[], #[]⟩], #[], some 0, [], #[]⟩

def initialFrame : GIR.Frame := { act := 0, scopes := [], depth := 1, vals := {} }

private theorem initialBuilder_generated : GeneratedBuilderState initialBuilder := by
  let le := lowerEnv (module .pilot) #[] []
  have newBlockRun : newBlock [] le initState =
      ((0, []), { initState with blocks := #[⟨[], #[]⟩] }) := by
    rw [newBlock0_run]
    simp [initState]
  have afterNew : GeneratedBuilderState { initState with blocks := #[⟨[], #[]⟩] } :=
    GeneratedBuilderState.initState.newBlock [] newBlockRun
  have blockBound : ∀ block, some 0 = some block →
      block < ({ initState with blocks := #[⟨[], #[]⟩] }).blocks.size := by
    intro block active
    have equal : block = 0 := Option.some.inj active.symm
    subst block
    simp
  have setCurrent : setCur (some 0) le { initState with blocks := #[⟨[], #[]⟩] } =
      ((), initialBuilder) := by
    rw [setCur_run]
    simp [initialBuilder, initState]
  simpa [initialBuilder] using afterNew.setCur (some 0) blockBound setCurrent

def loweredBody (profile : ArtifactProfile) : ValueId × LS :=
  lowerBlock none [] false body (lowerEnv (module profile) #[] []) initialBuilder

theorem body_simulation (fuel : Nat) (cfg : Cfg) :
    TypedBlockLoopSimulation fuel cfg [] none [] [] false body := by
  cases fuel with
  | zero => exact typedBlockLoopSimulation_zero cfg [] none [] [] false body
  | succ fuel =>
    apply typedBlockLoopSimulation_succ
    · cases fuel with
      | zero => exact typedStatementsLoopSimulation_zero cfg [] none _
      | succ fuel =>
        exact typedStatementsLoopSimulation_cons fuel cfg [] none (.ret none 0) []
          (typedStatementLoopSimulation_return_none fuel cfg [] none 0)
          (typedStatementsLoopSimulation_nil fuel cfg [] none)
    · trivial

theorem accepted_return_body (artifact : ArtifactProfile) (profile : NumProfile) (fuel : Nat)
    (accepted : Core.validate (module artifact) = .ok ()) :
    SimEAt ⟨⟨profile, lower (module artifact)⟩, lowerContextAt (module artifact) ⟨0, "main", [], [], []⟩ implementation⟩
      (0, 0) initialFrame
      (execBlock fuel ⟨profile, module artifact⟩ ⟨#[], 0, [], 1⟩ [] body >>=
        prepareReturn ⟨#[], 0, [], 1⟩)
      (BlockFlowPost ⟨profile, module artifact⟩ ⟨#[], 0, [], 1⟩
        ⟨⟨profile, lower (module artifact)⟩, lowerContextAt (module artifact) ⟨0, "main", [], [], []⟩ implementation⟩
        initialBuilder initialFrame (loweredBody artifact).2 body false
        (loweredBody artifact).1) { St.initial with nextAct := 1 } := by
  obtain ⟨context, impl, hcontext, himpl, hparams, hresults, source, htyping, hroots⟩ :=
    acceptedEntryAfterGlobals (cfg := ⟨profile, module artifact⟩) accepted 1 (by rfl)
  have hcontextEq : context = ⟨0, "main", [], [], []⟩ := by
    simpa [module] using hcontext.symm
  subst context
  have himplEq : impl = implementation := by simpa [module] using himpl.symm
  subst impl
  have hmetadata : SourceResults source.typingEnv source.rootsEnv [] := by
    intro impl hselected
    have hselectedEq : impl = implementation := by
      simpa [htyping, implEnv] using hselected.symm
    subst impl
    exact ⟨by rw [hroots], rfl⟩
  have hloops : source.typingEnv.loops = 0 := by rw [htyping]; rfl
  apply (body_simulation fuel ⟨profile, module artifact⟩).function _ _ source hmetadata hloops
    initialBuilder (loweredBody artifact).2 (loweredBody artifact).1 (0, 0)
    ⟨⟨profile, lower (module artifact)⟩, lowerContextAt (module artifact) ⟨0, "main", [], [], []⟩ implementation⟩
    initialFrame
  · exact (Prod.eta (loweredBody artifact)).symm
  · rfl
  · change ExtT (loweredBody artifact).2 (finishBlocks (loweredBody artifact).2.blocks)
    exact extT_finish _
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · trivial
  · rfl
  · rfl
  · exact initialBuilder_generated

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  match Core.validate (module artifact), GIR.validate (lower (module artifact)) with
  | .ok _, .ok _ => true
  | _, _ => false

#guard [ArtifactProfile.pilot, .shrink].all fun artifact =>
  [NumProfile.release, .debug].all fun profile =>
    match Core.eval 10 profile (module artifact), GIR.run 20 profile (lower (module artifact)) with
    | .done .returned "", .done .returned "" => true
    | _, _ => false

end Goose.Lower.TypedTransferChecks
