import Goose.GIR.Eval
import Goose.Proofs.Fuel

namespace Goose.Proofs.GIRFuel

open Goose.Core Goose.GIR Goose.Proofs.Fuel

private structure MonoG (n k : Nat) : Prop where
  call : ∀ cfg depth f vals, MonoM (callFn n cfg depth f vals) (callFn k cfg depth f vals)
  enter : ∀ cfg depth fn vals, MonoM (enterFn n cfg depth fn vals) (enterFn k cfg depth fn vals)
  exec : ∀ cx fr insts, MonoM (exec n cx fr insts) (exec k cx fr insts)
  op : ∀ cx fr instr, MonoM (execOp n cx fr instr) (execOp k cx fr instr)

private theorem op_step (n k : Nat) (ih : MonoG n k) (cx : FnCtx) (fr : Frame) (op : Op) :
    MonoM (execOp (n + 1) cx fr op) (execOp (k + 1) cx fr op) := by
  cases op with
  | call f args org =>
    simp only [execOp]
    refine MonoM.bind (MonoM.mapList (fun _ => MonoM.refl _) args) ?_
    intro vals
    exact MonoM.bind (ih.call cx.cfg fr.depth f vals) (fun v => MonoM.refl _)
  | _ => simp only [execOp]; exact MonoM.refl _

private theorem jump_mono {n k : Nat} (ih : MonoG n k)
    (cx : FnCtx) (fr : Frame) (b : BlockId) (args : List ValueId) :
    MonoM
      (do let vals ← mapList (getCell fr) args
          let (insts, fr') ← enterBlock cx.fn fr b vals
          exec n cx fr' insts)
      (do let vals ← mapList (getCell fr) args
          let (insts, fr') ← enterBlock cx.fn fr b vals
          exec k cx fr' insts) := by
  refine MonoM.bind (MonoM.mapList (fun _ => MonoM.refl _) args) ?_
  intro vals
  refine MonoM.bind (MonoM.refl _) ?_
  intro pair
  exact ih.exec cx pair.2 pair.1

private theorem step (n k : Nat) (ih : MonoG n k) : MonoG (n + 1) (k + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cfg depth f vals
    by_cases hd : depth ≥ maxCallDepth
    · simp [callFn, hd]
      exact MonoM.timeout _
    · simp only [callFn, hd, ↓reduceIte]
      exact MonoM.bind (MonoM.refl _) (fun fn => ih.enter cfg (depth + 1) fn vals)
  · intro cfg depth fn vals
    by_cases hp : fn.params.length = vals.length
    · simp only [enterFn, hp, ↓reduceIte]
      refine MonoM.bind (MonoM.refl _) ?_
      intro act
      refine MonoM.bind (MonoM.refl _) ?_
      intro pair
      exact ih.exec ⟨cfg, fn⟩ pair.2 pair.1
    · simp [enterFn, hp]
      exact MonoM.refl _
  · intro cx fr insts
    cases insts with
    | nil => simp only [exec]; exact MonoM.refl _
    | cons i rest =>
      cases i with
      | «def» r op =>
        simp only [exec]
        exact MonoM.bind (ih.op cx fr op) (fun x =>
          MonoM.bind (MonoM.refl _) (fun fr' => ih.exec cx fr' rest))
      | eff e =>
        simp only [exec]
        exact MonoM.bind (MonoM.refl _) (fun fr' => ih.exec cx fr' rest)
      | term t =>
        cases t with
        | br b args =>
          simp only [exec]
          exact jump_mono ih cx fr b args
        | condbr c tb targs eb eargs =>
          simp only [exec]
          refine MonoM.bind (MonoM.refl _) ?_
          intro value
          refine MonoM.bind (MonoM.refl _) ?_
          intro cond
          cases cond with
          | true => exact jump_mono ih cx fr tb targs
          | false => exact jump_mono ih cx fr eb eargs
        | ret vs org => simp only [exec]; exact MonoM.refl _
        | abort kind org => simp only [exec]; exact MonoM.refl _
        | exit v org => simp only [exec]; exact MonoM.refl _
        | unreachable => simp only [exec]; exact MonoM.refl _
  · intro cx fr op
    exact op_step n k ih cx fr op

private theorem zero (k : Nat) : MonoG 0 k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros; simp only [callFn]; exact MonoM.timeout _
  · intros; simp only [enterFn]; exact MonoM.timeout _
  · intros; simp only [exec]; exact MonoM.timeout _
  · intro cx fr op
    cases op with
    | call f args org => simp only [execOp]; exact MonoM.timeout _
    | _ => simp only [execOp]; exact MonoM.refl _

private theorem all : ∀ (n k : Nat), n ≤ k → MonoG n k
  | 0, k, _ => zero k
  | n + 1, 0, h => absurd h (by omega)
  | n + 1, k + 1, h => step n k (all n k (by omega))

private theorem initGlobals_mono (n k : Nat) (h : MonoG n k) (cfg : GCfg)
    (gs : List GlobalId) :
    MonoM (Goose.GIR.initGlobals n cfg gs) (Goose.GIR.initGlobals k cfg gs) := by
  induction gs with
  | nil => simp only [Goose.GIR.initGlobals]; exact MonoM.refl _
  | cons g rest ih =>
    simp only [Goose.GIR.initGlobals]
    refine MonoM.bind (MonoM.refl _) ?_
    intro init
    refine MonoM.bind (h.enter cfg 0 init []) ?_
    intro v
    refine MonoM.bind (MonoM.refl _) ?_
    intro _
    exact ih

private theorem runModule_mono (n k : Nat) (h : n ≤ k) (cfg : GCfg) :
    MonoM (Goose.GIR.runModule n cfg) (Goose.GIR.runModule k cfg) := by
  have H := all n k h
  simp only [Goose.GIR.runModule]
  refine MonoM.bind (initGlobals_mono n k H cfg _) ?_
  intro _
  refine MonoM.bind (H.call cfg 0 cfg.mod.entry []) ?_
  intro _
  exact MonoM.refl _

/-- Every non-timeout GIR result is unchanged when the fuel increases. -/
theorem run_nonTimeout_fuel_mono (n k : Nat) (p : NumProfile) (m : Goose.GIR.Module)
    (hk : n ≤ k)
    (h : ∀ t, Goose.GIR.run n p m ≠ .timeout t) :
    Goose.GIR.run k p m = Goose.GIR.run n p m := by
  have A := runModule_mono n k hk ⟨p, m⟩
  unfold Goose.GIR.run
  cases hr : Goose.GIR.runModule n ⟨p, m⟩ St.initial with
  | ok a s =>
    rw [(A St.initial).1 a s hr]
  | stop e s =>
    cases e with
    | abort _ _ =>
      rw [(A St.initial).2 _ s hr |>.resolve_left (by simp [isTimeout])]
    | exit _ =>
      rw [(A St.initial).2 _ s hr |>.resolve_left (by simp [isTimeout])]
    | fault _ =>
      rw [(A St.initial).2 _ s hr |>.resolve_left (by simp [isTimeout])]
    | timeout =>
      exact (h s.trace (by simp [Goose.GIR.run, hr])).elim

end Goose.Proofs.GIRFuel
