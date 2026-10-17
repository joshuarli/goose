import Goose.Lower.Validation.SummaryPreservationEffectRefinement

namespace Goose.Lower.Validation.SummaryPreservation

open Goose.Core Goose.Core.Sound Goose.GIR

theorem effectRefinement_before_of_replay {func : Func} {action : P α}
    {before after : RState} {result : α} {target : Core.Eff}
    (mono : PMono action) (rebinds : PMonoRebinds action) (flags : PFlagsMono action)
    (run : action before = .ok (result, after))
    (bound : EffectRefinement func after.eff target) :
    EffectRefinement func before.eff target :=
  ((EffectRefinement.refl func before.eff).source_mono
    (mono before result after run).2 (rebinds before result after run)
    (flags before result after run)).trans bound

theorem effectRefinement_before_expression {func : Func} {env : PEnv} {expression : Expr}
    {before after : RState} {roots : List RootRef} {target : Core.Eff}
    (run : rpExpr env expression before = .ok (roots, after))
    (bound : EffectRefinement func after.eff target) :
    EffectRefinement func before.eff target :=
  effectRefinement_before_of_replay (rp_mono_all.2.2.1 env expression)
    (rp_rebinds_mono_all.2.2.1 env expression) (rp_flags_mono_all.2.2.1 env expression) run bound

end Goose.Lower.Validation.SummaryPreservation
