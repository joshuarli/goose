import Goose.Lower.Validation.CfgSourceDominanceStatements

namespace Goose.Lower.Validation

open Goose.Core Goose.GIR

theorem ssa_whileStmt (loop : Option LoopCtx) (origin : OriginId) {condition : Expr} {body : Core.Block}
    (conditionSource : SSARun loop [] (fun result => [result]) (lowerExpr condition))
    (bodySource : ∀ depth exit header, SSARun (some ⟨depth, exit, .jump header⟩) [] (fun _ => [])
      (lowerBlock (some ⟨depth, exit, .jump header⟩) [] false body)) :
    LiveSSARun loop [] (fun _ => []) (lowerStmt loop (.while condition body origin)) := by
  exact ssa_header0 loop fun header => ssa_lowerWhile loop header [] conditionSource
    (fun depth exit => bodySource depth exit header)

theorem ssa_rangeStmt (loop : Option LoopCtx) (slot : SlotId) (origin : OriginId)
    {lo hi : Expr} {body : Core.Block}
    (loSource : SSARun loop [] (fun result => [result]) (lowerExpr lo))
    (hiSource : SSARun loop [] (fun result => [result]) (lowerExpr hi))
    (bodySource : ∀ depth exit header type counter,
      SSARun (some ⟨depth, exit, .next header type counter⟩) [counter] (fun _ => [])
        (lowerBlock (some ⟨depth, exit, .next header type counter⟩) [(slot, counter, origin)] false body)) :
    SSARun loop [] (fun _ => []) (lowerStmt loop (.forRange slot lo hi body origin)) := by
  refine loSource.bind fun start => ?_
  refine (hiSource.keep [start]).bind fun bound => ?_
  apply ssa_whenLive_live
  refine LiveSSARun.bind_current ((ssa_intTyOf loop start).keep [start, bound])
    (fun env state => congrArg LS.cur (intTyOf_eq (v := start) (le := env) (ls := state) rfl)) fun type => ?_
  exact ssa_header1 loop type start [bound] fun header counter =>
    ssa_lowerRange loop type counter bound header [] (fun depth exit => bodySource depth exit header type counter)

theorem ssa_eachPreparation (loop : Option LoopCtx) (regrow : Bool) (owner : Option ValueId) (view : ValueId)
    (present : regrow = true → owner.isSome = true) :
    SSARun loop (owner.toList ++ [view]) (fun sampled => [view] ++ eachCountInputs regrow owner sampled)
      (eachSampled regrow view) := by
  cases regrow with
  | false =>
    exact ((ssa_emitDef loop (.viewLen view)).keep [view]).weaken
      (by simp [Op.uses, List.subset_def])
  | true =>
    apply SSARun.pure
    cases owner with
    | none => simp at present
    | some owner => simp [eachCountInputs, List.subset_def, or_comm]

theorem ssa_eachBody (depth exit header counter view : Nat) (slot : SlotId) (index : Option VarId)
    (byRef : Bool) (origin : OriginId) {body : Core.Block}
    (bodySource : ∀ value, SSARun (some ⟨depth, exit, .next header .i64 counter⟩)
      (((slot, value, origin) :: (match index with | some j => [(j, counter, origin)] | none => [])).map fun entry => entry.2.1)
      (fun _ => []) (lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
        ((slot, value, origin) :: (match index with | some j => [(j, counter, origin)] | none => [])) false body)) :
    SSARun (some ⟨depth, exit, .next header .i64 counter⟩) [counter, view] (fun _ => []) (do
      let elem ← emitDef (.refElem view counter)
      let value ← eachElemValue slot byRef elem
      lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
        ((slot, value, origin) :: (match index with | some j => [(j, counter, origin)] | none => [])) false body) := by
  cases index <;>
    (let loop : Option LoopCtx := some ⟨depth, exit, .next header .i64 counter⟩
     refine (((ssa_emitDef loop (.refElem view counter)).keep [counter]).weaken
       (more := [counter, view]) (by simp [Op.uses, List.subset_def, or_comm])).bind fun elem => ?_
     refine ((ssa_eachElemValue loop slot byRef elem).keep [counter]).bind fun value => ?_
     exact (bodySource value).weaken (more := [counter, value]) (by simp [List.subset_def, or_comm]))

theorem ssa_eachCore (loop : Option LoopCtx) (regrow : Bool) (owner : Option ValueId) (view : ValueId)
    (present : regrow = true → owner.isSome = true) {body : Nat → Nat → Nat → Nat → B ValueId}
    (bodySource : ∀ header counter depth exit,
      SSARun (some ⟨depth, exit, .next header .i64 counter⟩) [counter, view] (fun _ => [])
        (body header counter depth exit)) :
    SSARun loop (owner.toList ++ [view]) (fun _ => []) (do
      let sampled ← eachSampled regrow view
      let start ← emitDef (.constInt .i64 0)
      whenLive () fun _ => do
        let (header, params) ← newBlock [.data (.int .i64)]
        let counter := params.headD 0
        emitTerm (.br header [start])
        setCur (some header)
        lowerEach regrow owner sampled header counter (body header counter)) := by
  refine (ssa_eachPreparation loop regrow owner view present).bind fun sampled => ?_
  let saved := [view] ++ eachCountInputs regrow owner sampled
  refine (show SSARun loop saved (fun start => saved ++ [start]) (emitDef (.constInt .i64 0)) from
    by simpa only [Op.uses, List.append_nil] using (ssa_emitDef loop (.constInt .i64 0)).keep saved).bind fun start => ?_
  apply ssa_whenLive_live
  have source := ssa_header1 loop .i64 start saved fun header counter =>
    ssa_lowerEach loop regrow owner sampled header counter [view] (fun depth exit => bodySource header counter depth exit)
  intro env before result after run imports checked ready arguments live
  exact source env before result after run imports checked ready
    (arguments.subset (by simp [List.subset_def, or_comm])) live

theorem ssa_eachStmt (loop : Option LoopCtx) (slot : SlotId) (index : Option VarId)
    (byRef : Bool) (origin : OriginId) {view : View} {body : Core.Block}
    (source : SSARun loop [] (fun result => result.1.toList ++ [result.2]) (lowerEachSource view))
    (bodySource : ∀ depth exit header counter value,
      SSARun (some ⟨depth, exit, .next header .i64 counter⟩)
        (((slot, value, origin) :: (match index with | some j => [(j, counter, origin)] | none => [])).map fun entry => entry.2.1)
        (fun _ => []) (lowerBlock (some ⟨depth, exit, .next header .i64 counter⟩)
          ((slot, value, origin) :: (match index with | some j => [(j, counter, origin)] | none => [])) false body)) :
    SSARun loop [] (fun _ => []) (lowerStmt loop (.forEach slot index view byRef body origin)) := by
  cases index with
  | none =>
    refine source.bind fun pair => ?_
    rcases pair with ⟨owner, value⟩
    have bodyChecked := fun header counter depth exit =>
      ssa_eachBody depth exit header counter value slot none byRef origin
        (body := body) (bodySource depth exit header counter)
    intro env before result after run imports checked ready arguments
    obtain ⟨regrow, prepared, regrowRun, tailRun⟩ := bind_eq.mp run
    obtain ⟨preparedImports, regrown⟩ := ssa_regrowOf loop owner env before regrow prepared regrowRun
      imports checked ready (by simp [AvailableValues])
    have present : regrow = true → owner.isSome = true := by
      cases owner with
      | none => obtain ⟨rfl, _⟩ := pure_eq.mp regrowRun; simp
      | some _ => simp
    obtain ⟨nextImports, finished⟩ := ssa_eachCore loop regrow owner value present bodyChecked env prepared
      result after tailRun preparedImports regrown.checked (regrown.loop ready) (regrown.frame _ arguments)
    exact ⟨nextImports, regrown.trans finished⟩
  | some index =>
    refine source.bind fun pair => ?_
    rcases pair with ⟨owner, value⟩
    have bodyChecked := fun header counter depth exit =>
      ssa_eachBody depth exit header counter value slot (some index) byRef origin
        (body := body) (bodySource depth exit header counter)
    intro env before result after run imports checked ready arguments
    obtain ⟨regrow, prepared, regrowRun, tailRun⟩ := bind_eq.mp run
    obtain ⟨preparedImports, regrown⟩ := ssa_regrowOf loop owner env before regrow prepared regrowRun
      imports checked ready (by simp [AvailableValues])
    have present : regrow = true → owner.isSome = true := by
      cases owner with
      | none => obtain ⟨rfl, _⟩ := pure_eq.mp regrowRun; simp
      | some _ => simp
    obtain ⟨nextImports, finished⟩ := ssa_eachCore loop regrow owner value present bodyChecked env prepared
      result after tailRun preparedImports regrown.checked (regrown.loop ready) (regrown.frame _ arguments)
    exact ⟨nextImports, regrown.trans finished⟩

end Goose.Lower.Validation
