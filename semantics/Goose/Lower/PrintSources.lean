import Goose.Lower.SourceContexts

namespace Goose.Lower

open Goose.Core Goose.Proofs.Memory
open Goose.Core.Sound

inductive PrintSourceSequence {cfg : Cfg} (env : Env) (fuel : Nat) :
    List PrintArg → St → List String → St → Prop
  | nil {state : St} : PrintSourceSequence (cfg := cfg) env fuel [] state [] state
  | text {text : String} {args : List PrintArg} {state : St}
      {parts : List String} {after : St}
      (tail : PrintSourceSequence (cfg := cfg) env fuel args state parts after) :
      PrintSourceSequence (cfg := cfg) env fuel (.text text :: args) state (text :: parts) after
  | expr {expr : Expr} {args : List PrintArg} {state after : St}
      {part : String} {parts : List String} {final : St}
      (source : ExprSource cfg env expr state)
      (printable : (∃ ty, source.ty = .int ty) ∨ source.ty = .bool)
      (value : Val)
      (evaluated : evalExpr fuel cfg env expr state = .ok value after)
      (rendered : render value after = .ok part after)
      (tail : PrintSourceSequence (cfg := cfg) env fuel args after parts final) :
      PrintSourceSequence (cfg := cfg) env fuel (.expr expr :: args) state (part :: parts) final

private theorem mapList_cons_ok {α β : Type} (f : α → M β) (head : α) (tail : List α)
    (state : St) (parts : List β) (after : St)
    (done : mapList f (head :: tail) state = .ok parts after) :
    ∃ value middle rest,
      parts = value :: rest ∧ f head state = .ok value middle ∧
        mapList f tail middle = .ok rest after := by
  change M.bind' (f head) (fun value =>
    M.bind' (mapList f tail) (fun rest => M.pure' (value :: rest))) state =
      .ok parts after at done
  cases hhead : f head state with
  | stop error stopped =>
      simp [M.bind', hhead] at done
  | ok value middle =>
      simp only [M.bind', hhead] at done
      change M.bind' (mapList f tail) (fun rest => M.pure' (value :: rest)) middle =
        .ok parts after at done
      cases htail : mapList f tail middle with
      | stop error stopped => simp [M.bind', htail] at done
      | ok rest final =>
          simp only [M.bind', htail] at done
          simp only [M.pure'] at done
          injection done with hparts hafter
          subst parts after
          exact ⟨value, middle, rest, rfl, rfl, htail⟩

private def printSuffixFuture {cfg : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {args : List PrintArg} {origin : OriginId}
    (context : EvaluationContext cfg plans path (.statement (.print args origin)) .statement)
    (rest : List PrintArg) : List VarId := rest.flatMap PrintArg.variables ++ context.outputFuture

private theorem printShrinkExprOutputFuture {cfg : Module} {plans : Array (Array DemandPoint)}
    {path : List Nat} {all : List PrintArg} {origin : OriginId} {pc : PlanContext cfg plans}
    (profile : cfg.profile = .shrink)
    (context : NodeContext pc path (.statement (.print all origin)) .statement)
    (offset : Nat) (expr : Expr) (rest : List PrintArg)
    (harg : all[offset]? = some (.expr expr)) (hrest : rest = all.drop (offset + 1)) :
    ((EvaluationContext.shrink profile context).child rfl offset (.expression expr) .expression
      (by simp [DemandNode.child?, DemandNode.children, harg])
      (by simp [DemandNodeHasPhase, DemandNode.phaseMatches])).outputFuture =
        printSuffixFuture (.shrink profile context) rest := by
  have hchild : (DemandNode.statement (.print all origin)).child? offset =
      some (.expression expr) := by
    simp [DemandNode.child?, DemandNode.children, harg]
  have hphase : DemandNodeHasPhase (.expression expr) .expression := by
    simp [DemandNodeHasPhase, DemandNode.phaseMatches]
  have hoffset : offset < all.length := (List.getElem?_eq_some_iff.mp harg).1
  let transition := context.child rfl offset (.expression expr) .expression hchild hphase
  let parent : DemandPoint :=
    ⟨path, .expression, context.expected.frame.active, context.expected.frame.future,
      context.expected.frame.retained⟩
  have hexpectation :
      (DemandNode.statement (.print all origin)).childExpectation?
          pc.approvals.access parent offset =
        some ⟨(DemandNode.statement (.print all origin)).visibleForChild
            context.expected.frame.active offset,
          rest.flatMap PrintArg.variables ++ context.expected.frame.future⟩ := by
    simp [parent, DemandNode.childExpectation?, DemandNode.childFuture, hchild, hrest, hoffset]
  have hfuture : transition.childFrame.future =
      rest.flatMap PrintArg.variables ++ context.expected.frame.future := by
    exact DemandNode.childFrame_future transition.childFrameEq hexpectation
  change transition.context.expected.frame.future =
    rest.flatMap PrintArg.variables ++ context.expected.frame.future
  rw [transition.expectedFrameEq, DemandNode.phaseFrame_future transition.phaseFrameEq,
    hfuture]
  simp [DemandNode.phaseFuture]

private theorem printSuffixFrame {cfg : Cfg} {env : Env} {args : List PrintArg} {origin : OriginId}
    {state : St} (source : StmtSource cfg env (.print args origin) state) :
    Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      (printSuffixFuture source.context args) := by
  cases hcontext : source.context with
  | pilot profile active =>
      have frame := source.frame
      rw [hcontext] at frame
      simpa [printSuffixFuture, EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        DemandNode.variables, Stmt.variables, PrintArg.variables, DemandNode.visibleAfter] using frame
  | shrink profile context =>
      have frame := source.frame
      rw [hcontext] at frame
      simpa [printSuffixFuture, EvaluationContext.inputFuture, EvaluationContext.outputFuture,
        NodeContext.inputFuture, NodeContext.outputFuture, DemandNode.variables, Stmt.variables,
        PrintArg.variables] using frame

private theorem render_success_state {value : Val} {part : String} {before after : St}
    (done : render value before = .ok part after) : after = before := by
  cases value with
  | int ty n => simp [render] at done; cases done; rfl
  | bool value => cases value <;> simp [render] at done <;> cases done <;> rfl
  | unit => simp [render] at done; cases done
  | fixed elems => simp [render] at done; cases done
  | record id fields => simp [render] at done; cases done
  | resizable elem elems => simp [render] at done; cases done
  | limited elem capacity slots len => simp [render] at done; cases done
  | ref location => simp [render] at done; cases done
  | slice location start len => simp [render] at done; cases done

private theorem execPrintExpr_success {cfg : Cfg} {env : Env} {expr : Expr}
    {state final : St} {part : String} {fuel : Nat}
    (done : execPrintArg (fuel + 1) cfg env (.expr expr) state = .ok part final) :
    ∃ value after, evalExpr fuel cfg env expr state = .ok value after ∧
      render value after = .ok part after ∧ final = after := by
  simp only [execPrintArg] at done
  change M.bind' (evalExpr fuel cfg env expr) render state = .ok part final at done
  cases heval : evalExpr fuel cfg env expr state with
  | stop error stopped => simp [M.bind', heval] at done
  | ok value after =>
      simp only [M.bind', heval] at done
      have hstate := render_success_state done
      subst final
      exact ⟨value, after, rfl, done, rfl⟩

private theorem printSourcesSuffix {cfg : Cfg} {env : Env} {all : List PrintArg}
    {origin : OriginId} {initial : St}
    (source : StmtSource cfg env (.print all origin) initial) (fuel offset : Nat)
    {args : List PrintArg} {state final : St} {parts : List String}
    (suffix : args = all.drop offset)
    {typingStart typingFinal : Nat}
    (typed : tyPrintArgs source.typingEnv args typingStart = .ok ((), typingFinal))
    {rootsStart rootsFinal : RState}
    (rooted : rpPrintArgs source.rootsEnv args rootsStart = .ok ((), rootsFinal))
    (effects : EffLe rootsFinal.eff source.world.E)
    (frame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
      (printSuffixFuture source.context args))
    (observed : ObservedSafe cfg.mod source.world
      (source.context.mayShrink source.world.ownerP source.observation) source.observation state.store)
    (classified : cfg.mod.profile = .shrink →
      ClassifiedParameters cfg.mod source.world.P source.world.D source.observation state.store)
    (done : mapList (execPrintArg (fuel + 1) cfg env) args state = .ok parts final) :
    PrintSourceSequence (cfg := cfg) env fuel args state parts final := by
  induction args generalizing offset typingStart typingFinal rootsStart rootsFinal state parts final with
  | nil =>
      simp only [mapList, M.pure'] at done
      injection done with hparts hfinal
      subst parts final
      exact .nil
  | cons arg rest ih =>
      have hdrop : arg :: rest = all.drop offset := suffix
      have harg : all[offset]? = some arg := by
        have hfirst : (all.drop offset)[0]? = some arg := by rw [← hdrop]; rfl
        simpa using hfirst
      have hrest : rest = all.drop (offset + 1) := by
        have h := congrArg (fun xs : List PrintArg => xs.drop 1) hdrop
        simpa using h
      obtain ⟨part, middle, restParts, hparts, hhead, htail⟩ :=
        mapList_cons_ok (execPrintArg (fuel + 1) cfg env) arg rest state parts final done
      subst parts
      cases arg with
      | text text =>
          simp only [tyPrintArgs] at typed
          simp only [rpPrintArgs] at rooted
          have htext : execPrintArg (fuel + 1) cfg env (.text text) state = .ok text state := by
            simp only [execPrintArg]
            rfl
          rw [htext] at hhead
          injection hhead with hpart hmiddle
          subst part middle
          refine .text (ih (offset + 1) hrest typed rooted effects ?_ observed classified htail)
          simpa [printSuffixFuture, PrintArg.variables] using frame
      | expr expr =>
          simp only [tyPrintArgs] at typed
          inv at typed
          simp only [rpPrintArgs] at rooted
          inv at rooted
          obtain ⟨ty, typingNext, htypedExpr, htypedRest⟩ := typed
          obtain ⟨roots, rootsNext, hrootedExpr, hrootedRest⟩ := rooted
          have hty : ((∃ t, ty = .int t) ∨ ty = .bool) ∧
              tyPrintArgs source.typingEnv rest typingNext = .ok ((), typingFinal) := by
            cases ty <;> inv at htypedRest <;> first
              | exact ⟨Or.inl ⟨_, rfl⟩, htypedRest⟩
              | exact ⟨Or.inr rfl, htypedRest⟩
          obtain ⟨value, after, heval, hrender, hmiddle⟩ := execPrintExpr_success hhead
          subst middle
          have childAt : (DemandNode.statement (.print all origin)).child? offset =
              some (.expression expr) := by
            simp [DemandNode.child?, DemandNode.children, harg]
          have visible : ∀ x, x ∈ source.typingEnv.visible ↔
              x ∈ (DemandNode.statement (.print all origin)).visibleForChild
                source.typingEnv.visible offset := by
            intro x
            simp [DemandNode.visibleForChild]
          have phase : DemandNodeHasPhase (.expression expr) .expression := by
            simp [DemandNodeHasPhase, DemandNode.phaseMatches]
          let childContext := source.context.child rfl offset (.expression expr) .expression childAt phase
          have childInputEq : childContext.inputFuture = expr.variables ++ childContext.outputFuture := by
            cases childContext with
            | pilot profile active => rfl
            | shrink profile context => rfl
          have childFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
              state childContext.inputFuture := by
            cases hcontext : source.context with
            | pilot profile active =>
                have base : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
                    state (expr.variables ++ (rest.flatMap PrintArg.variables ++ active)) := by
                  simpa [hcontext, printSuffixFuture, EvaluationContext.outputFuture,
                    DemandNode.visibleAfter, PrintArg.variables, List.append_assoc] using frame
                have houtput : childContext.outputFuture = active := by
                  simp [childContext, hcontext, EvaluationContext.child, EvaluationContext.outputFuture,
                    DemandNode.visibleForChild, DemandNode.visibleAfter]
                have hinput : childContext.inputFuture = expr.variables ++ active := by
                  rw [childInputEq, houtput]
                apply base.narrowFuture
                intro x hx
                rw [hinput] at hx
                simp only [List.mem_append] at hx ⊢
                rcases hx with hx | hx
                · exact Or.inl hx
                · exact Or.inr (Or.inr hx)
            | shrink profile context =>
                have hout := printShrinkExprOutputFuture profile context offset expr rest harg hrest
                have base : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
                    state (expr.variables ++ (rest.flatMap PrintArg.variables ++ context.outputFuture)) := by
                  change Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env state
                    (expr.variables ++ (rest.flatMap PrintArg.variables ++
                      (EvaluationContext.shrink profile context).outputFuture))
                  simpa [hcontext, printSuffixFuture, PrintArg.variables, List.append_assoc] using frame
                have houtput : childContext.outputFuture =
                    rest.flatMap PrintArg.variables ++ (EvaluationContext.shrink profile context).outputFuture := by
                  simpa [childContext, hcontext, phase, printSuffixFuture] using hout
                have hinput : childContext.inputFuture =
                    expr.variables ++ (rest.flatMap PrintArg.variables ++
                      (EvaluationContext.shrink profile context).outputFuture) := by
                  rw [childInputEq, houtput]
                rw [hinput]
                exact base
          have effectsExpr : EffLe rootsNext.eff source.world.E :=
            ((rpPrintArgs_mono hrootedRest).2.trans effects)
          obtain ⟨child, hTypingEnv, hRootsEnv, hChildTy, hWorld, hObservation,
              hChildFuture, hRetained, hMayShrink⟩ := source.expressionChildSource offset expr
                childAt visible typingStart typingNext ty rootsStart rootsNext roots
                htypedExpr hrootedExpr effectsExpr childFrame observed classified
          let result := child.result fuel value heval
          have childPrintable : (∃ t, child.ty = .int t) ∨ child.ty = .bool := by
            rw [hChildTy]
            exact hty.1
          have hchildContext : child.context.outputFuture = childContext.outputFuture := by
            simpa [childContext, phase] using hChildFuture
          have nextFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv source.rootsEnv env
              after (printSuffixFuture source.context rest) := by
            cases hcontext : source.context with
            | pilot profile active =>
                have hactive := source.active
                rw [hcontext] at hactive
                have hactivePilot : ∀ x, x ∈ source.typingEnv.visible ↔ x ∈ active := by
                  intro x
                  exact (hactive x).symm
                have houtput : childContext.outputFuture = active := by
                  simp [childContext, hcontext, EvaluationContext.child, EvaluationContext.outputFuture,
                    DemandNode.visibleForChild, DemandNode.visibleAfter]
                have hframe := result.frame
                rw [hchildContext, houtput] at hframe
                have activeFrame : Core.Sound.Frame cfg.mod source.world source.typingEnv
                    source.rootsEnv env after active := by
                  rw [hWorld, hTypingEnv, hRootsEnv] at hframe
                  exact hframe
                apply activeFrame.changeFuture
                intro x hxvisible _
                exact hactivePilot x |>.1 hxvisible
            | shrink profile context =>
                have hout := printShrinkExprOutputFuture profile context offset expr rest harg hrest
                have hout' : childContext.outputFuture = printSuffixFuture source.context rest := by
                  simpa [childContext, hcontext, phase] using hout
                have hframe := result.frame
                rw [hchildContext, hout'] at hframe
                rw [hWorld, hTypingEnv, hRootsEnv] at hframe
                simpa [hcontext] using hframe
          have nextObserved : ObservedSafe cfg.mod source.world
              (source.context.mayShrink source.world.ownerP source.observation) source.observation
              after.store := by
            simpa [hWorld, hObservation, hMayShrink] using result.observed
          have nextClassified : cfg.mod.profile = .shrink →
              ClassifiedParameters cfg.mod source.world.P source.world.D source.observation after.store := by
            simpa [hWorld, hObservation] using result.classified
          refine .expr child childPrintable value heval hrender ?_
          exact ih (offset + 1) hrest hty.2 hrootedRest effects nextFrame
            nextObserved nextClassified htail

theorem StmtSource.printSources {cfg : Cfg} {env : Env} {args : List PrintArg}
    {origin : OriginId} {state final : St} {parts : List String}
    (source : StmtSource cfg env (.print args origin) state) (fuel : Nat)
    (done : mapList (execPrintArg (fuel + 1) cfg env) args state = .ok parts final) :
    PrintSourceSequence (cfg := cfg) env fuel args state parts final := by
  have typedStmt := source.typed
  simp only [tyStmt] at typedStmt
  inv at typedStmt
  obtain ⟨_, htypedExists⟩ := typedStmt
  obtain ⟨typingFinal, htyped, _, _⟩ := htypedExists
  have rootedStmt := source.rooted
  simp only [rpStmt] at rootedStmt
  inv at rootedStmt
  obtain ⟨rootsFinal, hrooted, houtputs⟩ := rootedStmt
  have effects : EffLe rootsFinal.eff source.world.E :=
    (PMono.noteOutputs _ _ _ houtputs).2.trans source.effects
  have frame := printSuffixFrame source
  exact printSourcesSuffix source fuel 0 rfl htyped hrooted effects frame source.observed
    source.classified done

end Goose.Lower
