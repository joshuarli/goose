import Goose.Lower.ReflectionTyped

namespace Goose.Lower

open Goose.Core Goose.GIR Goose.Proofs.Fuel

noncomputable def ExprsSource.atFuel {n k : Nat} {cfg : Cfg} {env : Env} {expressions : List Expr} {state : St}
    (bound : n ≤ k) (source : ExprsSource k cfg env expressions state) : ExprsSource n cfg env expressions state := by
  induction expressions generalizing state with
  | nil => exact .nil state
  | cons expression rest induction =>
    cases source with
    | cons head tail =>
      exact .cons head (fun value after done =>
        induction (tail value after (((monoAll n k bound).expr cfg env expression state).1 value after done)))

theorem ExprsSource.atFuel_resultsMatch {n k : Nat} {cfg : Cfg} {env : Env}
    {expressions : List Expr} {state : St} {results : List Ty} (bound : n ≤ k)
    (source : ExprsSource k cfg env expressions state) (metadata : source.resultsMatch results) :
    (source.atFuel bound).resultsMatch results := by
  induction expressions generalizing state with
  | nil => trivial
  | cons expression rest induction =>
    cases source with
    | cons head tail =>
      obtain ⟨headMetadata,tailMetadata⟩ := metadata
      exact ⟨headMetadata,fun value after done => induction _ (tailMetadata value after
        (((monoAll n k bound).expr cfg env expression state).1 value after done))⟩

noncomputable def ArgsSource.atFuel {n k : Nat} {cfg : Cfg} {env : Env} {arguments : List Arg} {state : St}
    (bound : n ≤ k) (source : ArgsSource k cfg env arguments state) : ArgsSource n cfg env arguments state := by
  induction arguments generalizing state with
  | nil => exact .nil state
  | cons argument rest induction =>
    cases source with
    | cons head tail =>
      exact .cons head (fun value after done =>
        induction (tail value after (((monoAll n k bound).arg cfg env argument state).1 value after done)))

theorem ArgsSource.atFuel_resultsMatch {n k : Nat} {cfg : Cfg} {env : Env}
    {arguments : List Arg} {state : St} {results : List Ty} (bound : n ≤ k)
    (source : ArgsSource k cfg env arguments state) (metadata : source.resultsMatch results) :
    (source.atFuel bound).resultsMatch results := by
  induction arguments generalizing state with
  | nil => trivial
  | cons argument rest induction =>
    cases source with
    | cons head tail =>
      obtain ⟨headMetadata,tailMetadata⟩ := metadata
      exact ⟨headMetadata,fun value after done => induction _ (tailMetadata value after
        (((monoAll n k bound).arg cfg env argument state).1 value after done))⟩

noncomputable def ExprsSource.head {n : Nat} {cfg : Cfg} {env : Env}
    {expression : Expr} {rest : List Expr} {state : St}
    (source : ExprsSource n cfg env (expression :: rest) state) : ExprSource cfg env expression state :=
  match source with
  | .cons head _ => head

theorem ExprsSource.head_resultsMatch {n : Nat} {cfg : Cfg} {env : Env}
    {expression : Expr} {rest : List Expr} {state : St} {results : List Ty}
    (source : ExprsSource n cfg env (expression :: rest) state) (metadata : source.resultsMatch results) :
    SourceResults source.head.typingEnv source.head.rootsEnv results := by
  cases source with
  | cons head tail => exact metadata.1

noncomputable def ExprsSource.tail {n : Nat} {cfg : Cfg} {env : Env}
    {expression : Expr} {rest : List Expr} {state after : St} {value : Val}
    (source : ExprsSource n cfg env (expression :: rest) state)
    (done : evalExpr n cfg env expression state = .ok value after) : ExprsSource n cfg env rest after :=
  match source with
  | .cons _ tail => tail value after done

theorem ExprsSource.tail_resultsMatch {n : Nat} {cfg : Cfg} {env : Env}
    {expression : Expr} {rest : List Expr} {state after : St} {value : Val} {results : List Ty}
    (source : ExprsSource n cfg env (expression :: rest) state) (metadata : source.resultsMatch results)
    (done : evalExpr n cfg env expression state = .ok value after) :
    (source.tail done).resultsMatch results := by
  cases source with
  | cons head tail => exact metadata.2 value after done

noncomputable def ExprsSource.afterHead {n : Nat} {cfg : Cfg} {env : Env}
    {expression : Expr} {rest : List Expr} {state after : St} {value : Val}
    (sources : ∀ fuel, ExprsSource fuel cfg env (expression :: rest) state)
    (done : evalExpr n cfg env expression state = .ok value after) (fuel : Nat) :
    ExprsSource fuel cfg env rest after :=
  ((sources (max n fuel)).tail
    (((monoAll n (max n fuel) (Nat.le_max_left _ _)).expr cfg env expression state).1 value after done)).atFuel
      (Nat.le_max_right _ _)

theorem ExprsSource.afterHead_resultsMatch {n : Nat} {cfg : Cfg} {env : Env}
    {expression : Expr} {rest : List Expr} {state after : St} {value : Val} {results : List Ty}
    (sources : ∀ fuel, ExprsSource fuel cfg env (expression :: rest) state)
    (metadata : ∀ fuel, (sources fuel).resultsMatch results)
    (done : evalExpr n cfg env expression state = .ok value after) (fuel : Nat) :
    (ExprsSource.afterHead sources done fuel).resultsMatch results :=
  ExprsSource.atFuel_resultsMatch _ _ ((sources (max n fuel)).tail_resultsMatch (metadata (max n fuel))
    (((monoAll n (max n fuel) (Nat.le_max_left _ _)).expr cfg env expression state).1 value after done))

noncomputable def ArgsSource.tail {n : Nat} {cfg : Cfg} {env : Env}
    {expression : Arg} {rest : List Arg} {state after : St} {value : Val}
    (source : ArgsSource n cfg env (expression :: rest) state)
    (done : evalArg n cfg env expression state = .ok value after) : ArgsSource n cfg env rest after :=
  match source with
  | .cons _ tail => tail value after done

theorem ArgsSource.tail_resultsMatch {n : Nat} {cfg : Cfg} {env : Env}
    {expression : Arg} {rest : List Arg} {state after : St} {value : Val} {results : List Ty}
    (source : ArgsSource n cfg env (expression :: rest) state) (metadata : source.resultsMatch results)
    (done : evalArg n cfg env expression state = .ok value after) :
    (source.tail done).resultsMatch results := by
  cases source with
  | cons head tail => exact metadata.2 value after done

noncomputable def ArgsSource.afterHead {n : Nat} {cfg : Cfg} {env : Env}
    {expression : Arg} {rest : List Arg} {state after : St} {value : Val}
    (sources : ∀ fuel, ArgsSource fuel cfg env (expression :: rest) state)
    (done : evalArg n cfg env expression state = .ok value after) (fuel : Nat) :
    ArgsSource fuel cfg env rest after :=
  ((sources (max n fuel)).tail
    (((monoAll n (max n fuel) (Nat.le_max_left _ _)).arg cfg env expression state).1 value after done)).atFuel
      (Nat.le_max_right _ _)

theorem ArgsSource.afterHead_resultsMatch {n : Nat} {cfg : Cfg} {env : Env}
    {expression : Arg} {rest : List Arg} {state after : St} {value : Val} {results : List Ty}
    (sources : ∀ fuel, ArgsSource fuel cfg env (expression :: rest) state)
    (metadata : ∀ fuel, (sources fuel).resultsMatch results)
    (done : evalArg n cfg env expression state = .ok value after) (fuel : Nat) :
    (ArgsSource.afterHead sources done fuel).resultsMatch results :=
  ArgsSource.atFuel_resultsMatch _ _ ((sources (max n fuel)).tail_resultsMatch (metadata (max n fuel))
    (((monoAll n (max n fuel) (Nat.le_max_left _ _)).arg cfg env expression state).1 value after done))

end Goose.Lower
