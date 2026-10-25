import Goose.Construct.Eval
import Goose.Construct.Validate

set_option Elab.async false

namespace Goose.Proofs.ConstructionExecutionOwnershipNamedChecks
open Goose.Construct
open Goose.Core (NumProfile)

private def array : Ty := .varr (.int .u8)

private inductive CompletionShape
  | operands | tuple | branch | valueBreak

private def laterResultMutation (named : Bool) (shape : CompletionShape := .operands)
    (mutation : Bool := true) : Module :=
  let valuesAt := fun scope => [Expr.resultLocal 0 0,
    Expr.blockE (.mk scope (if mutation then [.clear (.var 0) 0] else [])
      (some (.bytes array [68] 0))) 0]
  let tail := match shape with
    | .operands => none
    | .tuple => some (.values (valuesAt 1))
    | .branch => some (.ifE (.bool true)
        (.mk 1 [] (some (.values (valuesAt 2)))) (.mk 3 [] (some (.values (valuesAt 4)))) 0)
    | .valueBreak => some (.blockE (.mk 1 [.breakValue (.values (valuesAt 2)) 0] none) 0)
  let owner : Ty := .growshrink (.int .u8)
  let producer : Impl :=
    ⟨"producer", #[], #[⟨array, .value, if named then some 0 else none⟩, ⟨array, .value, none⟩],
      #[⟨"result", owner, .mutable, 0, 0⟩],
      .mk 0 ([.letS 0 (.bytes owner [65] 0) 0] ++
        (match shape with | .operands => [.retValues (valuesAt 1) 0] | _ => [])) tail,
      .unknown⟩
  let entry : Impl := ⟨"entry", #[], #[],
    #[⟨"first", array, .mutable, 0, 0⟩, ⟨"second", array, .mutable, 0, 0⟩],
    .mk 0 [.receive [0, 1] (.call 1 [] 0) 0,
      .print [.view (.of (.var 0)), .view (.of (.var 1))] 0] none, .unknown⟩
  ⟨#["later-result-mutation.goose"], #[], #[], #[entry, producer],
    #[⟨0, "", [], [], []⟩, ⟨1, "", [], [[], []], []⟩], 0, #[⟨0, 1, "let"⟩], #[], #[]⟩

#guard (match (laterResultMutation false).impls[1]? with
  | some producer => discoverNamedResults (laterResultMutation false) 1 producer == [none, none]
  | none => false)

#guard match validate (laterResultMutation true) with
  | .error rejection => rejection.rule == .result
  | .ok () => false

#guard match validate (laterResultMutation false) with
  | .ok () => true
  | .error _ => false

#guard ([NumProfile.release, .debug].all fun profile =>
  match eval 1000 profile (laterResultMutation false) with
  | .done .returned bytes events => bytes.data.toList == [65, 68, 10] &&
      events == [.begin 0, .begin 1, .begin 2, .write 2 0, .publish 2,
        .copy (.storage 2 []) 0, .write 0 0, .write 1 0, .publish 0, .publish 1]
  | _ => false)

#guard ([CompletionShape.tuple, .branch, .valueBreak].all fun shape =>
  match validate (laterResultMutation false shape), validate (laterResultMutation true shape) with
  | .ok (), .error rejection => rejection.rule == .result
  | _, _ => false)

#guard ([NumProfile.release, .debug].all fun profile =>
  [CompletionShape.tuple, .branch, .valueBreak].all fun shape =>
    match eval 1000 profile (laterResultMutation false shape) with
    | .done .returned bytes _ => bytes.data.toList == [65, 68, 10]
    | _ => false)

#guard ([CompletionShape.operands, .tuple, .branch, .valueBreak].all fun shape =>
  match validate (laterResultMutation true shape false) with
  | .ok () => true
  | .error _ => false)

#guard ([NumProfile.release, .debug].all fun profile =>
  [CompletionShape.operands, .tuple, .branch, .valueBreak].all fun shape =>
    match eval 1000 profile (laterResultMutation true shape false) with
    | .done .returned bytes events => bytes.data.toList == [65, 68, 10] &&
        events == [.begin 0, .begin 1, .write 0 0, .write 1 0, .publish 0, .publish 1]
    | _ => false)

end Goose.Proofs.ConstructionExecutionOwnershipNamedChecks
