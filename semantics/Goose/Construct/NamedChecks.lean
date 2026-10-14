import Goose.Construct.Named

namespace Goose.Construct.NamedChecks

private def array : Ty := .varr (.int .u8)

private def base : Impl := {
  name := "builder"
  params := #[]
  results := #[⟨array, .value, some 0⟩]
  vars := #[⟨"first", array, .mutable, 0, 0⟩, ⟨"second", array, .mutable, 0, 0⟩,
    ⟨"alias", .ref .readOnly array, .immutable, 1, 0⟩]
  body := .mk 0 [.letS 0 (.bytes array [10] 0) 0,
    .retValues [.resultLocal 0 0] 0] none
  summary := .unknown }

private def module (implementation : Impl) : Module :=
  ⟨#[], #[], #[], #[implementation], #[], 0, #[], #[], #[]⟩

private def discovers (implementation : Impl) (expected : List (Option Nat)) : Bool :=
  discoverNamedResults (module implementation) 0 implementation == expected

#guard discovers base [some 0]
#guard discovers { base with body := .mk 0 [.letS 0 (.bytes array [10] 0) 0,
  .ifS (.bool true) (.mk 1 [.retValues [.resultLocal 0 0] 0] none) none 0,
  .retValues [.bytes array [20] 0] 0] none } [some 0]
#guard discovers { base with body := .mk 0 [.letS 0 (.bytes array [10] 0) 0,
  .letS 1 (.bytes array [20] 0) 0,
  .ifS (.bool true) (.mk 1 [.retValues [.resultLocal 0 0] 0] none) none 0,
  .retValues [.resultLocal 1 0] 0] none } [none]
#guard discovers { base with body := .mk 0 [.letS 0 (.bytes array [10] 0) 0,
  .ifS (.bool true) (.mk 1 [.retValues [.resultLocal 0 0] 0] none) none 0,
  .retValues [.copy array (.var 0) 0] 0] none } [none]
#guard discovers { base with body := .mk 0 [.letS 0 (.bytes array [10] 0) 0,
  .ifS (.bool true) (.mk 1 [.letS 2 (.ref .readOnly (.var 0)) 0,
    .retValues [.copy array (.deref (.read (.var 2))) 0] 0] none) none 0,
  .retValues [.resultLocal 0 0] 0] none } [none]
#guard discovers { base with results := #[⟨array, .value, some 0⟩, ⟨array, .value, none⟩], body := .mk 0 [.letS 0 (.bytes array [10] 0) 0,
    .retValues [.resultLocal 0 0, .resultLocal 0 0] 0] none } [some 0, none]
#guard discovers { base with results := #[⟨array, .elementRun, none⟩] } [none]
#guard match checkNamedResults (module { base with results := #[⟨array, .value, none⟩] }) with
  | .error _ => true
  | .ok _ => false
#guard discovers { base with body := .mk 0 [.letS 0 (.bytes array [10] 0) 0,
  .retForward (.call 0 [] 0) 0] none } [none]

#guard discovers { base with
  vars := #[⟨"first", array, .mutable, 0, 0⟩,
    ⟨"view", .slice .readOnly (.int .u8), .mutable, 0, 0⟩], body := .mk 0 [.letS 0 (.bytes array [10] 0) 0,
    .letS 1 (.bytes (.slice .readOnly (.int .u8)) [20] 0) 0,
    .expr (.call 0 [.byRef .mutable (.var 1), .byRef .readOnly (.var 0)] 0) 0,
    .ifS (.bool true) (.mk 1 [.retValues [.resultLocal 0 0] 0] none) none 0,
    .retValues [.copy array (.var 1) 0] 0] none } [none]

end Goose.Construct.NamedChecks
