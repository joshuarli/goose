import Goose.Construct.Roots

namespace Goose.Construct.ExitRootChecks

private def slice : Ty := .slice .readOnly (.int .u8)
private def caller : Impl :=
  ⟨"catcher", #[⟨0,.byValue⟩,⟨1,.byValue⟩], #[⟨slice,.register,none⟩],
    #[⟨"first",slice,.immutable,0,0⟩,⟨"second",slice,.immutable,0,0⟩],
    .mk 0 [.expr (.call 1 [.byVal (.read (.var 1))] 0) 0] none,.unknown⟩
private def helper : Impl :=
  ⟨"helper",#[⟨0,.byValue⟩],#[],#[⟨"source",slice,.immutable,0,0⟩],
    .mk 0 [.returnFrom 0 [.read (.var 0)] 0] none,.unknown⟩
private def callerContext : Context :=
  ⟨0,"catcher",[(0,[.param 0]),(1,[.param 1])],[[.param 0]],[]⟩
private def helperContext : Context := ⟨1,"helper",[(0,[.param 0])],[],[]⟩
private def module : Module :=
  ⟨#[],#[],#[],#[caller,helper],#[callerContext,helperContext],0,#[],#[],#[⟨0,[]⟩]⟩
private def accepts (module : Module) : Bool :=
  match checkModuleExitRoots module with | .ok _ => true | .error _ => false

#guard !accepts module
#guard accepts { module with contexts := #[{ callerContext with resultRoots := [[.param 1]] },helperContext] }

private def middle : Impl :=
  ⟨"middle",#[⟨0,.byValue⟩],#[],#[⟨"source",slice,.immutable,0,0⟩],
    .mk 0 [.expr (.call 1 [.byVal (.read (.var 0))] 0) 0] none,.unknown⟩
private def middleContext : Context := ⟨2,"middle",[(0,[.param 0])],[],[]⟩
private def transitive : Module := { module with
  impls := #[{ caller with body := .mk 0 [.expr (.call 2 [.byVal (.read (.var 1))] 0) 0] none },helper,middle]
  contexts := #[callerContext,helperContext,middleContext] }

#guard !accepts transitive
#guard accepts { transitive with contexts :=
  #[{ callerContext with resultRoots := [[.param 1]] },helperContext,middleContext] }

end Goose.Construct.ExitRootChecks
