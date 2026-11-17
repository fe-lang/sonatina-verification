import Draft.Sequentialization
import Draft.Verified

/-! Lawrence's Figure 5.6. Both arms compute `h(x)` on the incoming port. Their results
from `g` and `g′` feed the same continuation `f`. The binary scheduler supplies the move
of `h` before the test, and the control equation supplies the shared tail. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude Container Draft

namespace Draft.Checks.BinaryBranch

abbrev Unary := Fin 4

namespace Unary
abbrev h : Unary := ⟨0, by decide⟩
abbrev g : Unary := ⟨1, by decide⟩
abbrev g' : Unary := ⟨2, by decide⟩
abbrev f : Unary := ⟨3, by decide⟩
end Unary

/-- The test is the `none` constructor and each unary function labels a value operation. -/
abbrev Op := Option Unary

def sig : Signature Unit where
  Op := Op
  kind _ := .pure
  input _ := [()]
  output
    | none => [[], []]
    | some _ => .one [()]

instance : DecEq sig.Op := inferInstanceAs (DecEq Op)

abbrev input : List Unit := [(), ()]
abbrev value : Boundary Unit := .one [()]
abbrev mid : Exits Unit := [value, value]

def p : PortMap input [()] := .cons .here .nil
def x : PortMap input [()] := .cons (.there .here) .nil

def applyF {Γ : List Unit} : Diagram sig (() :: Γ) [value] :=
  .step ⟨some Unary.f, .cons .here .nil⟩ (Diagram.one (Diagram.exitOne (.cons .here .nil)))

def arm {Γ : List Unit} (u : Unary) : Diagram sig (() :: Γ) [value] :=
  .step ⟨some u, .cons .here .nil⟩ (Diagram.one applyF)

def branches : (c : (sig.output none).Case) → (d : value.Case) →
    Diagram sig (d.1 ++ (c.1 ++ input)) [value]
  | ⟨_, .here⟩, ⟨_, .here⟩ => arm Unary.g
  | ⟨_, .there .here⟩, ⟨_, .here⟩ => arm Unary.g'

def path (c : (sig.output none).Case) : Diagram sig (c.1 ++ input) [value] :=
  .step ⟨some Unary.h, x.weaken c.1⟩ (branches c)

def unshared : Diagram sig input [value] := .step ⟨none, p⟩ path

def straight (c : (sig.output none).Case) : (path c).Straight :=
  match c with
  | ⟨_, .here⟩ | ⟨_, .there .here⟩ =>
      ⟨Boundary.only _, (fun | ⟨_, .here⟩ => .refl),
        Boundary.only _, (fun | ⟨_, .here⟩ => .refl),
        Boundary.only _, (fun | ⟨_, .here⟩ => .refl), ()⟩

def choices : List unshared.Choice :=
  Diagram.binaryChoices (S := sig) none p path (.pair [] []) straight

set_option smartUnfolding false in
def readyCalls : choices.map Sigma.fst ≡ [none, some Unary.h] := .refl

/-- The move and its residual are taken from the scheduler's list. -/
def chosen : unshared.Choice := choices[1]'(by decide)

def raised : Diagram sig input [value] := .step ⟨chosen.1, chosen.2.1⟩ chosen.2.2.1

/-- Coverage places the independently specified move of `h` at the selected position. -/
def covered := Diagram.Ready.pastListed (S := sig) none (some Unary.h) (.inr .refl)
  p x path (.pair [] []) straight (after := branches) (fun _ => .here _ _)

set_option smartUnfolding false in
def coveredPosition : covered.2.2.1.toFin.val ≡ 1 := .refl

def finishCase : (c : value.Case) → Diagram sig c.1 [value] := fun | ⟨_, .here⟩ => applyF

def tail : Continuation sig value [value] := .copair finishCase

def joinArm {Γ : List Unit} (u : Unary) : Diagram sig (() :: Γ) mid :=
  .step ⟨some u, .cons .here .nil⟩ (Diagram.one
    (.exit ⟨value, .here, Boundary.only _, .cons .here .nil⟩))

def beforeTail : Diagram sig input mid :=
  .step ⟨some Unary.h, x⟩ (Diagram.one (.step ⟨none, p.weaken [()]⟩ fun
    | ⟨_, .here⟩ => joinArm Unary.g
    | ⟨_, .there .here⟩ => joinArm Unary.g'))

def shared : Diagram sig input [value] := .seq beforeTail tail

/-- Each branch passes its result to the same continuation. -/
def atJoin {Γ : List Unit} (u : Unary) :
    Diagram.Derivation (Rules.control sig) (arm (Γ := Γ) u) ((joinArm u).atExits tail) :=
  Diagram.Derivation.step (R := Rules.control sig) (Γ := () :: Γ) ⟨some u, .cons .here .nil⟩ fun
    | ⟨_, .here⟩ =>
      .symm (.trans (.rule (.inr (.inl (Diagram.ExitCopair.exit (S := sig)
        (Boundary.only [()]) (.cons .here .nil) finishCase))))
        (.agree (.step _ fun | ⟨_, .here⟩ => .exit _)))

def shareTail : Diagram.Derivation (Rules.control sig) raised shared :=
  .trans (e := beforeTail.atExits tail) (Diagram.Derivation.step (R := Rules.control sig)
    ⟨some Unary.h, x⟩ fun
    | ⟨_, .here⟩ => Diagram.Derivation.step (R := Rules.control sig) ⟨none, p.weaken [()]⟩ fun
      | ⟨_, .here⟩ => .trans (.agree (Diagram.renameId (arm Unary.g))) (atJoin Unary.g)
      | ⟨_, .there .here⟩ => .trans (.agree (Diagram.renameId (arm Unary.g'))) (atJoin Unary.g'))
    (.symm (.rule (.inr (.inr (.inr (.seq beforeTail tail))))))

def factor : Diagram.Derivation (Rules.control sig) unshared shared :=
  .trans (chosen.2.2.2.derivation ⟨Sum.inl, fun r => nomatch r⟩) shareTail

set_option smartUnfolding false in
def sizes : (unshared.size, raised.size, shared.size) ≡ (7, 6, 5) := .refl

def same {D : Container.{0, 0}} {X : Unit → Type} {α : Type}
    {lower : Impl (sig.interface X) D}
    (pure : ImplDep (sig.pureSpec X) (DepPoly.noCall.{0, 0, 0, 0} D) lower)
    (env : All X input) (stop : Free (sig.interface X) α) (n : Nat)
    (rest : Exits.At [value] X → Free (sig.interface X) α) :
    Free.Agreement ((unshared.run stop n env rest).subst lower)
      ((shared.run stop n env rest).subst lower) :=
  factor.sound stop n (Rules.Sound.control pure) env rest

abbrev Val (_ : Unit) := Nat

def response (fs : Unary → Nat → Nat) : Section (sig.interface Val)
  | ⟨none, .cons 0 .nil⟩ => ⟨⟨_, .here⟩, .nil⟩
  | ⟨none, .cons (_ + 1) .nil⟩ => ⟨⟨_, .there .here⟩, .nil⟩
  | ⟨some u, .cons a .nil⟩ => ⟨Boundary.only _, .cons (fs u a) .nil⟩

def output (r : Exits.At [value] Val) : Nat :=
  Exits.At.only (fun v => (Boundary.onlyValues v).lookup .here) r

def finish (out : Exits.At [value] Val) : Free (sig.interface Val) Nat :=
  .pure (output out)

/-- Run a residual with an arbitrary response `y` of the hoisted call. -/
def residualValue (fs : Unary → Nat → Nat) (q a y : Nat)
    (d : Diagram sig (() :: input) [value]) : Nat :=
  (d.run (.pure 0) 0 (.cons y (.cons q (.cons a .nil))) finish).run (response fs)

def residualAgreement (fs : Unary → Nat → Nat) (q a y : Nat)
    {d e : Diagram sig (() :: input) [value]} (agreement : Diagram.Agreement d e) :
    residualValue fs q a y d ≡ residualValue fs q a y e :=
  (agreement.run (X := Val) (.pure 0) 0 (.cons y (.cons q (.cons a .nil)))
    (rest := finish) (rest' := finish) (fun _ => .refl _)).run
      (f := response fs) (g := response fs) (fun _ => .refl)

set_option smartUnfolding false in
def coveredArms (fs : Unary → Nat → Nat) (q a y : Nat) (F : Nat → Type)
    (l : F (fs Unary.f (fs Unary.g y))) (r : F (fs Unary.f (fs Unary.g' y))) :
    (Identity.transport F (residualAgreement fs 0 a y (covered.2.2.2 (Boundary.only _))) l,
      Identity.transport F (residualAgreement fs (Nat.succ q) a y (covered.2.2.2 (Boundary.only _))) r) ≡
    (l, r) := .refl

def run (d : Diagram sig input [value]) (q a : Nat) : Free (sig.interface Val) Nat :=
  d.run (.pure 0) 0 (.cons q (.cons a .nil)) finish

def calls (fs : Unary → Nat → Nat) : Free (sig.interface Val) Nat → List Op
  | .pure _ => []
  | .request req k => req.1 :: calls fs (k (response fs req))

set_option smartUnfolding false in
def trueCalls (fs : Unary → Nat → Nat) (a : Nat) :
    (calls fs (run unshared 0 a), calls fs (run shared 0 a)) ≡
    ([none, some Unary.h, some Unary.g, some Unary.f],
      [some Unary.h, none, some Unary.g, some Unary.f]) := .refl

set_option smartUnfolding false in
def falseCalls (fs : Unary → Nat → Nat) (q a : Nat) :
    (calls fs (run unshared (q + 1) a), calls fs (run shared (q + 1) a)) ≡
    ([none, some Unary.h, some Unary.g', some Unary.f],
      [some Unary.h, none, some Unary.g', some Unary.f]) := .refl

def lower (fs : Unary → Nat → Nat) :
    Impl (sig.interface Val) Container.zero.{0, 0} := Impl.ofSection (response fs)

def returns (fs : Unary → Nat → Nat) :
    ImplDep (sig.pureSpec Val) (DepPoly.noCall.{0, 0, 0, 0} _) (lower fs) :=
  fun _ _ => .pure ⟨⟩

def expected (fs : Unary → Nat → Nat) : All Val input → Nat
  | .cons 0 (.cons a .nil) => fs Unary.f (fs Unary.g (fs Unary.h a))
  | .cons (_ + 1) (.cons a .nil) => fs Unary.f (fs Unary.g' (fs Unary.h a))

/-- The caller supplies data at the expected result. The receipt identifies the returned
value and carries that very witness at the returned value. -/
def spec (fs : Unary → Nat → Nat) (F : Nat → Type) :
    DepPoly.{0, 0, 0, 0} (Diagram.interface Val input [value]) where
  Pre env := F (expected fs env)
  Post env pre out := (p : expected fs env ≡ output out) ×
    ((w : F (output out)) × (Identity.transport F p pre ≡ w))

variable (stop : Free (sig.interface Val) (Exits.At [value] Val)) (n : Nat)

set_option smartUnfolding false in
def sourceLift (fs : Unary → Nat → Nat) (F : Nat → Type) :
    ImplDep (spec fs F) DepPoly.zero ((unshared.impl stop n).trans (lower fs))
  | .cons 0 (.cons _ .nil), pre => .pure ⟨.refl, pre, .refl⟩
  | .cons (_ + 1) (.cons _ .nil), pre => .pure ⟨.refl, pre, .refl⟩

def verified (fs : Unary → Nat → Nat) (F : Nat → Type) :
    ImplDep (spec fs F) DepPoly.zero ((shared.impl stop n).trans (lower fs)) :=
  factor.lift (.control (returns fs)) stop n (sourceLift stop n fs F)

set_option smartUnfolding false in
def trueEvidence (fs : Unary → Nat → Nat) (a : Nat) (F : Nat → Type)
    (w : F (fs Unary.f (fs Unary.g (fs Unary.h a)))) :
    ((verified stop n fs F).run (Evidence.zero _) (.cons 0 (.cons a .nil)) w).2.1 ≡ w := .refl

set_option smartUnfolding false in
def falseEvidence (fs : Unary → Nat → Nat) (q a : Nat) (F : Nat → Type)
    (w : F (fs Unary.f (fs Unary.g' (fs Unary.h a)))) :
    ((verified stop n fs F).run (Evidence.zero _) (.cons (Nat.succ q) (.cons a .nil)) w).2.1 ≡ w :=
  .refl

namespace Operands

/-- An effectful test with two fresh ports on the left and one on the right. Each arm
contains two occurrences of the same operation at the supplied operand. -/
def signature (kind : Kind) : Signature Unit where
  Op := Bool
  kind
    | false => .effectful
    | true => kind
  input
    | false => []
    | true => [()]
  output
    | false => [[(), ()], [()]]
    | true => .one []

instance (k : Kind) : DecEq (signature k).Op := inferInstanceAs (DecEq Bool)

def twice (k : Kind) {Γ : List Unit} (operand : PortMap Γ [()]) :
    Diagram (signature k) Γ [.one []] :=
  .step ⟨true, operand⟩ (Diagram.one
    (.step ⟨true, operand⟩ (Diagram.one (Diagram.exitOne .nil))))

def ready (k : Kind) (l : PortMap ([(), ()] ++ input) [()]) (r : PortMap ([()] ++ input) [()]) :
    List Bool :=
  let arms : (c : ((signature k).output false).Case) → Diagram (signature k) (c.1 ++ input) [.one []]
    | ⟨_, .here⟩ => twice k l
    | ⟨_, .there .here⟩ => twice k r
  let straight : (c : ((signature k).output false).Case) → (arms c).Straight
    | ⟨_, .here⟩ | ⟨_, .there .here⟩ =>
        ⟨Boundary.only _, (fun | ⟨_, .here⟩ => .refl),
          Boundary.only _, (fun | ⟨_, .here⟩ => .refl), ()⟩
  (Diagram.binaryChoices (S := signature k) (Γ := input) false .nil arms (.pair _ _) straight).map
    fun choice => choice.1

set_option smartUnfolding false in
/-- Every pairing is available, including a call that moves past an earlier occurrence
in one or both arms. -/
def repeated : ready .pure (x.weaken [(), ()]) (x.weaken [()]) ≡
    [false, true, true, true, true] := .refl

set_option smartUnfolding false in
def distinctPorts : ready .pure (x.weaken [(), ()]) (p.weaken [()]) ≡ [false] := .refl

set_option smartUnfolding false in
def localLeft : ready .pure (.cons .here .nil) (x.weaken [()]) ≡ [false] := .refl

set_option smartUnfolding false in
def localRight : ready .pure (x.weaken [(), ()]) (.cons .here .nil) ≡ [false] := .refl

set_option smartUnfolding false in
def orderedEffects : ready .effectful (x.weaken [(), ()]) (x.weaken [()]) ≡ [false] := .refl

end Operands

/-- info: 'Draft.Checks.BinaryBranch.readyCalls' does not depend on any axioms -/
#guard_msgs in #print axioms readyCalls
/-- info: 'Draft.Checks.BinaryBranch.coveredPosition' does not depend on any axioms -/
#guard_msgs in #print axioms coveredPosition
/-- info: 'Draft.Checks.BinaryBranch.coveredArms' does not depend on any axioms -/
#guard_msgs in #print axioms coveredArms
/-- info: 'Draft.Checks.BinaryBranch.sizes' does not depend on any axioms -/
#guard_msgs in #print axioms sizes
/-- info: 'Draft.Checks.BinaryBranch.same' does not depend on any axioms -/
#guard_msgs in #print axioms same
/-- info: 'Draft.Checks.BinaryBranch.trueCalls' does not depend on any axioms -/
#guard_msgs in #print axioms trueCalls
/-- info: 'Draft.Checks.BinaryBranch.falseCalls' does not depend on any axioms -/
#guard_msgs in #print axioms falseCalls
/-- info: 'Draft.Checks.BinaryBranch.trueEvidence' does not depend on any axioms -/
#guard_msgs in #print axioms trueEvidence
/-- info: 'Draft.Checks.BinaryBranch.falseEvidence' does not depend on any axioms -/
#guard_msgs in #print axioms falseEvidence
/-- info: 'Draft.Checks.BinaryBranch.Operands.repeated' does not depend on any axioms -/
#guard_msgs in #print axioms Operands.repeated
/-- info: 'Draft.Checks.BinaryBranch.Operands.distinctPorts' does not depend on any axioms -/
#guard_msgs in #print axioms Operands.distinctPorts
/-- info: 'Draft.Checks.BinaryBranch.Operands.localLeft' does not depend on any axioms -/
#guard_msgs in #print axioms Operands.localLeft
/-- info: 'Draft.Checks.BinaryBranch.Operands.localRight' does not depend on any axioms -/
#guard_msgs in #print axioms Operands.localRight
/-- info: 'Draft.Checks.BinaryBranch.Operands.orderedEffects' does not depend on any axioms -/
#guard_msgs in #print axioms Operands.orderedEffects

end Draft.Checks.BinaryBranch
