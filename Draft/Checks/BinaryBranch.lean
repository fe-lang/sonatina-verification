import Draft.Sequentialization
import Draft.Verified

/-! The ready steps of a test with two cases, on Lawrence's Figure 5.6.

The source diagram has a test, and each case has the step `h` on the input `x`, the step `g`
or `g′` on the output of `h`, and the step `f`. Its ready steps are the test and `h`. The
diagram with `h` at the front is from the list of the ready steps. For the evidence of the
move of `h` that is not from the list, the theorem of the completeness gives the position of
`h` in the list, and a check consumes the agreement of the diagrams after `h` through a
dependent payload, in each case of the test.

The third diagram has `f` one time, as a continuation: each case exits to the boundary of the
continuation with its value. A derivation in the control equation set relates the source
diagram to the third diagram: the derivation of the ready step, and then the first exit
equation and the composite equation. The three diagrams have seven, six, and five steps. The
source diagram calls the test before `h`, and the third diagram calls `h` before the test.
The source diagram has a verified implementation for a specification whose postcondition
depends on the witness of the precondition. The map of verified implementations along the
derivation gives the verified implementation of the third diagram, and a check consumes its
evidence at the exit in each case of the test.

The second group has the operands of the ready steps. The test is effectful, and its two
cases have different numbers of ports. Each case has two steps of one operation at one
operand. For a pure operation and an operand of the context of the test, the list has the
test and the four pairs of a step of the first case and a step of the second case. The list
has the test only in three conditions: the operands of the two cases are different ports, the
operand is an output port of the test in one case, or the operation is effectful. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude Container Draft

namespace Draft.Checks.BinaryBranch

/-- The four functions of one argument: `h`, `g`, `g′`, and `f`. -/
abbrev Unary := Fin 4

namespace Unary
abbrev h : Unary := ⟨0, by decide⟩
abbrev g : Unary := ⟨1, by decide⟩
abbrev g' : Unary := ⟨2, by decide⟩
abbrev f : Unary := ⟨3, by decide⟩
end Unary

/-- The operations: the test, which is `none`, and one operation for each function. -/
abbrev Op := Option Unary

/-- One value type. Each operation is pure and has one operand. The test has two cases with no
port, and each other operation has one output port. -/
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

/-- The operand of the test: the first input. -/
def p : PortMap input [()] := .cons .here .nil

/-- The operand of `h`: the second input, `x`. -/
def x : PortMap input [()] := .cons (.there .here) .nil

/-- The step `f` on the first port, and then the exit. -/
def applyF {Γ : List Unit} : Diagram sig (() :: Γ) [value] :=
  .step ⟨some Unary.f, .cons .here .nil⟩ (Diagram.one (Diagram.exitOne (.cons .here .nil)))

/-- The step of a function on the first port, and then the step `f`. -/
def arm {Γ : List Unit} (u : Unary) : Diagram sig (() :: Γ) [value] :=
  .step ⟨some u, .cons .here .nil⟩ (Diagram.one applyF)

/-- The rest after `h` in each case of the test: `g` in the first case, and `g′` in the second
case. -/
def branches : (c : (sig.output none).Case) → (d : value.Case) →
    Diagram sig (d.1 ++ (c.1 ++ input)) [value]
  | ⟨_, .here⟩, ⟨_, .here⟩ => arm Unary.g
  | ⟨_, .there .here⟩, ⟨_, .here⟩ => arm Unary.g'

/-- The rest of a case of the test: the step `h` on `x`, and then the rest after `h`. -/
def path (c : (sig.output none).Case) : Diagram sig (c.1 ++ input) [value] :=
  .step ⟨some Unary.h, x.weaken c.1⟩ (branches c)

/-- The source diagram: the test, and then the rest of each case. -/
def unshared : Diagram sig input [value] := .step ⟨none, p⟩ path

/-- The rest of each case is a diagram of the fragment. -/
def straight (c : (sig.output none).Case) : (path c).Straight :=
  match c with
  | ⟨_, .here⟩ | ⟨_, .there .here⟩ =>
      ⟨⟨Boundary.only _, fun | ⟨_, .here⟩ => .refl⟩,
        ⟨Boundary.only _, fun | ⟨_, .here⟩ => .refl⟩,
        ⟨Boundary.only _, fun | ⟨_, .here⟩ => .refl⟩, ()⟩

/-- The list of the ready steps of the source diagram. -/
def choices : List unshared.Choice :=
  Diagram.binaryChoices (S := sig) none p path (.pair [] []) straight

set_option smartUnfolding false in
/-- The ready steps are the test and `h`. -/
def readyCalls : choices.map Sigma.fst ≡ [none, some Unary.h] := .refl

/-- The ready step `h` of the list, with the diagram after it and its evidence. -/
def chosen : unshared.Choice := choices[1]'(by decide)

/-- The diagram with `h` at the front. -/
def raised : Diagram sig input [value] := .step ⟨chosen.1, chosen.2.1⟩ chosen.2.2.1

/-- The evidence that `h` is ready in the rest of each case is not from the list. The theorem
of the completeness gives a ready step of the list for it. -/
def covered := Diagram.Ready.pastListed (S := sig) none (some Unary.h) (.inr .refl)
  p x path (.pair [] []) straight (after := branches) (fun _ => .here _ _)

set_option smartUnfolding false in
/-- The theorem gives the position of `h` in the list. -/
def coveredPosition : covered.2.2.1.toFin.val ≡ 1 := .refl

/-- The diagram of the one case of the continuation: the step `f`, and then the exit. -/
def finishCase : (c : value.Case) → Diagram sig c.1 [value] := fun | ⟨_, .here⟩ => applyF

/-- The continuation with the step `f`. -/
def tail : Continuation sig value [value] := .copair finishCase

/-- The step of a function on the first port, and then the exit to the boundary of the
continuation. -/
def joinArm {Γ : List Unit} (u : Unary) : Diagram sig (() :: Γ) mid :=
  .step ⟨some u, .cons .here .nil⟩ (Diagram.one
    (.exit ⟨value, .here, Boundary.only _, .cons .here .nil⟩))

/-- The diagram before the continuation: the step `h`, the test, and the step of each case
with its exit to the boundary of the continuation. -/
def beforeTail : Diagram sig input mid :=
  .step ⟨some Unary.h, x⟩ (Diagram.one (.step ⟨none, p.weaken [()]⟩ fun
    | ⟨_, .here⟩ => joinArm Unary.g
    | ⟨_, .there .here⟩ => joinArm Unary.g'))

/-- The third diagram: the diagram before the continuation, and then the continuation. -/
def shared : Diagram sig input [value] := .seq beforeTail tail

/-- The rest after `h` in a case is the step of its function with an exit to the boundary of
the continuation, and then the continuation: the first exit equation under the step. -/
def atJoin {Γ : List Unit} (u : Unary) :
    Diagram.Derivation (Rules.control sig) (arm (Γ := Γ) u) ((joinArm u).atExits tail) :=
  Diagram.Derivation.step (R := Rules.control sig) (Γ := () :: Γ) ⟨some u, .cons .here .nil⟩ fun
    | ⟨_, .here⟩ =>
      .symm (.trans (.rule (.inr (.inl (Diagram.ExitCopair.exit (S := sig)
        (Boundary.only [()]) (.cons .here .nil) finishCase))))
        (.agree (.step _ fun | ⟨_, .here⟩ => .exit _)))

/-- The derivation from the diagram with `h` at the front to the third diagram: the first exit
equation in each case of the test, and then the composite equation. -/
def shareTail : Diagram.Derivation (Rules.control sig) raised shared :=
  .trans (e := beforeTail.atExits tail) (Diagram.Derivation.step (R := Rules.control sig)
    ⟨some Unary.h, x⟩ fun
    | ⟨_, .here⟩ => Diagram.Derivation.step (R := Rules.control sig) ⟨none, p.weaken [()]⟩ fun
      | ⟨_, .here⟩ => .trans (.agree (Diagram.renameId (arm Unary.g))) (atJoin Unary.g)
      | ⟨_, .there .here⟩ => .trans (.agree (Diagram.renameId (arm Unary.g'))) (atJoin Unary.g'))
    (.symm (.rule (.inr (.inr (.inr (.seq beforeTail tail))))))

/-- The derivation from the source diagram to the third diagram: the derivation of the ready
step, and then the derivation to the third diagram. -/
def factor : Diagram.Derivation (Rules.control sig) unshared shared :=
  .trans (chosen.2.2.2.derivation ⟨Sum.inl, fun r => nomatch r⟩) shareTail

set_option smartUnfolding false in
/-- The three diagrams have seven, six, and five steps. -/
def sizes : (unshared.size, raised.size, shared.size) ≡ (7, 6, 5) := .refl

/-- The source diagram and the third diagram agree after each lowering in which each pure
operation returns without a call. -/
def same {D : Container.{0, 0}} {X : Unit → Type} {α : Type}
    {lower : Impl (sig.interface X) D}
    (pure : ImplDep (sig.pureSpec X) (DepPoly.noCall.{0, 0, 0, 0} D) lower)
    (env : All X input) (stop : Free (sig.interface X) α) (n : Nat)
    (rest : Exits.At [value] X → Free (sig.interface X) α) :
    Free.Agreement ((unshared.run stop n env rest).subst lower)
      ((shared.run stop n env rest).subst lower) :=
  factor.sound stop n (Rules.Sound.control pure) env rest

abbrev Val (_ : Unit) := Nat

/-- The responses of the calls, for a function of each operation. The test has the first case
at zero and the second case at a successor. -/
def response (fs : Unary → Nat → Nat) : Section (sig.interface Val)
  | ⟨none, .cons 0 .nil⟩ => ⟨⟨_, .here⟩, .nil⟩
  | ⟨none, .cons (_ + 1) .nil⟩ => ⟨⟨_, .there .here⟩, .nil⟩
  | ⟨some u, .cons a .nil⟩ => ⟨Boundary.only _, .cons (fs u a) .nil⟩

/-- The value at the exit. -/
def output (r : Exits.At [value] Val) : Nat :=
  Exits.At.only (fun v => (Boundary.onlyValues v).lookup .here) r

def finish (out : Exits.At [value] Val) : Free (sig.interface Val) Nat :=
  .pure (output out)

/-- The value at the exit of a diagram after `h`, for a response `y` of `h`. -/
def residualValue (fs : Unary → Nat → Nat) (q a y : Nat)
    (d : Diagram sig (() :: input) [value]) : Nat :=
  (d.run (.pure 0) 0 (.cons y (.cons q (.cons a .nil))) finish).run (response fs)

/-- Two diagrams after `h` that agree have one value at the exit. -/
def residualAgreement (fs : Unary → Nat → Nat) (q a y : Nat)
    {d e : Diagram sig (() :: input) [value]} (agreement : Diagram.Agreement d e) :
    residualValue fs q a y d ≡ residualValue fs q a y e :=
  (agreement.run (X := Val) (.pure 0) 0 (.cons y (.cons q (.cons a .nil)))
    (rest := finish) (rest' := finish) (fun _ => .refl _)).run
      (f := response fs) (g := response fs) (fun _ => .refl)

set_option smartUnfolding false in
/-- The agreement of the diagrams after `h` that the theorem gives is consumed through a
dependent payload, in each case of the test. -/
def coveredArms (fs : Unary → Nat → Nat) (q a y : Nat) (F : Nat → Type)
    (l : F (fs Unary.f (fs Unary.g y))) (r : F (fs Unary.f (fs Unary.g' y))) :
    (Identity.transport F (residualAgreement fs 0 a y (covered.2.2.2 (Boundary.only _))) l,
      Identity.transport F (residualAgreement fs (Nat.succ q) a y (covered.2.2.2 (Boundary.only _))) r) ≡
    (l, r) := .refl

/-- The computation of a diagram from the two inputs. -/
def run (d : Diagram sig input [value]) (q a : Nat) : Free (sig.interface Val) Nat :=
  d.run (.pure 0) 0 (.cons q (.cons a .nil)) finish

/-- The operations of the calls of a computation. -/
def calls (fs : Unary → Nat → Nat) : Free (sig.interface Val) Nat → List Op
  | .pure _ => []
  | .request req k => req.1 :: calls fs (k (response fs req))

set_option smartUnfolding false in
/-- In the first case of the test, the source diagram calls the test before `h`, and the third
diagram calls `h` before the test. -/
def trueCalls (fs : Unary → Nat → Nat) (a : Nat) :
    (calls fs (run unshared 0 a), calls fs (run shared 0 a)) ≡
    ([none, some Unary.h, some Unary.g, some Unary.f],
      [some Unary.h, none, some Unary.g, some Unary.f]) := .refl

set_option smartUnfolding false in
/-- The two orders of the calls in the second case of the test. -/
def falseCalls (fs : Unary → Nat → Nat) (q a : Nat) :
    (calls fs (run unshared (q + 1) a), calls fs (run shared (q + 1) a)) ≡
    ([none, some Unary.h, some Unary.g', some Unary.f],
      [some Unary.h, none, some Unary.g', some Unary.f]) := .refl

/-- The lowering: each operation returns its response without a call. -/
def lower (fs : Unary → Nat → Nat) :
    Impl (sig.interface Val) Container.zero.{0, 0} := Impl.ofSection (response fs)

/-- Each pure operation of the lowering returns without a call. -/
def returns (fs : Unary → Nat → Nat) :
    ImplDep (sig.pureSpec Val) (DepPoly.noCall.{0, 0, 0, 0} _) (lower fs) :=
  fun _ _ => .pure ⟨⟩

/-- The value at the exit as a function of the inputs. -/
def expected (fs : Unary → Nat → Nat) : All Val input → Nat
  | .cons 0 (.cons a .nil) => fs Unary.f (fs Unary.g (fs Unary.h a))
  | .cons (_ + 1) (.cons a .nil) => fs Unary.f (fs Unary.g' (fs Unary.h a))

/-- The specification of the diagrams, for a family on the values. A witness of the
precondition is an element of the family at the expected value. The postcondition has the
identity of the expected value with the value at the exit, and an element of the family at the
value at the exit that is the transport of the witness. -/
def spec (fs : Unary → Nat → Nat) (F : Nat → Type) :
    DepPoly.{0, 0, 0, 0} (Diagram.interface Val input [value]) where
  Pre env := F (expected fs env)
  Post env pre out := (p : expected fs env ≡ output out) ×
    ((w : F (output out)) × (Identity.transport F p pre ≡ w))

variable (stop : Free (sig.interface Val) (Exits.At [value] Val)) (n : Nat)

set_option smartUnfolding false in
/-- The verified implementation of the source diagram, after the lowering. -/
def sourceLift (fs : Unary → Nat → Nat) (F : Nat → Type) :
    ImplDep (spec fs F) DepPoly.zero ((unshared.impl stop n).trans (lower fs))
  | .cons 0 (.cons _ .nil), pre => .pure ⟨.refl, pre, .refl⟩
  | .cons (_ + 1) (.cons _ .nil), pre => .pure ⟨.refl, pre, .refl⟩

/-- The verified implementation of the third diagram, along the derivation. -/
def verified (fs : Unary → Nat → Nat) (F : Nat → Type) :
    ImplDep (spec fs F) DepPoly.zero ((shared.impl stop n).trans (lower fs)) :=
  factor.lift (.control (returns fs)) stop n (sourceLift stop n fs F)

set_option smartUnfolding false in
/-- The evidence at the exit of the third diagram has the witness of the precondition, in the
first case of the test, for arbitrary functions of the operations and an arbitrary witness. -/
def trueEvidence (fs : Unary → Nat → Nat) (a : Nat) (F : Nat → Type)
    (w : F (fs Unary.f (fs Unary.g (fs Unary.h a)))) :
    ((verified stop n fs F).run (Evidence.zero _) (.cons 0 (.cons a .nil)) w).2.1 ≡ w := .refl

set_option smartUnfolding false in
/-- The same evidence in the second case of the test. -/
def falseEvidence (fs : Unary → Nat → Nat) (q a : Nat) (F : Nat → Type)
    (w : F (fs Unary.f (fs Unary.g' (fs Unary.h a)))) :
    ((verified stop n fs F).run (Evidence.zero _) (.cons (Nat.succ q) (.cons a .nil)) w).2.1 ≡ w :=
  .refl

namespace Operands

/-- An effectful test with two output ports in the first case and one in the second case, and
an operation of a given kind with one operand. -/
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

/-- Two steps of the operation at one operand, and then the exit. -/
def twice (k : Kind) {Γ : List Unit} (operand : PortMap Γ [()]) :
    Diagram (signature k) Γ [.one []] :=
  .step ⟨true, operand⟩ (Diagram.one
    (.step ⟨true, operand⟩ (Diagram.one (Diagram.exitOne .nil))))

/-- The operations of the ready steps of the test, for the operand of the two steps of each
case. -/
def ready (k : Kind) (l : PortMap ([(), ()] ++ input) [()]) (r : PortMap ([()] ++ input) [()]) :
    List Bool :=
  let arms : (c : ((signature k).output false).Case) → Diagram (signature k) (c.1 ++ input) [.one []]
    | ⟨_, .here⟩ => twice k l
    | ⟨_, .there .here⟩ => twice k r
  let straight : (c : ((signature k).output false).Case) → (arms c).Straight
    | ⟨_, .here⟩ | ⟨_, .there .here⟩ =>
        ⟨⟨Boundary.only _, fun | ⟨_, .here⟩ => .refl⟩,
          ⟨Boundary.only _, fun | ⟨_, .here⟩ => .refl⟩, ()⟩
  (Diagram.binaryChoices (S := signature k) (Γ := input) false .nil arms (.pair _ _) straight).map
    fun choice => choice.1

set_option smartUnfolding false in
/-- For a pure operation and an operand of the context of the test, the list has the test and
the four pairs of a step of the first case and a step of the second case. -/
def repeated : ready .pure (x.weaken [(), ()]) (x.weaken [()]) ≡
    [false, true, true, true, true] := .refl

set_option smartUnfolding false in
/-- The operands of the two cases are different ports: the list has the test only. -/
def distinctPorts : ready .pure (x.weaken [(), ()]) (p.weaken [()]) ≡ [false] := .refl

set_option smartUnfolding false in
/-- The operand is an output port of the test in the first case: the list has the test only. -/
def localLeft : ready .pure (.cons .here .nil) (x.weaken [()]) ≡ [false] := .refl

set_option smartUnfolding false in
/-- The operand is an output port of the test in the second case. -/
def localRight : ready .pure (x.weaken [(), ()]) (.cons .here .nil) ≡ [false] := .refl

set_option smartUnfolding false in
/-- The operation is effectful, as the test is: the list has the test only. -/
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
