import Draft.Sequentialization
import Draft.Checks.Lift

/-! The orders of the steps of three source diagrams.

The first group has three steps. `A` and `B` are pure, and `B` uses the output of `A`. `C` is
effectful and uses the first input only. The source diagram has the order `A B C`.

`C` is ready in the source diagram: it moves past `B` and then past `A`. The orders `A C B` and
`C A B` are two diagrams, and each has the evidence that it is an order of the source diagram.
The source diagram is an order of itself. Each order gives the same two values, for arbitrary
inputs and an arbitrary response of the store. The derivation of each order is in the
interchange equation set, and a check consumes its soundness through a dependent payload that
has the response of the store.

The source diagram is a diagram of the fragment with fixed occurrences. Its ready steps are `A`
and `C`: `B` has the output of `A` as an operand. The list of its orders has the three orders
and no other order, and each order of the list gives the same two values.

The source diagram has a verified implementation: its lift for a specification with an
admission, and then the verified lowering. The map of verified implementations along the
derivation of an order gives the verified implementation of the order. The receipt at the exit
of the source diagram and of the order `A C B` gives the same payload through its identity,
for an arbitrary admission. The evidence of the order `C A B` has the same value in its
receipt, and a check consumes its postcondition of `B` through a dependent payload.

The second group has a shared operand and a repeated operand. `A` is pure. `B` is pure and has
the output of `A` as its two operands. `C` is effectful and has the output of `A` as its
operand. `D` has the outputs of `B` and `C`. The list of the orders has the two orders of `B`
and `C`. Each order has four steps, so `A` has one occurrence, and each gives the same values.

The third group has a discarded value. `A` is effectful, and no step and no exit port has its
response. `B` is pure. The list of the orders has the two orders. After the lowering, each
order is one call of the store. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude

namespace Draft.Checks.Dependency

open Container
open Draft.Checks.Free (store provider)
open Draft.Checks.Dependent (Admission Receipt expected)
open Draft.Checks.Diagram (Op sig Value lower returns inputs values observe opSpec lowerDep)

abbrev Two : Exits Unit := [.one [(), ()]]

/-- The exit after the three steps: the output of `B` and the response of `C`. -/
def last : Diagram sig [(), (), (), (), ()] Two :=
  .exit ⟨_, .here, Boundary.only _, .cons (.there .here) (.cons .here .nil)⟩

/-- `C` is effectful, and its operand is the first input. -/
def stepC : Diagram sig [(), (), (), ()] Two :=
  .step ⟨.emit, .cons (.there (.there .here)) .nil⟩ fun | ⟨_, .here⟩ => last

/-- `B` is pure, and its operands are the output of `A` and the second input. -/
def stepB : Diagram sig [(), (), ()] Two :=
  .step ⟨.add, .cons .here (.cons (.there (.there .here)) .nil)⟩ fun | ⟨_, .here⟩ => stepC

/-- The source diagram: `A` on the two inputs, and then `B`, and then `C`. -/
def source : Diagram sig [(), ()] Two :=
  .step ⟨.add, .cons .here (.cons (.there .here) .nil)⟩ fun | ⟨_, .here⟩ => stepB

/-- The one case of an output boundary with one port. -/
def center : (Boundary.one [()] : Boundary Unit).Case := ⟨_, .here⟩

/-- Each case of that boundary is the one case. -/
def only : (c : (Boundary.one [()] : Boundary Unit).Case) → center ≡ c
  | ⟨_, .here⟩ => .refl

/-- `C` is ready after `A`: it moves past `B`. -/
def pastB := Diagram.Ready.pastOne (S := sig) (b := Op.emit) (Qs := Two) Op.add (.inl .refl)
  (.cons .here (.cons (.there (.there .here)) .nil)) (.cons (.there .here) .nil)
  (rest := fun | ⟨_, .here⟩ => stepC) center only (.here _ _)

/-- `C` is ready in the source diagram: it moves past `B` and then past `A`. -/
def pastA := Diagram.Ready.pastOne (S := sig) (b := Op.emit) (Qs := Two) Op.add (.inl .refl)
  (.cons .here (.cons (.there .here) .nil)) (.cons .here .nil)
  (rest := fun | ⟨_, .here⟩ => stepB) center only pastB.2

/-- The source diagram is an order of itself: each step is the first step. -/
def sourceOrder : Diagram.Order source source :=
  ⟨_, .here _ _, fun
    | ⟨_, .here⟩ => ⟨_, .here _ _, fun
      | ⟨_, .here⟩ => ⟨_, .here _ _, fun
        | ⟨_, .here⟩ => .refl⟩⟩⟩

/-- The order `A C B`. `C` has the first input, and `B` has the output of `A` and the second
input. The exit has the output of `B` and the response of `C`. -/
def middle : Diagram sig [(), ()] Two :=
  .step ⟨.add, .cons .here (.cons (.there .here) .nil)⟩ fun
    | ⟨_, .here⟩ => .step ⟨.emit, .cons (.there .here) .nil⟩ fun
      | ⟨_, .here⟩ =>
          .step ⟨.add, .cons (.there .here) (.cons (.there (.there (.there .here))) .nil)⟩ fun
          | ⟨_, .here⟩ =>
              .exit ⟨_, .here, Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩

/-- The evidence of the order `A C B`: after `A`, the step `C` is ready past `B`. -/
def middleOrder : Diagram.Order middle source :=
  ⟨_, .here _ _, fun
    | ⟨_, .here⟩ => ⟨_, pastB.2, fun
      | ⟨_, .here⟩ => ⟨_, .here _ _, fun
        | ⟨_, .here⟩ => .refl⟩⟩⟩

/-- The order `C A B`. -/
def front : Diagram sig [(), ()] Two :=
  .step ⟨.emit, .cons .here .nil⟩ fun
    | ⟨_, .here⟩ => .step ⟨.add, .cons (.there .here) (.cons (.there (.there .here)) .nil)⟩ fun
      | ⟨_, .here⟩ =>
          .step ⟨.add, .cons .here (.cons (.there (.there (.there .here))) .nil)⟩ fun
          | ⟨_, .here⟩ =>
              .exit ⟨_, .here, Boundary.only _,
                .cons .here (.cons (.there (.there .here)) .nil)⟩

/-- The evidence of the order `C A B`: the step `C` is ready past `B` and `A`. -/
def frontOrder : Diagram.Order front source :=
  ⟨_, pastA.2, fun
    | ⟨_, .here⟩ => ⟨_, .here _ _, fun
      | ⟨_, .here⟩ => ⟨_, .here _ _, fun
        | ⟨_, .here⟩ => .refl⟩⟩⟩

/-- The source diagram is a diagram of the fragment: each of its three steps has one output
case. -/
def straight : source.Straight := ⟨center, only, center, only, center, only, ()⟩

set_option smartUnfolding false in
/-- Each order is a diagram of the fragment, and it has its steps in its order. -/
def orders :
    (Diagram.ops source straight,
      Diagram.ops middle (Diagram.Order.straight middle source middleOrder straight),
      Diagram.ops front (Diagram.Order.straight front source frontOrder straight)) ≡
      ([Op.add, Op.add, Op.emit], [Op.add, Op.emit, Op.add], [Op.emit, Op.add, Op.add]) :=
  .refl

variable (stop : Free (sig.interface Value) (Exits.At Two Value)) (count : Nat)

set_option smartUnfolding false in
/-- Each order gives the same two values, for arbitrary inputs and an arbitrary response of the
store. -/
def sourceRun (flag : Bool) (u v x y : Nat) :
    observe stop count source flag u v x y ≡ (x + y + y, u + x) := .refl

set_option smartUnfolding false in
def middleRun (flag : Bool) (u v x y : Nat) :
    observe stop count middle flag u v x y ≡ (x + y + y, u + x) := .refl

set_option smartUnfolding false in
def frontRun (flag : Bool) (u v x y : Nat) :
    observe stop count front flag u v x y ≡ (x + y + y, u + x) := .refl

/-- The soundness of the derivation of an order: the source diagram and the order agree after
the lowering. -/
def sound (e : Diagram sig [(), ()] Two) (o : Diagram.Order e source) (x y : Nat) :
    Free.Agreement ((source.meaning stop count (inputs x y)).subst lower)
      ((e.meaning stop count (inputs x y)).subst lower) :=
  (Diagram.Order.derivation (Rules.Map.id _) e source o).sound stop count
    (.interchange returns) (inputs x y) .pure

set_option smartUnfolding false in
/-- The identity of the returned values of the source diagram and of the order `A C B` is
consumed through a dependent payload that has the response of the store. -/
def middleSound (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((sound stop count middle middleOrder x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + x, Nat.lt_succ_self _⟩).val ≡ u + x := .refl

set_option smartUnfolding false in
/-- The same for the order `C A B`, whose derivation has two interchanges. -/
def frontSound (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((sound stop count front frontOrder x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + x, Nat.lt_succ_self _⟩).val ≡ u + x := .refl

set_option smartUnfolding false in
/-- The ready steps of the source diagram are `A` and `C`. -/
def readySteps : (Diagram.choices source straight).map (fun choice => choice.1) ≡
    [Op.add, Op.emit] := .refl

set_option smartUnfolding false in
/-- The list of the orders of the source diagram has the three orders. -/
def allOrders :
    ((Diagram.orders source straight).map fun r =>
        Diagram.ops r.1 (Diagram.Order.straight r.1 source r.2 straight)) ≡
      [[Op.add, Op.add, Op.emit], [Op.add, Op.emit, Op.add], [Op.emit, Op.add, Op.add]] :=
  .refl

set_option smartUnfolding false in
/-- Each order of the list gives the same two values, for arbitrary inputs and an arbitrary
response of the store. -/
def allRuns (flag : Bool) (u v x y : Nat) :
    ((Diagram.orders source straight).map fun r =>
        observe stop count r.1 flag u v x y) ≡
      [(x + y + y, u + x), (x + y + y, u + x), (x + y + y, u + x)] := .refl

/-! The evidence of each order. -/

/-- The specification of the source diagram. The witness of its precondition is an admission.
The exit has the output of `B` as a function of the two inputs, and the response of `C` with a
receipt for the admission. -/
def sourceSpec : DepPoly.{0, 0, 0, 0} (Diagram.interface Value [(), ()] Two) where
  Pre _ := Admission
  Post env pre out :=
    ((values out).1 ≡ env.lookup .here + env.lookup (.there .here) + env.lookup (.there .here)) ×
      ((m : Nat) × (((values out).2 ≡ m + env.lookup .here) × Receipt (expected pre m)))

/-- The lift of the source diagram, by the constructors of the diagram. The exit has the
postconditions of `A` and `B`, and the receipt of `C`. -/
def sourceLift : source.Lift opSpec sourceSpec := fun env pre =>
  Diagram.RunDep.step (S := sig) ⟨Op.add, .cons .here (.cons (.there .here) .nil)⟩ _ () fun
    | ⟨⟨_, .here⟩, .cons _ .nil⟩, sumA =>
        Diagram.RunDep.step (S := sig)
          ⟨Op.add, .cons .here (.cons (.there (.there .here)) .nil)⟩ _ () fun
          | ⟨⟨_, .here⟩, .cons _ .nil⟩, sumB =>
              Diagram.RunDep.step (S := sig) ⟨Op.emit, .cons (.there (.there .here)) .nil⟩ _
                pre fun
                | ⟨⟨_, .here⟩, .cons _ .nil⟩, receipt =>
                    Diagram.RunDep.exit _
                      ⟨sumB.trans
                          (Identity.cong (fun k => k + env.lookup (.there .here)) sumA),
                        receipt⟩

section

variable (limit : (env : All Value [(), ()]) → (pre : Admission) →
  FreeDep opSpec (sourceSpec.Post env pre) stop)

/-- The verified source diagram and then the verified lowering. -/
def loweredSource : ImplDep sourceSpec Verified.spec ((source.impl stop count).trans lower) :=
  (sourceLift.impl limit count).trans lowerDep

/-- The verified implementation of an order: the map of verified implementations along the
derivation of the order. -/
def lowered (e : Diagram sig [(), ()] Two) (o : Diagram.Order e source) :
    ImplDep sourceSpec Verified.spec ((e.impl stop count).trans lower) :=
  (Diagram.Order.derivation (Rules.Map.id _) e source o).lift (.interchange returns) stop count
    (loweredSource stop count limit)

/-- The receipt at the exit, from a run with a provider that has evidence. -/
def receipt {f : Impl (Diagram.interface Value [(), ()] Two) store}
    (ff : ImplDep sourceSpec Verified.spec f) (flag : Bool) (u v x y : Nat) (pre : Admission) :
    Nat :=
  ((ff.run (Verified.verify flag u v)) (inputs x y) pre).2.2.2.read

set_option smartUnfolding false in
/-- The receipt of the source diagram has the response of the store, for an arbitrary
admission, arbitrary inputs, and arbitrary responses. The payload is a function of the
constructor of the admission. -/
def sourceReceipt (flag : Bool) (u v x y : Nat) (pre : Admission) :
    receipt (loweredSource stop count limit) flag u v x y pre ≡ expected pre u := .refl

set_option smartUnfolding false in
/-- The evidence of the order `A C B` gives the same payload. -/
def middleReceipt (flag : Bool) (u v x y : Nat) (pre : Admission) :
    receipt (lowered stop count limit middle middleOrder) flag u v x y pre ≡ expected pre u := .refl

set_option smartUnfolding false in
/-- The receipt in the evidence of the order `C A B` has the same value. -/
def frontValue (flag : Bool) (u v x y : Nat) (pre : Admission) :
    (((lowered stop count limit front frontOrder).run (Verified.verify flag u v))
      (inputs x y) pre).2.2.2.actual ≡ expected pre u := .refl

set_option smartUnfolding false in
/-- The postcondition of `B` in the evidence of the order `C A B` is consumed through a
dependent payload. -/
def frontSum (flag : Bool) (u v x y : Nat) (pre : Admission) :
    (Identity.transport (fun k => Fin (k + 1))
      (((lowered stop count limit front frontOrder).run (Verified.verify flag u v))
        (inputs x y) pre).1
      ⟨x + y + y, Nat.lt_succ_self _⟩).val ≡ x + y + y := .refl

end

/-! A shared operand and a repeated operand. -/

/-- `A` on the two inputs. `B` has the output of `A` as its two operands. `C` is effectful and
has the output of `A` as its operand. `D` has the outputs of `B` and `C`. The exit has the
output of `D` and the output of `A`. -/
def diamond : Diagram sig [(), ()] Two :=
  .step ⟨.add, .cons .here (.cons (.there .here) .nil)⟩ fun
    | ⟨_, .here⟩ => .step ⟨.add, .cons .here (.cons .here .nil)⟩ fun
      | ⟨_, .here⟩ => .step ⟨.emit, .cons (.there .here) .nil⟩ fun
        | ⟨_, .here⟩ => .step ⟨.add, .cons (.there .here) (.cons .here .nil)⟩ fun
          | ⟨_, .here⟩ =>
              .exit ⟨_, .here, Boundary.only _,
                .cons .here (.cons (.there (.there (.there .here))) .nil)⟩

/-- The diagram is a diagram of the fragment. -/
def diamondStraight : diamond.Straight :=
  ⟨center, only, center, only, center, only, center, only, ()⟩

set_option smartUnfolding false in
/-- The list of the orders has the two orders of `B` and `C`. Each order has four steps: `A`
has one occurrence. -/
def diamondOrders :
    ((Diagram.orders diamond diamondStraight).map fun r =>
        Diagram.ops r.1 (Diagram.Order.straight r.1 diamond r.2 diamondStraight)) ≡
      [[Op.add, Op.add, Op.emit, Op.add], [Op.add, Op.emit, Op.add, Op.add]] := .refl

set_option smartUnfolding false in
/-- Each order gives the same two values. The output of `B` has the output of `A` two times,
and the response of `C` has it one time. -/
def diamondRuns (flag : Bool) (u v x y : Nat) :
    ((Diagram.orders diamond diamondStraight).map fun r =>
        observe stop count r.1 flag u v x y) ≡
      [(x + y + (x + y) + (u + (x + y)), x + y), (x + y + (x + y) + (u + (x + y)), x + y)] :=
  .refl

/-! A discarded value. -/

/-- `A` is effectful, and no step and no exit port has its response. `B` is pure, and the exit
has its output two times. -/
def discarded : Diagram sig [(), ()] Two :=
  .step ⟨.emit, .cons .here .nil⟩ fun
    | ⟨_, .here⟩ => .step ⟨.add, .cons (.there .here) (.cons (.there (.there .here)) .nil)⟩ fun
      | ⟨_, .here⟩ => .exit ⟨_, .here, Boundary.only _, .cons .here (.cons .here .nil)⟩

/-- The diagram is a diagram of the fragment. -/
def discardedStraight : discarded.Straight := ⟨center, only, center, only, ()⟩

set_option smartUnfolding false in
/-- The list of the orders has the two orders. -/
def discardedOrders :
    ((Diagram.orders discarded discardedStraight).map fun r =>
        Diagram.ops r.1 (Diagram.Order.straight r.1 discarded r.2 discardedStraight)) ≡
      [[Op.emit, Op.add], [Op.add, Op.emit]] := .refl

set_option smartUnfolding false in
/-- After the lowering, each order is one call of the store: the step with the discarded
response has one execution in each order. -/
def discardedCalls (x y : Nat) :
    ((Diagram.orders discarded discardedStraight).map fun r =>
        (r.1.meaning (X := Value) stop count (inputs x y)).subst lower) ≡
      [.request .one fun (_ : Nat) =>
          .pure ⟨_, .here, Boundary.only _, .cons (x + y) (.cons (x + y) .nil)⟩,
        .request .one fun (_ : Nat) =>
          .pure ⟨_, .here, Boundary.only _, .cons (x + y) (.cons (x + y) .nil)⟩] := .refl

end Draft.Checks.Dependency

/-- info: 'Draft.Checks.Dependency.orders' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.orders

/-- info: 'Draft.Checks.Dependency.sourceRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.sourceRun

/-- info: 'Draft.Checks.Dependency.middleRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.middleRun

/-- info: 'Draft.Checks.Dependency.frontRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.frontRun

/-- info: 'Draft.Checks.Dependency.middleSound' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.middleSound

/-- info: 'Draft.Checks.Dependency.frontSound' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.frontSound

/-- info: 'Draft.Checks.Dependency.readySteps' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.readySteps

/-- info: 'Draft.Checks.Dependency.allOrders' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.allOrders

/-- info: 'Draft.Checks.Dependency.allRuns' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.allRuns

/-- info: 'Draft.Checks.Dependency.frontSum' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.frontSum

/-- info: 'Draft.Checks.Dependency.diamondOrders' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.diamondOrders

/-- info: 'Draft.Checks.Dependency.diamondRuns' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.diamondRuns

/-- info: 'Draft.Checks.Dependency.discardedOrders' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.discardedOrders

/-- info: 'Draft.Checks.Dependency.discardedCalls' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.discardedCalls

/-- info: 'Draft.Checks.Dependency.sourceReceipt' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.sourceReceipt

/-- info: 'Draft.Checks.Dependency.middleReceipt' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.middleReceipt

/-- info: 'Draft.Checks.Dependency.frontValue' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.frontValue
