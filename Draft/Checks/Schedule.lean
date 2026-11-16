import Draft.Sequentialization
import Draft.Checks.Lift

/-! The orders of the steps of three source diagrams.

The first group has three steps.

`A` and `B` are pure, and `B` uses the output of `A`. `C` is effectful and uses the first input
only. The source diagram has the order `A B C`.

`C` is ready in the source diagram: it moves past `B` and then past `A`. Three schedules give
the orders `A B C`, `A C B`, and `C A B`. Each realization has its steps in that order. Each
gives the same two values, for arbitrary inputs and an arbitrary response of the store. The
derivation of each schedule is in the interchange equation set, and a check consumes its
soundness through a dependent payload that has the response of the store.

The source diagram is a diagram of the fragment with fixed occurrences. Its ready steps are `A`
and `C`: `B` has the output of `A` as an operand. The list of its schedules has the three
orders and no other order, and each realization of the list gives the same two values.

The source diagram has a verified implementation: its lift for a specification with an
admission, and then the verified lowering. The map of verified implementations along the
derivation of a schedule gives the verified implementation of the realization. The receipt at
the exit of the source diagram and of the order `A C B` gives the same payload through its
identity, for an arbitrary admission. The evidence of the order `C A B` has the same value in
its receipt, and a check consumes its postcondition of `B` through a dependent payload.

The second group has a shared operand and a repeated operand. `A` is pure. `B` is pure and has
the output of `A` as its two operands. `C` is effectful and has the output of `A` as its
operand. `D` has the outputs of `B` and `C`. The list of the schedules has the two orders of
`B` and `C`. Each realization has four steps, so `A` has one occurrence, and each gives the
same values.

The third group has a discarded value. `A` is effectful, and no step and no exit port has its
response. `B` is pure. The list of the schedules has the two orders. After the lowering, each
realization is one call of the store. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude

namespace Draft.Checks.Schedule

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

/-- The schedule with the order `A B C`. -/
def first : Diagram.Schedule source :=
  .pick Op.add (.here _ _) fun
    | ⟨_, .here⟩ => .pick Op.add (.here _ _) fun
      | ⟨_, .here⟩ => .pick Op.emit (.here _ _) fun
        | ⟨_, .here⟩ => .exit _

/-- The schedule with the order `A C B`. -/
def middle : Diagram.Schedule source :=
  .pick Op.add (.here _ _) fun
    | ⟨_, .here⟩ => .pick Op.emit pastB.2 fun
      | ⟨_, .here⟩ => .pick Op.add (.here _ _) fun
        | ⟨_, .here⟩ => .exit _

/-- The schedule with the order `C A B`. -/
def front : Diagram.Schedule source :=
  .pick Op.emit pastA.2 fun
    | ⟨_, .here⟩ => .pick Op.add (.here _ _) fun
      | ⟨_, .here⟩ => .pick Op.add (.here _ _) fun
        | ⟨_, .here⟩ => .exit _

/-- The first case of each output boundary of the signature. -/
def firstCase : (o : Op) → (sig.output o).Case
  | .add => ⟨_, .here⟩
  | .isZero => ⟨_, .here⟩
  | .emit => ⟨_, .here⟩

/-- The operations of a diagram, on the path of the first cases. -/
def order : {Γ : List Unit} → {Qs : Exits Unit} → Diagram sig Γ Qs → List Op
  | _, _, .exit _ => []
  | _, _, .step call rest => call.1 :: order (rest (firstCase call.1))
  | _, _, .seq _ _ => []

set_option smartUnfolding false in
/-- Each realization has its steps in the order of its schedule. -/
def orders :
    (order first.realization, order middle.realization, order front.realization) ≡
      ([.add, .add, .emit], [.add, .emit, .add], [.emit, .add, .add]) := .refl

variable (stop : Free (sig.interface Value) (Exits.At Two Value)) (count : Nat)

set_option smartUnfolding false in
/-- Each order gives the same two values, for arbitrary inputs and an arbitrary response of the
store. -/
def firstRun (flag : Bool) (u v x y : Nat) :
    observe stop count first.realization flag u v x y ≡ (x + y + y, u + x) := .refl

set_option smartUnfolding false in
def middleRun (flag : Bool) (u v x y : Nat) :
    observe stop count middle.realization flag u v x y ≡ (x + y + y, u + x) := .refl

set_option smartUnfolding false in
def frontRun (flag : Bool) (u v x y : Nat) :
    observe stop count front.realization flag u v x y ≡ (x + y + y, u + x) := .refl

/-- The soundness of the derivation of a schedule: the source diagram and the realization agree
after the lowering. -/
def sound (s : Diagram.Schedule source) (x y : Nat) :
    Free.Agreement ((source.meaning stop count (inputs x y)).subst lower)
      ((s.realization.meaning stop count (inputs x y)).subst lower) :=
  (s.derivation (Rules.Map.id _)).sound stop count (.interchange returns) (inputs x y) .pure

set_option smartUnfolding false in
/-- The identity of the returned values of the source diagram and of the order `A C B` is
consumed through a dependent payload that has the response of the store. -/
def middleSound (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((sound stop count middle x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + x, Nat.lt_succ_self _⟩).val ≡ u + x := .refl

set_option smartUnfolding false in
/-- The same for the order `C A B`, whose derivation has two interchanges. -/
def frontSound (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((sound stop count front x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + x, Nat.lt_succ_self _⟩).val ≡ u + x := .refl

/-- The source diagram is a diagram of the fragment: each of its three steps has one output
case. -/
def straight : source.Straight := ⟨center, only, center, only, center, only, ()⟩

set_option smartUnfolding false in
/-- The ready steps of the source diagram are `A` and `C`. -/
def readySteps : (Diagram.choices source straight).map (fun choice => choice.1) ≡
    [Op.add, Op.emit] := .refl

set_option smartUnfolding false in
/-- The list of the schedules of the source diagram has the three orders. -/
def allOrders :
    ((Diagram.schedules source straight).map fun s =>
        Diagram.ops s.realization (s.straight straight)) ≡
      [[Op.add, Op.add, Op.emit], [Op.add, Op.emit, Op.add], [Op.emit, Op.add, Op.add]] :=
  .refl

set_option smartUnfolding false in
/-- Each realization of the list gives the same two values, for arbitrary inputs and an
arbitrary response of the store. -/
def allRuns (flag : Bool) (u v x y : Nat) :
    ((Diagram.schedules source straight).map fun s =>
        observe stop count s.realization flag u v x y) ≡
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

/-- The verified implementation of the realization of a schedule: the map of verified
implementations along the derivation of the schedule. -/
def lowered (s : Diagram.Schedule source) :
    ImplDep sourceSpec Verified.spec ((s.realization.impl stop count).trans lower) :=
  (s.derivation (Rules.Map.id _)).lift (.interchange returns) stop count
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
    receipt (lowered stop count limit middle) flag u v x y pre ≡ expected pre u := .refl

set_option smartUnfolding false in
/-- The receipt in the evidence of the order `C A B` has the same value. -/
def frontValue (flag : Bool) (u v x y : Nat) (pre : Admission) :
    (((lowered stop count limit front).run (Verified.verify flag u v)) (inputs x y)
      pre).2.2.2.actual ≡ expected pre u := .refl

set_option smartUnfolding false in
/-- The postcondition of `B` in the evidence of the order `C A B` is consumed through a
dependent payload. -/
def frontSum (flag : Bool) (u v x y : Nat) (pre : Admission) :
    (Identity.transport (fun k => Fin (k + 1))
      (((lowered stop count limit front).run (Verified.verify flag u v)) (inputs x y) pre).1
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
/-- The list of the schedules has the two orders of `B` and `C`. Each realization has four
steps: `A` has one occurrence. -/
def diamondOrders :
    ((Diagram.schedules diamond diamondStraight).map fun s =>
        Diagram.ops s.realization (s.straight diamondStraight)) ≡
      [[Op.add, Op.add, Op.emit, Op.add], [Op.add, Op.emit, Op.add, Op.add]] := .refl

set_option smartUnfolding false in
/-- Each realization gives the same two values. The output of `B` has the output of `A` two
times, and the response of `C` has it one time. -/
def diamondRuns (flag : Bool) (u v x y : Nat) :
    ((Diagram.schedules diamond diamondStraight).map fun s =>
        observe stop count s.realization flag u v x y) ≡
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
/-- The list of the schedules has the two orders. -/
def discardedOrders :
    ((Diagram.schedules discarded discardedStraight).map fun s =>
        Diagram.ops s.realization (s.straight discardedStraight)) ≡
      [[Op.emit, Op.add], [Op.add, Op.emit]] := .refl

set_option smartUnfolding false in
/-- After the lowering, each realization is one call of the store: the step with the discarded
response has one execution in each order. -/
def discardedCalls (x y : Nat) :
    ((Diagram.schedules discarded discardedStraight).map fun s =>
        (s.realization.meaning (X := Value) stop count (inputs x y)).subst lower) ≡
      [.request .one fun (_ : Nat) =>
          .pure ⟨_, .here, Boundary.only _, .cons (x + y) (.cons (x + y) .nil)⟩,
        .request .one fun (_ : Nat) =>
          .pure ⟨_, .here, Boundary.only _, .cons (x + y) (.cons (x + y) .nil)⟩] := .refl

end Draft.Checks.Schedule

/-- info: 'Draft.Checks.Schedule.orders' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.orders

/-- info: 'Draft.Checks.Schedule.firstRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.firstRun

/-- info: 'Draft.Checks.Schedule.middleRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.middleRun

/-- info: 'Draft.Checks.Schedule.frontRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.frontRun

/-- info: 'Draft.Checks.Schedule.middleSound' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.middleSound

/-- info: 'Draft.Checks.Schedule.frontSound' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.frontSound

/-- info: 'Draft.Checks.Schedule.readySteps' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.readySteps

/-- info: 'Draft.Checks.Schedule.allOrders' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.allOrders

/-- info: 'Draft.Checks.Schedule.allRuns' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.allRuns

/-- info: 'Draft.Checks.Schedule.frontSum' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.frontSum

/-- info: 'Draft.Checks.Schedule.diamondOrders' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.diamondOrders

/-- info: 'Draft.Checks.Schedule.diamondRuns' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.diamondRuns

/-- info: 'Draft.Checks.Schedule.discardedOrders' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.discardedOrders

/-- info: 'Draft.Checks.Schedule.discardedCalls' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.discardedCalls

/-- info: 'Draft.Checks.Schedule.sourceReceipt' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.sourceReceipt

/-- info: 'Draft.Checks.Schedule.middleReceipt' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.middleReceipt

/-- info: 'Draft.Checks.Schedule.frontValue' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Schedule.frontValue
