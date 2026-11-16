import Draft.Sequentialization
import Draft.Checks.Diagram

/-! The orders of three steps.

`A` and `B` are pure, and `B` uses the output of `A`. `C` is effectful and uses the first input
only. The source diagram has the order `A B C`.

`C` is ready in the source diagram: it moves past `B` and then past `A`. Three schedules give
the orders `A B C`, `A C B`, and `C A B`. Each realization has its steps in that order. Each
gives the same two values, for arbitrary inputs and an arbitrary response of the store. The
derivation of each schedule is in the interchange equation set, and a check consumes its
soundness through a dependent payload that has the response of the store. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude

namespace Draft.Checks.Schedule

open Container
open Draft.Checks.Free (store provider)
open Draft.Checks.Diagram (Op sig Value lower returns inputs values observe)

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
