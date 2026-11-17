import Draft.Diagram
import Draft.Checks.Free

/-! A loop that counts down.

The entrance of the loop has a counter and a value. The body tests the counter. At zero, it
exits from the loop with the value. At a successor, it has one effectful step on the value, and
it exits to the entrance with the predecessor of the counter and the response.

The first group has the function meaning. From the counter 2, a path has three entrances of
the loop. With three or more unrollings, the computation after the substitution of the
implementations is two calls of the store, for an arbitrary value and an arbitrary computation
at the limit. With two unrollings, the computation is the two calls and then the computation
at the limit. The body and then the loop is the same computation with one unrolling less.

The second group has a function of the calls with a runtime, and the values of the entrance
and of the exit, for the checks on this loop in other modules.

Each check sets `smartUnfolding false`. The definitions of the diagrams keep the default. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude

namespace Draft.Checks.Countdown

open Container
open Draft.Checks.Free (store provider)

inductive Op where
  | isZero
  | pred
  | emit

/-- One value type. `isZero` is a pure test: its output boundary has two cases with no port.
`pred` is pure. `emit` is effectful. -/
def sig : Signature Unit where
  Op := Op
  kind
    | .isZero => .pure
    | .pred => .pure
    | .emit => .effectful
  input _ := [()]
  output
    | .isZero => [[], []]
    | .pred => .one [()]
    | .emit => .one [()]

abbrev Value : Unit → Type := fun _ => Nat

/-- The entrance of the loop: a counter and a value. -/
abbrev Entry : Boundary Unit := .one [(), ()]

/-- The exit of the loop: the value. -/
abbrev Out : Boundary Unit := .one [()]

/-- One iteration. The first case of the test exits from the loop with the value. The second
case has the predecessor of the counter and one effectful step on the value, and it exits to
the entrance with the predecessor and the response. -/
def iteration : Diagram sig [(), ()] [Entry, Out] :=
  .step ⟨.isZero, .cons .here .nil⟩ fun
    | ⟨_, .here⟩ => .exit ⟨_, .there .here, Boundary.only _, .cons (.there .here) .nil⟩
    | ⟨_, .there .here⟩ =>
        .step ⟨.pred, .cons .here .nil⟩ (.one
          (.step ⟨.emit, .cons (.there (.there .here)) .nil⟩ (.one
            (.exit
              (Exits.At.here ⟨Boundary.only _, .cons (.there .here) (.cons .here .nil)⟩)))))

/-- The body of the loop: the iteration at the one case of the entrance. -/
def body : Continuation sig Entry [Entry, Out] := .one iteration

def loop : Continuation sig Entry [Out] := .loop body

/-- The exit to the entrance of the loop with the two inputs. -/
def enter {Qs : Exits Unit} : Diagram sig [(), ()] (Entry :: Qs) :=
  .exit (Exits.At.here ⟨Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩)

/-- The loop from the two inputs. -/
def countdown : Diagram sig [(), ()] [Out] := .seq enter loop

/-- The body, and then the loop. -/
def unpeeled : Diagram sig [(), ()] [Out] := .seq (.seq enter body) loop

def inputs (c a : Nat) : All Value [(), ()] := .cons c (.cons a .nil)

/-- The value of the one exit case. -/
def result : Exits.At [Out] Value → Nat
  | ⟨_, .here, ⟨_, .here⟩, out⟩ => out.lookup .here

/-- `isZero` and `pred` return without a call. The first case of `isZero` is the case of zero.
`emit` is one call of the store, and its response has the operand. -/
def lower : Impl (sig.interface Value) store
  | ⟨.isZero, args⟩ =>
      match args.lookup .here with
      | 0 => .pure ⟨⟨_, .here⟩, .nil⟩
      | _ + 1 => .pure ⟨⟨_, .there .here⟩, .nil⟩
  | ⟨.pred, args⟩ => .pure ⟨Boundary.only _, .cons (args.lookup .here).pred .nil⟩
  | ⟨.emit, args⟩ =>
      .request .one fun (m : Nat) => .pure ⟨Boundary.only _, .cons (m + args.lookup .here) .nil⟩

/-! The function meaning. -/

set_option smartUnfolding false in
/-- With three or more unrollings, the computation from the counter 2 is two calls of the
store. -/
def threeUnrollings (n a : Nat) (stop : Free (sig.interface Value) Nat) :
    (countdown.run stop (n + 3) (inputs 2 a) fun r => .pure (result r)).subst lower ≡
      .request .one fun (m₁ : Nat) => .request .one fun (m₂ : Nat) => .pure (m₂ + (m₁ + a)) :=
  .refl

set_option smartUnfolding false in
/-- With two unrollings, the third entrance is the computation at the limit. -/
def twoUnrollings (a : Nat) (stop : Free (sig.interface Value) Nat) :
    (countdown.run stop 2 (inputs 2 a) fun r => .pure (result r)).subst lower ≡
      .request .one fun _ => .request .one fun _ => stop.subst lower :=
  .refl

set_option smartUnfolding false in
/-- The body and then the loop, with two or more unrollings, is the same two calls. -/
def unpeeledCalls (n a : Nat) (stop : Free (sig.interface Value) Nat) :
    (unpeeled.run stop (n + 2) (inputs 2 a) fun r => .pure (result r)).subst lower ≡
      .request .one fun (m₁ : Nat) => .request .one fun (m₂ : Nat) => .pure (m₂ + (m₁ + a)) :=
  .refl

/-- The loop has one count of its body, and the body and then the loop has two. -/
def countdownSize : countdown.size ≡ 3 := .refl

def unpeeledSize : unpeeled.size ≡ 6 := .refl

/-! A function of the calls with a runtime. -/

/-- A function of the calls with a runtime. The runtime is the number of the calls of `emit`,
and `emit` returns the runtime plus its operand. -/
def handle : (a : (sig.interface Value).Shape) → Nat → (sig.interface Value).Pos a × Nat
  | ⟨.isZero, args⟩, s =>
      (match args.lookup .here with
        | 0 => ⟨⟨_, .here⟩, .nil⟩
        | _ + 1 => ⟨⟨_, .there .here⟩, .nil⟩, s)
  | ⟨.pred, args⟩, s => (⟨Boundary.only _, .cons (args.lookup .here).pred .nil⟩, s)
  | ⟨.emit, args⟩, s => (⟨Boundary.only _, .cons (s + args.lookup .here) .nil⟩, s + 1)

def entry (c a : Nat) : Entry.At Value := ⟨Boundary.only _, inputs c a⟩

def out (a : Nat) : Exits.At [Out] Value := ⟨_, .here, Boundary.only _, .cons a .nil⟩

/-- The response with one value. -/
def value (a : Nat) : (Boundary.one [()]).At Value := ⟨Boundary.only _, .cons a .nil⟩

#guard ((countdown.run (.pure 0) 5 (inputs 2 10) fun r => .pure (result r)).subst lower).run
  (provider true 3 4) == 16
#guard ((countdown.run (.pure 0) 2 (inputs 2 10) fun r => .pure (result r)).subst lower).run
  (provider true 3 4) == 0
#guard ((unpeeled.run (.pure 0) 2 (inputs 2 10) fun r => .pure (result r)).subst lower).run
  (provider true 3 4) == 16
#guard countdown.size == 3 && unpeeled.size == 6

end Draft.Checks.Countdown

/-- info: 'Draft.Checks.Countdown.threeUnrollings' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Countdown.threeUnrollings
