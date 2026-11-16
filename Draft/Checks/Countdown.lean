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

The second group has the run family, for a function of the calls with a runtime. A run of the
body continues or exits, and a run of the loop exists from each counter, for an arbitrary
value and an arbitrary runtime. The run of the whole diagram from the counter 2 has the value
and the runtime, and the first exit equation gives its run of the loop. The unrolling law and
the fixpoint law of `Prelude.Loop` apply to the run from the counter 2, and their round trips
hold by computation.

Each check and each run of the body sets `smartUnfolding false`. A run of the body has the
context of each step in its type, and with the default the elaborator normalizes that context
again at each step. The definitions of the diagrams keep the default. -/

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

/-! The run family. -/

/-- A function of the calls with a runtime. The runtime is the number of the calls of `emit`,
and `emit` returns the runtime plus its operand. -/
def handle : (a : (sig.interface Value).Shape) → Nat → (sig.interface Value).Pos a × Nat
  | ⟨.isZero, args⟩, s =>
      (match args.lookup .here with
        | 0 => ⟨⟨_, .here⟩, .nil⟩
        | _ + 1 => ⟨⟨_, .there .here⟩, .nil⟩, s)
  | ⟨.pred, args⟩, s => (⟨Boundary.only _, .cons (args.lookup .here).pred .nil⟩, s)
  | ⟨.emit, args⟩, s => (⟨Boundary.only _, .cons (s + args.lookup .here) .nil⟩, s + 1)

/-- The relation of calls: the graph of the function. -/
def calls : Signature.Calls.{0, 0} sig Value Nat := fun a s r s' => handle a s ≡ (r, s')

/-- One iteration of the loop, as a relation between an entrance with a runtime and its
result. -/
abbrev Step : Rel.{0, 0, 0} (Entry.At Value × Nat)
    ((Exits.At [Out] Value × Nat) ⊕ (Entry.At Value × Nat)) :=
  Continuation.Iteration.{0, 0} calls body

def entry (c a : Nat) : Entry.At Value := ⟨Boundary.only _, inputs c a⟩

def out (a : Nat) : Exits.At [Out] Value := ⟨_, .here, Boundary.only _, .cons a .nil⟩

/-- The response with one value. -/
def value (a : Nat) : (Boundary.one [()]).At Value := ⟨Boundary.only _, .cons a .nil⟩

set_option smartUnfolding false in
/-- A run of the body that continues: the test, the predecessor, and the effectful step, to
the exit to the entrance. -/
def continues (c a s : Nat) : Step (entry (c + 1) a, s) (.inr (entry c (s + a), s + 1)) :=
  ⟨(Exits.At.here (entry c (s + a)), s + 1),
    ⟨(⟨⟨_, .there .here⟩, .nil⟩, s), .refl, (value c, s), .refl, (value (s + a), s + 1), .refl,
      ⟨.refl⟩⟩,
    .refl⟩

set_option smartUnfolding false in
/-- A run of the body that exits: the test, to the exit of the loop. -/
def exits (a s : Nat) : Step (entry 0 a, s) (.inl (out a, s)) :=
  ⟨((out a).there Entry, s), ⟨(⟨⟨_, .here⟩, .nil⟩, s), .refl, ⟨.refl⟩⟩, .refl⟩

/-- A run of the loop from each counter, for an arbitrary value and an arbitrary runtime. -/
def runs : (c a s : Nat) → (r : Exits.At [Out] Value × Nat) × Loop Step (entry c a, s) r
  | 0, a, s => ⟨(out a, s), .exit (exits a s)⟩
  | c + 1, a, s =>
      ⟨(runs c (s + a) (s + 1)).1, .next (continues c a s) (runs c (s + a) (s + 1)).2⟩

/-- The run of the whole diagram from the counter 2, to the value and the runtime: the exit to
the entrance, and the run of the loop. -/
def fromTwo (a s : Nat) :
    countdown.Runs calls (inputs 2 a, s) (out ((s + 1) + (s + a)), s + 2) :=
  ⟨(Exits.At.here (entry 2 a), s), ⟨.refl⟩, (runs 2 a s).2⟩

set_option smartUnfolding false in
/-- The first exit equation gives the run of the loop from the run of the whole diagram. -/
def loopOfWhole (a s : Nat) :
    (Diagram.exitSeqRuns calls ⟨Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩ loop
      (inputs 2 a, s) _).to (fromTwo a s) ≡ (runs 2 a s).2 :=
  .refl

set_option smartUnfolding false in
/-- The round trip of the first exit equation at that run is the reflexivity. -/
def loopOfWholeBack (a s : Nat) :
    (Diagram.exitSeqRuns calls ⟨Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩ loop
      (inputs 2 a, s) _).invTo (fromTwo a s) ≡ .refl :=
  .refl

set_option smartUnfolding false in
/-- The run from the counter 2 has three runs of the body. -/
def runsLength (a s : Nat) : (runs 2 a s).2.length ≡ 3 := .refl

set_option smartUnfolding false in
/-- The unrolling law gives two runs of the body run twice. -/
def unrolledLength (a s : Nat) :
    ((Loop.unrolling Step _ _).to (runs 2 a s).2).length ≡ 2 := .refl

set_option smartUnfolding false in
/-- The inverse of the unrolling gives the first run. -/
def unrolledBack (a s : Nat) :
    (Loop.unrolling Step _ _).inv ((Loop.unrolling Step _ _).to (runs 2 a s).2) ≡
      (runs 2 a s).2 :=
  .refl

set_option smartUnfolding false in
/-- The round trip of the fixpoint law at the run is the reflexivity. -/
def fixpointBack (a s : Nat) : (Loop.fixpoint Step _ _).invTo (runs 2 a s).2 ≡ .refl := .refl

-- Compiled observations supplement the kernel checks above.
#guard ((countdown.run (.pure 0) 5 (inputs 2 10) fun r => .pure (result r)).subst lower).run
  (provider true 3 4) == 16
#guard ((countdown.run (.pure 0) 2 (inputs 2 10) fun r => .pure (result r)).subst lower).run
  (provider true 3 4) == 0
#guard ((unpeeled.run (.pure 0) 2 (inputs 2 10) fun r => .pure (result r)).subst lower).run
  (provider true 3 4) == 16
#guard countdown.size == 3 && unpeeled.size == 6

end Draft.Checks.Countdown
