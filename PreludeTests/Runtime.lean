import Prelude

/-! Machines, and specifications of an interface with a runtime.

The interface is Aberlé's state effect, and its machine has the state as its runtime. The
program reads the counter, writes its successor, and returns the value of the read.

The first group has her state invariant: a specification of the interface with no runtime, and
an invariant of the runtime. The evidence of the program moves to the interface with the
runtime, and the run on the machine gives the invariant at the last runtime.

The second group has a specification that relates two runtimes: the response is the runtime
before, and the runtime after is its successor. An invariant of one runtime cannot say this.
The program is a verified implementation of it, with the graph of the machine as the
assumption on each call, and the machine of the program has evidence of it. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude Container

namespace PreludeTests.Runtime

inductive StateI (S : Type) : Type where
  | get
  | put (s : S)

/-- The state effect: a read has the state, and a write has no value. -/
def State (S : Type) : Container.{0, 0} :=
  ⟨StateI S, fun
    | .get => S
    | .put _ => Unit⟩

/-- The machine of the state effect. It does not stop. -/
def stateMachine (S : Type) : Machine (State S) S Empty
  | (.get, s) => .inr (s, s)
  | (.put s', _) => .inr ((), s')

/-- The interface of the program: one call that returns a number. -/
abbrev Tick : Container.{0, 0} := ⟨Unit, fun _ => Nat⟩

/-- Read the counter, write its successor, and return the value of the read. -/
def tick : Impl Tick (State Nat) := fun _ =>
  .request .get fun (s : Nat) => .request (.put (s + 1)) fun _ => .pure s

/-- The machine of the program has the value of the read, and the successor as its next
runtime. -/
def tickRun (s : Nat) : Machine.impl tick (stateMachine Nat) ((), s) ≡ .inr (s, s + 1) := .refl

/-! The state invariant. -/

/-- A write has the invariant at its value, and a read gives the invariant at its response. -/
def Invariant (S : Type) (T : S → Type) : DepPoly.{0, 0, 0, 0} (State S) where
  Pre
    | .get => Unit
    | .put s => T s
  Post
    | .get, _, s => T s
    | .put _, _, _ => Unit

/-- The machine has evidence of the specification with the invariant of the runtime. -/
def invariant (S : Type) (T : S → Type) :
    Evidence ((Invariant S T).invariant T (fun _ : Empty => Empty)) (stateMachine S)
  | (.get, _), (t, _) => (t, t)
  | (.put _, _), (_, t') => ((), t')

/-- The invariant: the state is a lower bound plus a number. -/
abbrev AtLeast (b : Nat) (s : Nat) : Type := (d : Nat) × (s ≡ b + d)

/-- The evidence of the program for the state invariant. The write has the invariant at the
successor, from the invariant at the read. -/
def tickInvariant (b : Nat) :
    FreeDep (Invariant Nat (AtLeast b)) (fun r => AtLeast b r) (tick ()) :=
  .request () fun _ t =>
    .request ⟨t.1 + 1, Identity.cong (fun k => k + 1) t.2⟩ fun _ _ => .pure t

/-- The evidence at the result of the run on the machine: the invariant at the returned value,
and the invariant at the last runtime. -/
def tickOutcome (b d : Nat) :=
  FreeDep.run (invariant Nat (AtLeast b))
    ((tickInvariant b).thread (Z := fun _ : Empty => Empty) (b + d) ⟨d, .refl⟩)

/-- The invariant at the last runtime has one more than the number of the first runtime, for
an arbitrary bound and an arbitrary number. -/
def tickOutcomeLast (b d : Nat) : (tickOutcome b d).2.1 ≡ d + 1 := .refl

def tickOutcomeValue (b d : Nat) : (tickOutcome b d).1.1 ≡ d := .refl

/-! A specification of two runtimes. -/

/-- The response is the runtime before the call, and the runtime after it is its successor. -/
def tickSpec : DepPoly.{0, 0, 0, 0} (Tick.runtime Nat Empty) where
  Pre _ := Unit
  Post a _ b := b ≡ .inr (a.2, a.2 + 1)

/-- The program is a verified implementation of the specification, with the graph of the
machine as the assumption on each call. -/
def tickDep : ImplDep tickSpec (stateMachine Nat).graph (Impl.thread tick) := fun _ _ =>
  .request ⟨⟩ fun b post =>
    match b, post with
    | _, .refl =>
        .request ⟨⟩ fun b' post' =>
          match b', post' with
          | _, .refl => .pure .refl

/-- The machine of the program has evidence of the specification: the run of the verified
implementation with the machine, which has evidence of its graph. -/
def tickEvidence : Evidence tickSpec (Machine.impl tick (stateMachine Nat)) :=
  tickDep.run (stateMachine Nat).graphEvidence

/-- The evidence computes: it is the reflexivity at each runtime. -/
def tickEvidenceRefl (s : Nat) : tickEvidence ((), s) () ≡ .refl := .refl

end PreludeTests.Runtime

/-- info: 'PreludeTests.Runtime.tickOutcomeLast' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.tickOutcomeLast

/-- info: 'PreludeTests.Runtime.tickEvidenceRefl' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.tickEvidenceRefl
