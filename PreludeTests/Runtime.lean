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
assumption on each call, and the machine of the program has evidence of it.

The third group has the laws of the run on a machine, for a computation that calls the program
two times: the run of a bind, the run of a substitution, and the machine of a composite. Each
check eliminates the identity of the law at an arbitrary runtime. The evidence of the
computation is built with the law of a bind, and it moves along the law of a substitution to
the calls of the state effect.

The fourth group has the two general sources of a verified implementation with a runtime: the
graph of the machine of an implementation, and a verified implementation with an invariant of
the runtime.

The fifth group has the congruence of a machine. Two writes and then a read, and one write and
then the value, have different calls and one run from each runtime. A read before each of them
keeps the congruence, and a check eliminates the identity of the two runs. -/

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

/-! The laws of the run on a machine. -/

/-- The rest after the first call: one more call, and the sum of the two responses. -/
def second (a : Nat) : Free Tick Nat := (Free.call ()).bind fun b => .pure (a + b)

/-- Two calls of the program, and the sum of the two responses. -/
def twice : Free Tick Nat := (Free.call ()).bind second

/-- The machine of the program. -/
abbrev tickMachine : Machine Tick Nat Empty := Machine.impl tick (stateMachine Nat)

/-- The last runtime of a result. -/
def last : Empty ⊕ (Nat × Nat) → Nat
  | .inr b => b.2

/-- The run of the two calls, for an arbitrary runtime. -/
def twiceRun (s : Nat) : tickMachine.run twice s ≡ .inr (s + (s + 1), s + 2) := .refl

/-- The identity of the run of a bind is consumed through a dependent payload, for an arbitrary
runtime. -/
def twiceRunBind (s : Nat) :
    (Identity.transport (fun out => Fin (last out + 1))
      (Machine.runBind tickMachine second (Free.call ()) s) ⟨s + 2, Nat.lt_succ_self _⟩).val ≡
      s + 2 := .refl

/-- The identity of the run of a substitution: the run of the substituted computation on the
machine of the state effect, and the run of the computation on the machine of the program. -/
def twiceRunSubst (s : Nat) :
    (Identity.transport (fun out => Fin (last out + 1))
      (Machine.runSubst tick (stateMachine Nat) twice s) ⟨s + 2, Nat.lt_succ_self _⟩).val ≡
      s + 2 := .refl

/-- The interface of the computation: one call that returns a number. -/
abbrev Pair : Container.{0, 0} := ⟨Unit, fun _ => Nat⟩

/-- The computation as an implementation by calls of the program. -/
def pair : Impl Pair Tick := fun _ => twice

/-- The machine of the composite is the machine of the first implementation on the machine of
the program. -/
def pairTrans (s : Nat) :
    (Identity.transport (fun out => Fin (last out + 1))
      (Machine.implTrans pair tick (stateMachine Nat) ((), s)) ⟨s + 2, Nat.lt_succ_self _⟩).val ≡
      s + 2 := .refl

/-- The machine of the implementation with one call is the machine. -/
def tickId (s : Nat) :
    (Identity.transport (fun out => Fin (last out + 1)) (Machine.implId tickMachine ((), s))
      ⟨s + 1, Nat.lt_succ_self _⟩).val ≡ s + 1 := .refl

/-- The evidence of one call of the program, for the specification of two runtimes. -/
def callDep (s : Nat) :
    FreeDep tickSpec (fun out => out ≡ .inr (s, s + 1)) ((Free.call (C := Tick) ()).thread s) :=
  .request () fun b post =>
    match b, post with
    | _, .refl => .pure .refl

/-- The evidence of the two calls, by the law of a bind. The rest receives the response and
the runtime of the first call. -/
def twiceDep (s : Nat) :
    FreeDep tickSpec (fun out => out ≡ .inr (s + (s + 1), s + 2)) (twice.thread s) :=
  FreeDep.threadBind (callDep s) fun b post =>
    match b, post with
    | _, .refl =>
        FreeDep.threadBind (f := fun b => .pure (s + b)) (callDep (s + 1)) fun b' post' =>
          match b', post' with
          | _, .refl => .pure .refl

/-- The evidence moves along the law of a substitution, to the calls of the state effect. The
run on the machine of the state effect gives the result of the two calls. -/
def twiceEvidence (s : Nat) :
    (stateMachine Nat).run (twice.subst tick) s ≡ .inr (s + (s + 1), s + 2) :=
  FreeDep.run (stateMachine Nat).graphEvidence ((twiceDep s).threadSubst tickDep)

/-- The evidence computes: it is the reflexivity at each runtime. -/
def twiceEvidenceRefl (s : Nat) : twiceEvidence s ≡ .refl := .refl

/-! The sources of a verified implementation with a runtime. -/

/-- The program is a verified implementation between the graphs of the two machines. -/
def tickGraph : ImplDep tickMachine.graph (stateMachine Nat).graph (Impl.thread tick) :=
  ImplDep.graph (Impl.thread tick) (stateMachine Nat)

/-- Its run with the machine of the state effect is the evidence of the graph of the machine
of the program. -/
def tickGraphRefl (s : Nat) :
    tickGraph.run (stateMachine Nat).graphEvidence ((), s) ⟨⟩ ≡ .refl := .refl

/-- The specification of the program for the state invariant: the response has the
invariant. -/
def tickBound (b : Nat) : DepPoly.{0, 0, 0, 0} Tick where
  Pre _ := Unit
  Post _ _ r := AtLeast b r

/-- The program is a verified implementation for the state invariant. -/
def tickBoundDep (b : Nat) : ImplDep (tickBound b) (Invariant Nat (AtLeast b)) tick :=
  fun _ _ => tickInvariant b

/-- The verified implementation with a runtime, on the machine of the state effect: the machine
of the program has evidence of the specification with the invariant of the runtime. -/
def tickBoundEvidence (b : Nat) :
    Evidence ((tickBound b).invariant (AtLeast b) (fun _ : Empty => Empty)) tickMachine :=
  (tickBoundDep b).thread.run (invariant Nat (AtLeast b))

/-- The invariant at the next runtime, for an arbitrary bound and an arbitrary number. -/
def tickBoundLast (b d : Nat) :
    (tickBoundEvidence b ((), b + d) (⟨d, .refl⟩, ())).2.1 ≡ d + 1 := .refl

/-! The congruence of a machine. -/

/-- Two writes, and then a read. -/
def writeTwice (a b : Nat) : Free (State Nat) Nat :=
  .request (.put a) fun _ => .request (.put b) fun _ => .request .get .pure

/-- One write, and then the value. -/
def writeOnce (b : Nat) : Free (State Nat) Nat := .request (.put b) fun _ => .pure b

/-- The two computations have different calls, and one run from each runtime. -/
def written (a b : Nat) :
    (stateMachine Nat).congruence.Rel (writeTwice a b) (writeOnce b) := fun _ => .refl

/-- A call keeps the congruence: a read, and then each of the two computations. -/
def readFirst (b : Nat) :
    (stateMachine Nat).congruence.Rel (.request .get fun s => writeTwice s b)
      (.request .get fun _ => writeOnce b) :=
  (stateMachine Nat).congruence.request .get fun s => written s b

/-- The identity of the two runs is consumed through a dependent payload, for an arbitrary
value and an arbitrary runtime. -/
def readFirstLast (b s : Nat) :
    (Identity.transport (fun out => Fin (last out + 1)) (readFirst b s)
      ⟨b, Nat.lt_succ_self _⟩).val ≡ b := .refl

/-- Agreement after the substitution of the program gives one run on the machine of the
program. -/
def twiceOfSubst (s : Nat) :
    (Identity.transport (fun out => Fin (last out + 1))
      (Machine.runOfSubst tick (stateMachine Nat) ((Free.Congruence.subst tick).refl twice) s)
      ⟨s + 2, Nat.lt_succ_self _⟩).val ≡ s + 2 := .refl

end PreludeTests.Runtime

/-- info: 'PreludeTests.Runtime.tickOutcomeLast' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.tickOutcomeLast

/-- info: 'PreludeTests.Runtime.tickEvidenceRefl' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.tickEvidenceRefl

/-- info: 'PreludeTests.Runtime.twiceRunBind' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.twiceRunBind

/-- info: 'PreludeTests.Runtime.twiceRunSubst' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.twiceRunSubst

/-- info: 'PreludeTests.Runtime.pairTrans' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.pairTrans

/-- info: 'PreludeTests.Runtime.tickId' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.tickId

/-- info: 'PreludeTests.Runtime.twiceEvidenceRefl' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.twiceEvidenceRefl

/-- info: 'PreludeTests.Runtime.tickGraphRefl' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.tickGraphRefl

/-- info: 'PreludeTests.Runtime.tickBoundLast' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.tickBoundLast

/-- info: 'PreludeTests.Runtime.readFirstLast' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.readFirstLast

/-- info: 'PreludeTests.Runtime.twiceOfSubst' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.twiceOfSubst
