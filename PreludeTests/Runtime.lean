import Prelude

/-! Machines, and specifications of an interface with a runtime.

The interface is the interface of a cell, which is Aberlé's state effect, and its machine has
the value as its runtime. The program reads the counter, writes its successor, and returns the
value of the read.

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
the runtime. The invariant of the runtime applies also to a specification whose precondition is
one level above its postcondition: a witness of the precondition has a family of types.

The fifth group has the congruence of a machine. Two writes and then a read, and one write and
then the value, have different calls and one run from each runtime. A read before each of them
keeps the congruence, and a check eliminates the identity of the two runs.

The sixth group has a lens of runtimes: the first part of a pair. Its two squares hold by
computation, and each of its three laws is the reflexivity. The composite of two such lenses is
lawful by the composition of homomorphisms, and its laws compute. The machine of the cell
along the lens has a runtime with a second part, which stays. A cell of pairs implements the
cell of the first part, and the two computations of the fifth group have one run on the machine
of the cell of pairs, in a continuation that reads the cell again. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude Container

namespace PreludeTests.Runtime

/-- The interface of the program: one call that returns a number. -/
abbrev Tick : Container.{0, 0} := ⟨Unit, fun _ => Nat⟩

/-- Read the counter, write its successor, and return the value of the read. -/
def tick : Impl Tick (cell Nat) := fun _ =>
  .request .get fun (s : Nat) => .request (.put (s + 1)) fun _ => .pure s

/-- The machine of the program has the value of the read, and the successor as its next
runtime. -/
def tickRun (s : Nat) : Machine.impl tick (Machine.cell Nat Empty) ((), s) ≡ .inr (s, s + 1) := .refl

/-! The state invariant. -/

/-- A write has the invariant at its value, and a read gives the invariant at its response. -/
def Invariant (S : Type) (T : S → Type) : DepPoly.{0, 0, 0, 0} (cell S) where
  Pre
    | .get => Unit
    | .put s => T s
  Post
    | .get, _, s => T s
    | .put _, _, _ => Unit

/-- The machine has evidence of the specification with the invariant of the runtime. -/
def invariant (S : Type) (T : S → Type) :
    Evidence ((Invariant S T).invariant T (fun _ : Empty => Empty)) (Machine.cell S Empty)
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
def tickDep : ImplDep tickSpec (Machine.cell Nat Empty).graph (Impl.thread tick) := fun _ _ =>
  .request ⟨⟩ fun b post =>
    match b, post with
    | _, .refl =>
        .request ⟨⟩ fun b' post' =>
          match b', post' with
          | _, .refl => .pure .refl

/-- The machine of the program has evidence of the specification: the run of the verified
implementation with the machine, which has evidence of its graph. -/
def tickEvidence : Evidence tickSpec (Machine.impl tick (Machine.cell Nat Empty)) :=
  tickDep.run (Machine.cell Nat Empty).graphEvidence

/-- The evidence computes: it is the reflexivity at each runtime. -/
def tickEvidenceRefl (s : Nat) : tickEvidence ((), s) () ≡ .refl := .refl

/-! The laws of the run on a machine. -/

/-- The rest after the first call: one more call, and the sum of the two responses. -/
def second (a : Nat) : Free Tick Nat := (Free.call ()).bind fun b => .pure (a + b)

/-- Two calls of the program, and the sum of the two responses. -/
def twice : Free Tick Nat := (Free.call ()).bind second

/-- The machine of the program. -/
abbrev tickMachine : Machine Tick Nat Empty := Machine.impl tick (Machine.cell Nat Empty)

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
      (Machine.runSubst tick (Machine.cell Nat Empty) twice s) ⟨s + 2, Nat.lt_succ_self _⟩).val ≡
      s + 2 := .refl

/-- The interface of the computation: one call that returns a number. -/
abbrev Pair : Container.{0, 0} := ⟨Unit, fun _ => Nat⟩

/-- The computation as an implementation by calls of the program. -/
def pair : Impl Pair Tick := fun _ => twice

/-- The machine of the composite is the machine of the first implementation on the machine of
the program. -/
def pairTrans (s : Nat) :
    (Identity.transport (fun out => Fin (last out + 1))
      (Machine.implTrans pair tick (Machine.cell Nat Empty) ((), s)) ⟨s + 2, Nat.lt_succ_self _⟩).val ≡
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
    (Machine.cell Nat Empty).run (twice.subst tick) s ≡ .inr (s + (s + 1), s + 2) :=
  FreeDep.run (Machine.cell Nat Empty).graphEvidence ((twiceDep s).threadSubst tickDep)

/-- The evidence computes: it is the reflexivity at each runtime. -/
def twiceEvidenceRefl (s : Nat) : twiceEvidence s ≡ .refl := .refl

/-! The sources of a verified implementation with a runtime. -/

/-- The program is a verified implementation between the graphs of the two machines. -/
def tickGraph : ImplDep tickMachine.graph (Machine.cell Nat Empty).graph (Impl.thread tick) :=
  ImplDep.graph (Impl.thread tick) (Machine.cell Nat Empty)

/-- Its run with the machine of the state effect is the evidence of the graph of the machine
of the program. -/
def tickGraphRefl (s : Nat) :
    tickGraph.run (Machine.cell Nat Empty).graphEvidence ((), s) ⟨⟩ ≡ .refl := .refl

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

/-- A specification of the program whose precondition is one level above its postcondition. A
witness of the precondition is a family of types on the numbers, with an element at each
number that has the invariant. The postcondition is the family at the response. -/
def tickFamily (b : Nat) : DepPoly.{0, 0, 1, 0} Tick where
  Pre _ := (P : Nat → Type) × ((r : Nat) → AtLeast b r → P r)
  Post _ pre r := pre.1 r

/-- The program is a verified implementation of it for the state invariant: the element at the
value of the read, from the invariant at that value. -/
def tickFamilyDep (b : Nat) : ImplDep (tickFamily b) (Invariant Nat (AtLeast b)) tick :=
  fun _ pre =>
    .request () fun r t =>
      .request ⟨t.1 + 1, Identity.cong (fun k => k + 1) t.2⟩ fun _ _ => .pure (pre.2 r t)

/-- The verified implementation with a runtime. The specification with the invariant of the
runtime has its precondition at the level of the family, and its postcondition at the level of
the invariant. -/
def tickFamilyEvidence (b : Nat) :
    Evidence ((tickFamily b).invariant (AtLeast b) (fun _ : Empty => Empty)) tickMachine :=
  (tickFamilyDep b).thread.run (invariant Nat (AtLeast b))

/-- The element of the family of the witness at the response has the number of the invariant
at the read, for an arbitrary bound and an arbitrary number. -/
def tickFamilyValue (b d : Nat) :
    (tickFamilyEvidence b ((), b + d)
      (⟨d, .refl⟩, ⟨fun _ => Nat × Nat, fun r t => (t.1, r)⟩)).1 ≡ (d, b + d) := .refl

/-! The congruence of a machine. -/

/-- Two writes, and then a read. -/
def writeTwice (a b : Nat) : Free (cell Nat) Nat :=
  .request (.put a) fun _ => .request (.put b) fun _ => .request .get .pure

/-- One write, and then the value. -/
def writeOnce (b : Nat) : Free (cell Nat) Nat := .request (.put b) fun _ => .pure b

/-- The two computations have different calls, and one run from each runtime. -/
def written (a b : Nat) :
    (Machine.cell Nat Empty).congruence.Rel (writeTwice a b) (writeOnce b) := fun _ => .refl

/-- A call keeps the congruence: a read, and then each of the two computations. -/
def readFirst (b : Nat) :
    (Machine.cell Nat Empty).congruence.Rel (.request .get fun s => writeTwice s b)
      (.request .get fun _ => writeOnce b) :=
  (Machine.cell Nat Empty).congruence.request .get fun s => written s b

/-- The identity of the two runs is consumed through a dependent payload, for an arbitrary
value and an arbitrary runtime. -/
def readFirstLast (b s : Nat) :
    (Identity.transport (fun out => Fin (last out + 1)) (readFirst b s)
      ⟨b, Nat.lt_succ_self _⟩).val ≡ b := .refl

/-- Agreement after the substitution of the program gives one run on the machine of the
program. -/
def twiceOfSubst (s : Nat) :
    (Identity.transport (fun out => Fin (last out + 1))
      (Machine.runOfSubst tick (Machine.cell Nat Empty) ((Free.Congruence.subst tick).refl twice) s)
      ⟨s + 2, Nat.lt_succ_self _⟩).val ≡ s + 2 := .refl

/-! A lens of runtimes. -/

/-- The lens to the first part of a pair: the view is the first part, and the update replaces
it. -/
def first (A Q : Type) : Hom (state (A × Q)) (state A) where
  shape s := s.1
  position s a := (a, s.2)

/-- The lens is lawful: the counit square and the comultiplication square hold by
computation. -/
def firstLawful (A Q : Type) : (first A Q).Lawful where
  counit _ := .refl
  comult _ := ⟨.refl, fun _ => .refl, fun _ _ => .refl⟩

/-- Each of the three laws of the lens is the reflexivity, at arbitrary values. -/
def firstViewUpdate (A Q : Type) (s : A × Q) (a : A) :
    (firstLawful A Q).viewUpdate s a ≡ .refl := .refl

def firstUpdateView (A Q : Type) (s : A × Q) : (firstLawful A Q).updateView s ≡ .refl := .refl

def firstUpdateUpdate (A Q : Type) (s : A × Q) (a b : A) :
    (firstLawful A Q).updateUpdate s a b ≡ .refl := .refl

/-- The lens from its three laws is the same homomorphism. -/
def firstOfLaws (A Q : Type) :
    Hom.Lawful.ofLaws (ℓ := first A Q) (fun _ _ => .refl) (fun _ => .refl)
      (fun _ _ _ => .refl) ≡ firstLawful A Q := .refl

/-- The first part of the first part: the composite of two lenses, which is lawful by the
composition of homomorphisms. -/
def firstTwo (A Q Q' : Type) : ((first (A × Q) Q').trans (first A Q)).Lawful :=
  (firstLawful (A × Q) Q').trans (firstLawful A Q)

/-- Each of the three laws of the composite is the reflexivity, at arbitrary values. -/
def firstTwoViewUpdate (A Q Q' : Type) (s : (A × Q) × Q') (a : A) :
    (firstTwo A Q Q').viewUpdate s a ≡ .refl := .refl

def firstTwoUpdateView (A Q Q' : Type) (s : (A × Q) × Q') :
    (firstTwo A Q Q').updateView s ≡ .refl := .refl

def firstTwoUpdateUpdate (A Q Q' : Type) (s : (A × Q) × Q') (a b : A) :
    (firstTwo A Q Q').updateUpdate s a b ≡ .refl := .refl

/-- The machine of the cell on the first part of a runtime with a second part. -/
abbrev wide : Machine (cell Nat) (Nat × Nat) Empty :=
  (Machine.cell Nat Empty).along (first Nat Nat)

/-- The last value of the cell in a result on the runtime with a second part. -/
def lastWide : Empty ⊕ (Nat × (Nat × Nat)) → Nat
  | .inr b => b.2.1

/-- The run of the two calls of the program on the whole runtime. The second part stays. -/
def twiceWide (s q : Nat) :
    wide.run (twice.subst tick) (s, q) ≡ .inr (s + (s + 1), (s + 2, q)) := .refl

/-- The law of the run along the lens is consumed through a dependent payload, for an
arbitrary runtime. -/
def twiceAlong (s q : Nat) :
    (Identity.transport (fun out => Fin (lastWide out + 1))
      (Machine.runAlong (firstLawful Nat Nat) (Machine.cell Nat Empty) (twice.subst tick) (s, q))
      ⟨s + 2, Nat.lt_succ_self _⟩).val ≡ s + 2 := .refl

/-- The cell of the first part, by the calls of a cell of pairs. A read is one call, and a
write is a read and a write of the pair with the new first part. -/
def part : Impl (cell Nat) (cell (Nat × Nat))
  | .get => .request .get fun (s : Nat × Nat) => .pure s.1
  | .put a => .request .get fun (s : Nat × Nat) => .request (.put (a, s.2)) fun _ => .pure ⟨⟩

/-- The machine of the implementation is the machine of the cell along the lens. -/
def partAlong :
    Homotopy ((Machine.cell (Nat × Nat) Empty).impl part)
      ((Machine.cell Nat Empty).along (first Nat Nat))
  | (.get, _) => .refl
  | (.put _, _) => .refl

/-- The continuation that reads the cell of pairs again. -/
def again (v : Nat) : Free (cell (Nat × Nat)) Nat :=
  .request .get fun (s : Nat × Nat) => .pure (v + s.1 + s.2)

/-- The two computations of the cell have one run on the machine of the cell of pairs, after
the implementation and in the continuation. -/
def writtenWide (a b : Nat) (s : Nat × Nat) :
    (Machine.cell (Nat × Nat) Empty).run (((writeTwice a b).subst part).bind again) s ≡
      (Machine.cell (Nat × Nat) Empty).run (((writeOnce b).subst part).bind again) s :=
  Machine.alongCongr (firstLawful Nat Nat) (Machine.cell Nat Empty) part
    (Machine.cell (Nat × Nat) Empty) partAlong (written a b) again s

/-- The returned value of a result on the runtime of pairs. -/
def returnedWide : Empty ⊕ (Nat × (Nat × Nat)) → Nat
  | .inr b => b.1

/-- The identity of the two runs is consumed through a dependent payload, for arbitrary
values and an arbitrary runtime. -/
def writtenWideValue (a b c q : Nat) :
    (Identity.transport (fun out => Fin (returnedWide out + 1)) (writtenWide a b (c, q))
      ⟨b + b + q, Nat.lt_succ_self _⟩).val ≡ b + b + q := .refl

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

/-- info: 'PreludeTests.Runtime.tickFamilyValue' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.tickFamilyValue

/-- info: 'PreludeTests.Runtime.readFirstLast' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.readFirstLast

/-- info: 'PreludeTests.Runtime.twiceOfSubst' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.twiceOfSubst

/-- info: 'PreludeTests.Runtime.firstUpdateUpdate' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.firstUpdateUpdate

/-- info: 'PreludeTests.Runtime.firstOfLaws' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.firstOfLaws

/-- info: 'PreludeTests.Runtime.firstTwoViewUpdate' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.firstTwoViewUpdate

/-- info: 'PreludeTests.Runtime.firstTwoUpdateUpdate' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.firstTwoUpdateUpdate

/-- info: 'PreludeTests.Runtime.twiceAlong' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.twiceAlong

/-- info: 'PreludeTests.Runtime.writtenWideValue' does not depend on any axioms -/
#guard_msgs in
#print axioms PreludeTests.Runtime.writtenWideValue

/-- info: 'Prelude.Container.Comonoid.stateAssoc' does not depend on any axioms -/
#guard_msgs in
#print axioms Prelude.Container.Comonoid.stateAssoc

/-- info: 'Prelude.Container.cell.putGet' does not depend on any axioms -/
#guard_msgs in
#print axioms Prelude.Container.cell.putGet
