import Draft.Runtime
import Draft.Checks.Countdown
import Draft.Specification.Completeness
import Draft.Specification.Machine
import Draft.Specification.Derivation
import Draft.Specification.Peel

/-! Checks of the specification of a diagram, on the countdown loop.

Each check has an arbitrary value and an arbitrary runtime. The first group has the round trip
of a run through the computation with a number of unrollings, and the same for a loop in a
loop. The second group has the run that the result of the function meaning on a machine has,
for a bound over the witness of the graph of the machine and an arbitrary computation at the
limit. The third group has the two exit equations and the laws of the loop at a run of the
specification, with their round trips. The fourth group has the equivalence of the runs over
the witness that a derivation gives, with its two round trips, for a derivation with no rule
and for a derivation with the second exit equation between two different loops.

The last groups have the evidence that the constructors give. The condition at the result of a
run over the witness goes through the invariant of each iteration. With the empty condition at
the limit, a family with a count gives the verified implementation of the approximant for each
counter that is less than the number of unrollings. The same holds for a loop in a loop, where
one number of unrollings is for the two loops. The evidence of a loop with no count moves along
a derivation with a rule under the loop, and along the peel of the loop, and the moved evidence
is a part under the constructor of a composite. Each of these checks consumes the moved
evidence at a run of the second diagram over the moved witness. The evidence of the machine of
the countdown with a real bound moves along the derivation, with the same number of
unrollings: the two approximants have one machine. The peeled diagram with a real bound needs
one unrolling less. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude Container

namespace Draft.Checks.Specification

open Draft Draft.Checks.Countdown

/-- A machine with a response at each call. -/
def machine : Machine (sig.interface Value) Nat Unit := fun a => .inr (handle a.1 a.2)

abbrev G : DepPoly.{0, 0, 0, 0} ((sig.interface Value).runtime Nat Unit) := machine.graph

abbrev Res : Type := Unit ⊕ (Option (Exits.At [Out] Value) × Nat)

/-- The condition at a result of an approximant of a continuation, over a witness: the runs to
a stop, the runs to an exit, and no condition at the limit. -/
def Seen (k : Continuation sig Entry [Out]) (x : Entry.At Value × Nat) (w : (Continuation.spec G k).Pre x) :
    Res → Type
  | .inl e => (Continuation.spec G k).Post x w (.inl e)
  | .inr (some q, s') => (Continuation.spec G k).Post x w (.inr (q, s'))
  | .inr (none, _) => PUnit

/-- The rest that returns the run. -/
def returns (k : Continuation sig Entry [Out]) (x : Entry.At Value × Nat) (w : (Continuation.spec G k).Pre x) :
    (m : Unit ⊕ (Exits.At [Out] Value × Nat)) → (Continuation.spec G k).Post x w m →
    FreeDep G (Seen k x w)
      (Free.resume (fun q => (Free.pure (some q) : Free (sig.interface Value) _)) m)
  | .inl e, run => FreeDep.pure (Q := Seen k x w) (value := Sum.inl e) run
  | .inr y, run => FreeDep.pure (Q := Seen k x w) (value := Sum.inr (some y.1, y.2)) run

/-- The evidence at the limit: no condition. -/
def limitEv (k : Continuation sig Entry [Out]) (x : Entry.At Value × Nat) (w : (Continuation.spec G k).Pre x)
    (s₀ : Nat) :
    FreeDep G (Seen k x w)
      ((Free.pure none : Free (sig.interface Value) (Option (Exits.At [Out] Value))).thread s₀) :=
  FreeDep.pure (Q := Seen k x w) (value := Sum.inr (none, s₀)) PUnit.unit

/-! The loop of the countdown. -/

def keepsAll : (iterSpec G body).Keeps fun _ => PUnit :=
  fun a' _ => ⟨Continuation.witness G (fun _ => PUnit.unit) body a', fun _ _ => PUnit.unit⟩

def wit (c a s : Nat) : (Continuation.spec G loop).Pre (entry c a, s) := ⟨fun _ => PUnit, PUnit.unit, keepsAll⟩

abbrev StepS := (iterSpec G body).iterate keepsAll

set_option smartUnfolding false in
def goes (c a s : Nat) :
    StepS ⟨(entry (c + 1) a, s), PUnit.unit⟩ (.inr ⟨(entry c (s + a), s + 1), PUnit.unit⟩) :=
  ⟨⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s), .refl, .inr (value c, s), .refl,
      .inr (value (s + a), s + 1), .refl, ⟨.refl⟩⟩,
    .refl⟩

set_option smartUnfolding false in
def ends (a s : Nat) : StepS ⟨(entry 0 a, s), PUnit.unit⟩ (.inl (.inr (out a, s))) :=
  ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s), .refl, ⟨.refl⟩⟩

def runsS : (c a s : Nat) → (r : Exits.At [Out] Value × Nat) ×
    Loop StepS ⟨(entry c a, s), PUnit.unit⟩ (.inr r)
  | 0, a, s => ⟨(out a, s), .exit (ends a s)⟩
  | c + 1, a, s => ⟨(runsS c (s + a) (s + 1)).1, .next (goes c a s) (runsS c (s + a) (s + 1)).2⟩

/-- Completeness at the run from the counter 2. -/
def alongTwo (a s : Nat) :=
  Continuation.along G (limitEv loop (entry 2 a, s) (wit 2 a s)) loop (entry 2 a) s (wit 2 a s)
    (.inr (runsS 2 a s).1) (runsS 2 a s).2

set_option smartUnfolding false in
/-- The threshold of the run is the number of its runs of the body. -/
def thresholdTwo (a s : Nat) : (alongTwo a s).1 ≡ 3 := .refl

set_option smartUnfolding false in
/-- The run of the approximant with three unrollings, along the evidence. -/
def treeTwo (a s : Nat) :=
  (alongTwo a s).2 3 (Nat.le_refl 3) (fun q => .pure (some q))
    (returns loop (entry 2 a, s) (wit 2 a s))
    (.inr (some (runsS 2 a s).1.1, (runsS 2 a s).1.2)) ⟨.refl⟩

set_option smartUnfolding false in
/-- The round trip: the condition at the result of that run of the approximant is the run of
the loop, for an arbitrary value and an arbitrary runtime. -/
def roundTrip (a s : Nat) : FreeDep.atRun _ _ (treeTwo a s) ≡ (runsS 2 a s).2 := .refl

end Draft.Checks.Specification

namespace Draft.Checks.Specification

open Draft Draft.Checks.Countdown

/-! The countdown with a name for each rest, and an arbitrary computation at the limit. -/

def afterEmit : (c : (sig.output .emit).Case) → Diagram sig (c.1 ++ [(), (), ()]) [Entry, Out] :=
  Diagram.one
    (.exit (Exits.At.here ⟨Boundary.only _, .cons (.there .here) (.cons .here .nil)⟩))

def afterPred : (c : (sig.output .pred).Case) → Diagram sig (c.1 ++ [(), ()]) [Entry, Out] :=
  Diagram.one (.step ⟨.emit, .cons (.there (.there .here)) .nil⟩ afterEmit)

def afterTest : (c : (sig.output .isZero).Case) → Diagram sig (c.1 ++ [(), ()]) [Entry, Out]
  | ⟨_, .here⟩ => .exit ⟨_, .there .here, Boundary.only _, .cons (.there .here) .nil⟩
  | ⟨_, .there .here⟩ => .step ⟨.pred, .cons .here .nil⟩ afterPred

def bodyN : Continuation sig Entry [Entry, Out] :=
  .one (.step ⟨.isZero, .cons .here .nil⟩ afterTest)

def loopN : Continuation sig Entry [Out] := .loop bodyN

def keepsN : (iterSpec G bodyN).Keeps fun _ => PUnit :=
  fun a' _ => ⟨Continuation.graphWitness machine bodyN a', fun _ _ => PUnit.unit⟩

def witN (c a s : Nat) : (Continuation.spec G loopN).Pre (entry c a, s) :=
  ⟨fun _ => PUnit, PUnit.unit, keepsN⟩

abbrev Never : Nat → Type := fun _ => PEmpty

set_option smartUnfolding false in
def bodyIn (n c a s : Nat) :
    bodyN.Within G Never n (entry (c + 1) a, s)
      (Continuation.graphWitness machine bodyN (entry (c + 1) a, s)) :=
  stepWithin machine Never n ⟨.isZero, .cons .here .nil⟩ afterTest (inputs (c + 1) a, s) _
    (stepWithin machine Never n ⟨.pred, .cons .here .nil⟩ afterPred (inputs (c + 1) a, s) _
      (stepWithin machine Never n ⟨.emit, .cons (.there (.there .here)) .nil⟩ afterEmit
        (.cons c (inputs (c + 1) a), s) _ PUnit.unit))

set_option smartUnfolding false in
def bodyIn0 (n a s : Nat) :
    bodyN.Within G Never n (entry 0 a, s)
      (Continuation.graphWitness machine bodyN (entry 0 a, s)) :=
  stepWithin machine Never n ⟨.isZero, .cons .here .nil⟩ afterTest (inputs 0 a, s) _ PUnit.unit

set_option smartUnfolding false in
/-- Each run of the body from a counter that is not zero gives the next entrance. -/
def bodyNext (c a s : Nat) (m : Unit ⊕ (Exits.At [Entry, Out] Value × Nat))
    (run : (Continuation.spec G bodyN).Post (entry (c + 1) a, s)
      (Continuation.graphWitness machine bodyN (entry (c + 1) a, s)) m) :
    (Sum.inr (Exits.At.here (entry c (s + a)), s + 1) :
      Unit ⊕ (Exits.At [Entry, Out] Value × Nat)) ≡ m :=
  (stepPost machine ⟨.emit, .cons (.there (.there .here)) .nil⟩ afterEmit
    (.cons c (inputs (c + 1) a), s) _ m
    (stepPost machine ⟨.pred, .cons .here .nil⟩ afterPred (inputs (c + 1) a, s) _ m
      (stepPost machine ⟨.isZero, .cons .here .nil⟩ afterTest (inputs (c + 1) a, s) _ m
        run))).down

set_option smartUnfolding false in
/-- Each run of the body from the counter zero is the exit of the loop. -/
def bodyDone (a s : Nat) (m : Unit ⊕ (Exits.At [Entry, Out] Value × Nat))
    (run : (Continuation.spec G bodyN).Post (entry 0 a, s)
      (Continuation.graphWitness machine bodyN (entry 0 a, s)) m) :
    (Sum.inr ((out a).there Entry, s) : Unit ⊕ (Exits.At [Entry, Out] Value × Nat)) ≡ m :=
  (stepPost machine ⟨.isZero, .cons .here .nil⟩ afterTest (inputs 0 a, s) _ m run).down

/-- The bound of the loop: from the counter `c`, `c + 1` unrollings are sufficient, for an
arbitrary value and an arbitrary runtime. -/
def bound (n : Nat) : (c a s : Nat) →
    LoopBound G Never n bodyN keepsN (c + 1) ⟨(entry c a, s), PUnit.unit⟩
  | 0, a, s =>
      ⟨bodyIn0 n a s, fun _ post =>
        (Identity.inlNotInr
          (Identity.cong (result (X := Value) (R := Nat) (E := Unit) (K := Entry) (Qs := [Out]))
            (bodyDone a s _ post))).elim⟩
  | c + 1, a, s =>
      ⟨bodyIn n c a s, fun _ post =>
        Identity.transport
          (fun a' => LoopBound G Never n bodyN keepsN (c + 1) ⟨a', PUnit.unit⟩)
          (Identity.inrInject
            (Identity.cong (result (X := Value) (R := Nat) (E := Unit) (K := Entry) (Qs := [Out]))
              (bodyNext c a s _ post)))
          (bound n c (s + a) (s + 1))⟩

/-- The result of the function meaning on the machine has a run of the loop, for an arbitrary
computation at the limit. The evidence of the approximant is from the witness and the bound,
with the empty condition at the limit. -/
def resultRun (stop : Free (sig.interface Value) (Exits.At [Out] Value)) (c a s : Nat) :
    (Continuation.spec G loopN).Post (entry c a, s) (witN c a s)
      (((loopN.run stop (c + 1) (entry c a) .pure).thread s).run machine) :=
  FreeDep.run (Section.graphEvidence machine)
    (Continuation.evidenceAt G Never
      (F := fun o => (Continuation.spec G loopN).Post (entry c a, s) (witN c a s) o)
      (stop := stop) (fun _ e => nomatch e) (c + 1) loopN (entry c a) s (witN c a s)
      (bound (c + 1) c a s) .pure fun m run =>
        Sum.casesOn
          (motive := fun m => (Continuation.spec G loopN).Post (entry c a, s) (witN c a s) m →
            FreeDep G (fun o => (Continuation.spec G loopN).Post (entry c a, s) (witN c a s) o)
              (Free.resume .pure m))
          m (fun _ run => .pure run) (fun _ run => .pure run) run)

def lengthAt {c a s : Nat} {o : Unit ⊕ (Exits.At [Out] Value × Nat)}
    (run : (Continuation.spec G loopN).Post (entry c a, s) (witN c a s) o) : Nat :=
  Loop.length (F := (iterSpec G bodyN).iterate keepsN) run

set_option smartUnfolding false in
/-- From the counter 2 with three unrollings, the run has three runs of the body, for an
arbitrary computation at the limit, an arbitrary value, and an arbitrary runtime. -/
def limitFree (stop : Free (sig.interface Value) (Exits.At [Out] Value)) (a s : Nat) :
    lengthAt (resultRun stop 2 a s) ≡ 3 := .refl

end Draft.Checks.Specification


namespace Draft.Checks.Specification

open Draft Draft.Checks.Countdown

/-! A loop in a loop: the inner loop has the body with no exit to its own entrance. -/

abbrev mapped : Continuation sig Entry [Entry, Entry, Out] :=
  Continuation.mapExit (Exits.Map.there Entry [Entry, Out]) body

abbrev innerLoop : Continuation sig Entry [Entry, Out] := .loop mapped

def nested : Continuation sig Entry [Out] := .loop innerLoop

def keepsInner : (iterSpec G mapped).Keeps fun _ => PUnit :=
  fun a' _ => ⟨Continuation.witness G (fun _ => PUnit.unit) mapped a', fun _ _ => PUnit.unit⟩

def keepsOuter : (iterSpec G innerLoop).Keeps fun _ => PUnit :=
  fun _ _ => ⟨⟨fun _ => PUnit, PUnit.unit, keepsInner⟩, fun _ _ => PUnit.unit⟩

def witNested (c a s : Nat) : (Continuation.spec G nested).Pre (entry c a, s) :=
  ⟨fun _ => PUnit, PUnit.unit, keepsOuter⟩

abbrev StepInner := (iterSpec G mapped).iterate keepsInner

abbrev StepOuter := (iterSpec G innerLoop).iterate keepsOuter

set_option smartUnfolding false in
/-- A run of the inner loop to the entrance of the outer loop: one run of the body. -/
def innerGoes (c a s : Nat) :
    Loop StepInner ⟨(entry (c + 1) a, s), PUnit.unit⟩
      (.inr (Exits.At.here (entry c (s + a)), s + 1)) :=
  .exit
    ⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s), .refl, .inr (value c, s), .refl,
      .inr (value (s + a), s + 1), .refl, ⟨.refl⟩⟩

set_option smartUnfolding false in
/-- A run of the inner loop to the exit of the outer loop. -/
def innerEnds (a s : Nat) :
    Loop StepInner ⟨(entry 0 a, s), PUnit.unit⟩ (.inr (Exits.At.there Entry (out a), s)) :=
  .exit ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s), .refl, ⟨.refl⟩⟩

set_option smartUnfolding false in
def outerGoes (c a s : Nat) :
    StepOuter ⟨(entry (c + 1) a, s), PUnit.unit⟩ (.inr ⟨(entry c (s + a), s + 1), PUnit.unit⟩) :=
  ⟨innerGoes c a s, .refl⟩

set_option smartUnfolding false in
def outerEnds (a s : Nat) : StepOuter ⟨(entry 0 a, s), PUnit.unit⟩ (.inl (.inr (out a, s))) :=
  innerEnds a s

def runsNested : (c a s : Nat) → (r : Exits.At [Out] Value × Nat) ×
    Loop StepOuter ⟨(entry c a, s), PUnit.unit⟩ (.inr r)
  | 0, a, s => ⟨(out a, s), .exit (outerEnds a s)⟩
  | c + 1, a, s =>
      ⟨(runsNested c (s + a) (s + 1)).1,
        .next (outerGoes c a s) (runsNested c (s + a) (s + 1)).2⟩

/-- Completeness at the run of the loop in a loop from the counter 2. -/
def alongNested (a s : Nat) :=
  Continuation.along G (limitEv nested (entry 2 a, s) (witNested 2 a s)) nested (entry 2 a) s
    (witNested 2 a s) (.inr (runsNested 2 a s).1) (runsNested 2 a s).2

set_option smartUnfolding false in
/-- The threshold is a sum over the runs of the two bodies: it is 6, and three unrollings are
sufficient for the run. -/
def thresholdNested (a s : Nat) : (alongNested a s).1 ≡ 6 := .refl

end Draft.Checks.Specification


namespace Draft.Checks.Specification

open Draft Draft.Checks.Countdown

set_option smartUnfolding false in
/-- The run of the approximant of the loop in a loop with six unrollings, along the evidence. -/
def treeNested (a s : Nat) :=
  (alongNested a s).2 6 (Nat.le_refl 6) (fun q => .pure (some q))
    (returns nested (entry 2 a, s) (witNested 2 a s))
    (.inr (some (runsNested 2 a s).1.1, (runsNested 2 a s).1.2)) ⟨.refl⟩

set_option smartUnfolding false in
/-- The round trip for the loop in a loop. -/
def roundTripNested (a s : Nat) :
    FreeDep.atRun _ _ (treeNested a s) ≡ (runsNested 2 a s).2 := .refl

end Draft.Checks.Specification

/-! The checks on the countdown loop, for an arbitrary value and an arbitrary runtime: the first
exit equation at the run of the whole diagram, and the unrolling law and the fixpoint law of the
loop at the run from the counter 2. -/

namespace Draft.Checks.Specification.ExitEquations

open Draft Draft.Checks.Countdown Draft.Checks.Specification

/-- The witness of the whole diagram from the counter 2, from the witness of the loop. -/
def whole (a s : Nat) : (Diagram.spec G countdown).Pre (inputs 2 a, s) :=
  Diagram.exitSeqPreInv G ⟨Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩ loop
    (inputs 2 a, s) (wit 2 a s)

/-- The run of the whole diagram over that witness: the exit to the entrance, and the run of
the loop. -/
def fromTwo (a s : Nat) : (Diagram.spec G countdown).Post (inputs 2 a, s) (whole a s)
    (.inr (runsS 2 a s).1) :=
  ⟨.inr (Exits.At.here (entry 2 a), s), ⟨.refl⟩, (runsS 2 a s).2⟩

set_option smartUnfolding false in
/-- The first exit equation gives the run of the loop from the run of the whole diagram. -/
def loopOfWhole (a s : Nat) :
    (Diagram.exitSeqSpecRuns G ⟨Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩ loop
      (inputs 2 a, s) (whole a s) _).to (fromTwo a s) ≡ (runsS 2 a s).2 :=
  .refl

set_option smartUnfolding false in
/-- The round trip of the first exit equation at that run is the reflexivity. -/
def loopOfWholeBack (a s : Nat) :
    (Diagram.exitSeqSpecRuns G ⟨Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩ loop
      (inputs 2 a, s) (whole a s) _).invTo (fromTwo a s) ≡ .refl :=
  .refl

set_option smartUnfolding false in
/-- The run from the counter 2 has three runs of the body. -/
def runsLength (a s : Nat) : (runsS 2 a s).2.length ≡ 3 := .refl

set_option smartUnfolding false in
/-- The unrolling law gives two runs of the body run twice. -/
def unrolledLength (a s : Nat) :
    ((Loop.unrolling StepS _ _).to (runsS 2 a s).2).length ≡ 2 := .refl

set_option smartUnfolding false in
/-- The inverse of the unrolling gives the first run. -/
def unrolledBack (a s : Nat) :
    (Loop.unrolling StepS _ _).inv ((Loop.unrolling StepS _ _).to (runsS 2 a s).2) ≡
      (runsS 2 a s).2 :=
  .refl

set_option smartUnfolding false in
/-- The round trip of the fixpoint law at the run is the reflexivity. -/
def fixpointBack (a s : Nat) : (Loop.fixpoint StepS _ _).invTo (runsS 2 a s).2 ≡ .refl := .refl

end Draft.Checks.Specification.ExitEquations

/-! The checks on the countdown loop, for an arbitrary value and an arbitrary runtime. A
derivation with the forms of a loop, of transitivity, and of symmetry gives an equivalence of
the runs over the moved witness and the runs over the first witness: the checks have its two
maps at a run, and the round trip at the run over the first witness. A derivation with one
loop form has the round trip at the run over the moved witness. A derivation with the form of
a composite has the map back and the two round trips. -/

namespace Draft.Checks.Specification

open Draft Draft.Checks.Countdown Draft.Checks.Specification

/-- The rule set with no rule. -/
def noRule : Rules sig := ⟨fun _ _ => Empty, fun _ _ => Empty⟩

/-- The rule set with no rule holds for each specification of the calls. -/
def noRuleSound : noRule.SpecSound G := ⟨(fun x => nomatch x), (fun x => nomatch x)⟩

/-- A derivation from the loop to the loop, with the forms of a loop, of transitivity, and of
symmetry. -/
def again : Continuation.Derivation noRule loop loop :=
  .trans (.loop (.agree (Continuation.Agreement.refl body)))
    (.symm (.loop (.agree (Continuation.Agreement.refl body))))

/-- The witness of the loop along the derivation, with the equivalence of its runs. -/
def moved (c a s : Nat) := (again.spec noRuleSound).1 (entry c a, s) (wit c a s)

/-- One iteration over the moved witness. -/
abbrev StepM := (iterSpec G body).iterate (moved 0 0 0).1.2.2

set_option smartUnfolding false in
/-- One iteration over the moved witness that goes to the next entrance. -/
def goesM (c a s : Nat) :
    StepM ⟨(entry (c + 1) a, s), PUnit.unit⟩ (.inr ⟨(entry c (s + a), s + 1), PUnit.unit⟩) :=
  ⟨⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s), .refl, .inr (value c, s), .refl,
      .inr (value (s + a), s + 1), .refl, ⟨.refl⟩⟩,
    .refl⟩

set_option smartUnfolding false in
/-- One iteration over the moved witness that exits. -/
def endsM (a s : Nat) : StepM ⟨(entry 0 a, s), PUnit.unit⟩ (.inl (.inr (out a, s))) :=
  ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s), .refl, ⟨.refl⟩⟩

/-- The run over the moved witness from each counter. -/
def runsM : (c a s : Nat) → (r : Exits.At [Out] Value × Nat) ×
    Loop StepM ⟨(entry c a, s), PUnit.unit⟩ (.inr r)
  | 0, a, s => ⟨(out a, s), .exit (endsM a s)⟩
  | c + 1, a, s => ⟨(runsM c (s + a) (s + 1)).1, .next (goesM c a s) (runsM c (s + a) (s + 1)).2⟩

set_option smartUnfolding false in
/-- The run over the moved witness maps to the run over the first witness. -/
def movedRun (a s : Nat) :
    ((moved 2 a s).2 (.inr (runsM 2 a s).1)).to (runsM 2 a s).2 ≡ (runsS 2 a s).2 := .refl

set_option smartUnfolding false in
/-- The run over the first witness maps back to the run over the moved witness. -/
def movedBack (a s : Nat) :
    ((moved 2 a s).2 (.inr (runsS 2 a s).1)).inv (runsS 2 a s).2 ≡ (runsM 2 a s).2 := .refl

set_option smartUnfolding false in
/-- The round trip at the run over the first witness is the reflexivity. -/
def movedRound (a s : Nat) :
    ((moved 2 a s).2 (.inr (runsS 2 a s).1)).toInv (runsS 2 a s).2 ≡ .refl := .refl

/-- A derivation from the loop to the loop with one loop form. -/
def single : Continuation.Derivation noRule loop loop :=
  .loop (.agree (Continuation.Agreement.refl body))

/-- The witness of the loop along that derivation, with the equivalence of its runs. -/
def movedOne (c a s : Nat) := (single.spec noRuleSound).1 (entry c a, s) (wit c a s)

/-- One iteration over that witness. -/
abbrev StepOne := (iterSpec G body).iterate (movedOne 0 0 0).1.2.2

set_option smartUnfolding false in
/-- One iteration over that witness that goes to the next entrance. -/
def goesOne (c a s : Nat) :
    StepOne ⟨(entry (c + 1) a, s), PUnit.unit⟩ (.inr ⟨(entry c (s + a), s + 1), PUnit.unit⟩) :=
  ⟨⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s), .refl, .inr (value c, s), .refl,
      .inr (value (s + a), s + 1), .refl, ⟨.refl⟩⟩,
    .refl⟩

set_option smartUnfolding false in
/-- One iteration over that witness that exits. -/
def endsOne (a s : Nat) : StepOne ⟨(entry 0 a, s), PUnit.unit⟩ (.inl (.inr (out a, s))) :=
  ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s), .refl, ⟨.refl⟩⟩

/-- The run over that witness from each counter. -/
def runsOne : (c a s : Nat) → (r : Exits.At [Out] Value × Nat) ×
    Loop StepOne ⟨(entry c a, s), PUnit.unit⟩ (.inr r)
  | 0, a, s => ⟨(out a, s), .exit (endsOne a s)⟩
  | c + 1, a, s =>
      ⟨(runsOne c (s + a) (s + 1)).1, .next (goesOne c a s) (runsOne c (s + a) (s + 1)).2⟩

set_option smartUnfolding false in
/-- The round trip at the run over the moved witness is the reflexivity, for the derivation
with one loop form. -/
def roundOne (a s : Nat) :
    ((movedOne 2 a s).2 (.inr (runsOne 2 a s).1)).invTo (runsOne 2 a s).2 ≡ .refl := .refl

/-- A derivation from the whole diagram to the whole diagram, with the form of a composite. -/
def wholeOne : Diagram.Derivation noRule countdown countdown :=
  .seq (.agree (Diagram.Agreement.refl _)) single

/-- The witness of the whole diagram along the derivation, with the equivalence of its runs. -/
def movedWhole (a s : Nat) :=
  (wholeOne.spec noRuleSound).1 (inputs 2 a, s) (ExitEquations.whole a s)

/-- The run of the whole diagram over the moved witness. -/
def wholeRun (a s : Nat) : (Diagram.spec G countdown).Post (inputs 2 a, s) (movedWhole a s).1
    (.inr (runsOne 2 a s).1) :=
  ⟨.inr (Exits.At.here (entry 2 a), s), ⟨.refl⟩, (runsOne 2 a s).2⟩

set_option smartUnfolding false in
/-- The run of the whole diagram over the first witness maps back to the run over the moved
witness. -/
def wholeBack (a s : Nat) :
    ((movedWhole a s).2 (.inr (runsS 2 a s).1)).inv (ExitEquations.fromTwo a s) ≡ wholeRun a s :=
  .refl

set_option smartUnfolding false in
/-- The round trip of the whole diagram at the run over the first witness is the
reflexivity. -/
def wholeRound (a s : Nat) :
    ((movedWhole a s).2 (.inr (runsS 2 a s).1)).toInv (ExitEquations.fromTwo a s) ≡ .refl := .refl

set_option smartUnfolding false in
/-- The round trip of the whole diagram at the run over the moved witness is the
reflexivity. -/
def wholeRoundBack (a s : Nat) :
    ((movedWhole a s).2 (.inr (runsOne 2 a s).1)).invTo (wholeRun a s) ≡ .refl := .refl

end Draft.Checks.Specification

/-! The check of a rule on two different loops, for an arbitrary value and an arbitrary runtime.
The first loop has the exit from the loop as an exit past a continuation, and then that
continuation. The second loop is the countdown loop. The derivation has the second exit
equation under a step, a copairing, and a loop. The checks have the two maps of the
equivalence of the runs, and its two round trips. -/

namespace Draft.Checks.Specification

open Draft Draft.Checks.Countdown

/-- A continuation that the exit from the loop goes past. -/
def skipped : Continuation sig Out [Entry, Out] :=
  .one (.exit ⟨_, .there .here, Boundary.only _, .cons .here .nil⟩)

/-- The rest after the test, with the exit from the loop as an exit past the continuation, and
then the continuation. -/
def afterTestPast : (c : (sig.output .isZero).Case) → Diagram sig (c.1 ++ [(), ()]) [Entry, Out]
  | ⟨_, .here⟩ =>
      .seq (.exit (Exits.At.there Out ⟨_, .there .here, Boundary.only _, .cons (.there .here) .nil⟩))
        skipped
  | ⟨_, .there .here⟩ => .step ⟨.pred, .cons .here .nil⟩ afterPred

def bodyPast : Continuation sig Entry [Entry, Out] :=
  .one (.step ⟨.isZero, .cons .here .nil⟩ afterTestPast)

def loopPast : Continuation sig Entry [Out] := .loop bodyPast

/-- The derivation of the rests after the test: the second exit equation at the exit from the
loop, and the agreement of the other rest with itself. -/
def afterTestToExit : (c : (sig.output .isZero).Case) →
    Diagram.Derivation (Rules.exitPast sig) (afterTestPast c) (afterTest c)
  | ⟨_, .here⟩ => .rule (.exit _ _)
  | ⟨_, .there .here⟩ => .agree (Diagram.Agreement.refl _)

/-- The derivation of the diagram of the one case of the entrance. -/
def bodyToExit : (c : Entry.Case) →
    Diagram.Derivation (Rules.exitPast sig)
      (Boundary.family (F := fun Δ => Diagram sig Δ [Entry, Out])
        (.cons (.step ⟨.isZero, .cons .here .nil⟩ afterTestPast) .nil) c)
      (Boundary.family (F := fun Δ => Diagram sig Δ [Entry, Out])
        (.cons (.step ⟨.isZero, .cons .here .nil⟩ afterTest) .nil) c)
  | ⟨_, .here⟩ => .step _ afterTestToExit

/-- The derivation from that loop to the countdown loop. -/
def pastToExit : Continuation.Derivation (Rules.exitPast sig) loopPast loopN :=
  .loop (.copair bodyToExit)

/-- One iteration of the countdown loop over its witness. -/
abbrev StepN := (iterSpec G bodyN).iterate keepsN

set_option smartUnfolding false in
def goesN (c a s : Nat) :
    StepN ⟨(entry (c + 1) a, s), PUnit.unit⟩ (.inr ⟨(entry c (s + a), s + 1), PUnit.unit⟩) :=
  ⟨⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s), .refl, .inr (value c, s), .refl,
      .inr (value (s + a), s + 1), .refl, ⟨.refl⟩⟩,
    .refl⟩

set_option smartUnfolding false in
def endsN (a s : Nat) : StepN ⟨(entry 0 a, s), PUnit.unit⟩ (.inl (.inr (out a, s))) :=
  ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s), .refl, ⟨.refl⟩⟩

/-- The run of the countdown loop from each counter. -/
def runsN : (c a s : Nat) → (r : Exits.At [Out] Value × Nat) ×
    Loop StepN ⟨(entry c a, s), PUnit.unit⟩ (.inr r)
  | 0, a, s => ⟨(out a, s), .exit (endsN a s)⟩
  | c + 1, a, s => ⟨(runsN c (s + a) (s + 1)).1, .next (goesN c a s) (runsN c (s + a) (s + 1)).2⟩

/-- The witness of the first loop from the witness of the countdown loop, with the equivalence
of the runs. -/
def movedPast (c a s : Nat) :=
  (pastToExit.spec (Rules.exitPastSound G)).2 (entry c a, s) (witN c a s)

/-- One iteration of the first loop over the moved witness. -/
abbrev StepP := (iterSpec G bodyPast).iterate (movedPast 0 0 0).1.2.2

set_option smartUnfolding false in
def goesP (c a s : Nat) :
    StepP ⟨(entry (c + 1) a, s), PUnit.unit⟩ (.inr ⟨(entry c (s + a), s + 1), PUnit.unit⟩) :=
  ⟨⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s), .refl, .inr (value c, s), .refl,
      .inr (value (s + a), s + 1), .refl, ⟨.refl⟩⟩,
    .refl⟩

set_option smartUnfolding false in
/-- The iteration that exits has the run of the exit past the continuation. -/
def endsP (a s : Nat) : StepP ⟨(entry 0 a, s), PUnit.unit⟩ (.inl (.inr (out a, s))) :=
  ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s), .refl, _, ⟨.refl⟩, ⟨.refl⟩⟩

/-- The run of the first loop from each counter. -/
def runsP : (c a s : Nat) → (r : Exits.At [Out] Value × Nat) ×
    Loop StepP ⟨(entry c a, s), PUnit.unit⟩ (.inr r)
  | 0, a, s => ⟨(out a, s), .exit (endsP a s)⟩
  | c + 1, a, s => ⟨(runsP c (s + a) (s + 1)).1, .next (goesP c a s) (runsP c (s + a) (s + 1)).2⟩

set_option smartUnfolding false in
/-- The run of the first loop maps to the run of the countdown loop. -/
def pastRun (a s : Nat) :
    ((movedPast 2 a s).2 (.inr (runsP 2 a s).1)).to (runsP 2 a s).2 ≡ (runsN 2 a s).2 := .refl

set_option smartUnfolding false in
/-- The run of the countdown loop maps back to the run of the first loop. -/
def pastBack (a s : Nat) :
    ((movedPast 2 a s).2 (.inr (runsN 2 a s).1)).inv (runsN 2 a s).2 ≡ (runsP 2 a s).2 := .refl

set_option smartUnfolding false in
/-- The round trip at the run of the countdown loop is the reflexivity. -/
def pastRound (a s : Nat) :
    ((movedPast 2 a s).2 (.inr (runsN 2 a s).1)).toInv (runsN 2 a s).2 ≡ .refl := .refl

set_option smartUnfolding false in
/-- The round trip at the run of the first loop is the reflexivity. -/
def pastRoundBack (a s : Nat) :
    ((movedPast 2 a s).2 (.inr (runsP 2 a s).1)).invTo (runsP 2 a s).2 ≡ .refl := .refl

end Draft.Checks.Specification

namespace Draft.Checks.Specification.Invariant

open Draft Draft.Checks.Countdown Draft.Checks.Specification

/-- The counter of an entrance. -/
def counter (k : Entry.At Value) : Nat := (Boundary.onlyValues k).lookup .here

/-- The sum with a successor on the left. -/
def succAdd (m : Nat) : (n : Nat) → (m + 1) + n ≡ (m + n) + 1
  | 0 => .refl
  | n + 1 => Identity.cong (· + 1) (succAdd m n)

variable (s₀ c₀ : Nat)

/-- The invariant: the sum of the runtime and the counter is the sum at the first entrance. -/
abbrev Inv (x : Entry.At Value × Nat) : Type := x.2 + counter x.1 ≡ s₀ + c₀

/-- The condition at a result: no stop, and the runtime at the exit. -/
def Final : Unit ⊕ (Exits.At [Out] Value × Nat) → Type
  | .inl _ => Empty
  | .inr y => y.2 ≡ s₀ + c₀

/-- The condition at the limit that each runtime has. -/
abbrev Always : Nat → Type := fun _ => Unit

/-- The evidence of the body at each entrance with the invariant, by the constructors. -/
def bodyHolds (n : Nat) : (x : Entry.At Value × Nat) → Inv s₀ c₀ x →
    body.Holds G Always n
      (Spec.Later (fun e => Final s₀ c₀ (.inl e)) (Inv s₀ c₀) (fun y => Final s₀ c₀ (.inr y))) x
  | (⟨⟨_, .here⟩, .cons 0 (.cons _ .nil)⟩, s), inv =>
      Continuation.Holds.copair _
        (Diagram.Holds.stepResponse machine ⟨.isZero, .cons .here .nil⟩ _
          (b := (⟨⟨_, .here⟩, .nil⟩, s)) .refl (Diagram.Holds.exit _ inv))
  | (⟨⟨_, .here⟩, .cons (c + 1) (.cons a .nil)⟩, s), inv =>
      Continuation.Holds.copair _
        (Diagram.Holds.stepResponse machine ⟨.isZero, .cons .here .nil⟩ _
          (b := (⟨⟨_, .there .here⟩, .nil⟩, s)) .refl
          (Diagram.Holds.stepResponse machine ⟨.pred, .cons .here .nil⟩ _
            (b := (value c, s)) .refl
            (Diagram.Holds.stepResponse machine ⟨.emit, .cons (.there (.there .here)) .nil⟩ _
              (b := (value (s + a), s + 1)) .refl
              (Diagram.Holds.exit _ ((succAdd s c).trans inv)))))

/-- The evidence of the loop at each entrance with the invariant. The loop has no count, and
the invariant gives the condition at the limit. -/
def loopHolds (n : Nat) (x : Entry.At Value × Nat) (start : Inv s₀ c₀ x) :
    loop.Holds G Always n (Final s₀ c₀) x :=
  Continuation.Holds.loop (Inv s₀ c₀) body (bodyHolds s₀ c₀ n) (fun _ _ => ()) start

/-- The evidence of the loop from the counter 2: the runtime at the exit is the runtime at the
entrance plus 2. -/
def holds (a s : Nat) : loop.Holds G Always 0 (Final s 2) (entry 2 a, s) :=
  loopHolds s 2 0 (entry 2 a, s) .refl

/-- The witness of the precondition of the loop that the evidence has. -/
def witness (a s : Nat) : (Continuation.spec G loop).Pre (entry 2 a, s) :=
  (holds a s).parts.1.1

/-- One iteration over that witness. -/
abbrev Step (a s : Nat) := (iterSpec G body).iterate (witness a s).2.2

set_option smartUnfolding false in
/-- The first iteration, with the invariant witness at the next entrance. -/
def first (a s : Nat) : (i : (witness a s).1 (entry 1 (s + a), s + 1)) ×
    Step a s ⟨(entry 2 a, s), (witness a s).2.1⟩ (.inr ⟨(entry 1 (s + a), s + 1), i⟩) :=
  ⟨_, ⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s), .refl, .inr (value 1, s), .refl,
      .inr (value (s + a), s + 1), .refl, ⟨.refl⟩⟩, .refl⟩

set_option smartUnfolding false in
/-- The second iteration. -/
def second (a s : Nat) : (i : (witness a s).1 (entry 0 ((s + 1) + (s + a)), s + 2)) ×
    Step a s ⟨(entry 1 (s + a), s + 1), (first a s).1⟩
      (.inr ⟨(entry 0 ((s + 1) + (s + a)), s + 2), i⟩) :=
  ⟨_, ⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s + 1), .refl, .inr (value 0, s + 1), .refl,
      .inr (value ((s + 1) + (s + a)), s + 2), .refl, ⟨.refl⟩⟩, .refl⟩

set_option smartUnfolding false in
/-- The last iteration: the exit. -/
def last (a s : Nat) :
    Step a s ⟨(entry 0 ((s + 1) + (s + a)), s + 2), (second a s).1⟩
      (.inl (.inr (out ((s + 1) + (s + a)), s + 2))) :=
  ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s + 2), .refl, ⟨.refl⟩⟩

/-- The run of the loop over that witness, from the counter 2. -/
def loopRun (a s : Nat) :
    (Continuation.spec G loop).Post (entry 2 a, s) (witness a s)
      (.inr (out ((s + 1) + (s + a)), s + 2)) :=
  .next (first a s).2 (.next (second a s).2 (.exit (last a s)))

set_option smartUnfolding false in
/-- The condition at the result of the run: the identity of the runtime at the exit with the
runtime at the entrance plus 2, for an arbitrary value and an arbitrary runtime. The evidence
goes through the invariant of each of the two iterations. -/
def runtimeAtExit (a s : Nat) :
    ((holds a s).parts.2 (.inr (out ((s + 1) + (s + a)), s + 2)) (loopRun a s)).result ≡
      (Identity.refl : s + 2 ≡ s + 2) := .refl

end Draft.Checks.Specification.Invariant

namespace Draft.Checks.Specification.Bound

open Draft Draft.Checks.Countdown Draft.Checks.Specification
open Draft.Checks.Specification.Invariant (counter succAdd Final)

/-! A real bound: the empty condition at the limit. A family with a count shows that the
number of unrollings is sufficient, and the verified implementation of the approximant needs no
evidence for the computation at the limit. -/

/-- A number that is not zero. -/
def Positive : Nat → Type
  | 0 => Empty
  | _ + 1 => Unit

/-- A number is less than a second number: the second number is the first plus one, plus a
difference. -/
abbrev Below (c m : Nat) : Type := (k : Nat) × (k + (c + 1) ≡ m)

/-- No number is less than zero. -/
def Below.zero {c : Nat} (h : Below c 0) : Empty := Identity.transport Positive h.2 ()

/-- The predecessors of two numbers keep the order. -/
def Below.pred {c m : Nat} (h : Below (c + 1) (m + 1)) : Below c m :=
  ⟨h.1, Identity.cong Nat.pred h.2⟩

variable (s₀ c₀ : Nat)

/-- The family with a count: the sum of the runtime and the counter is the sum at the first
entrance, and the counter is less than the count. -/
abbrev Count (m : Nat) (x : Entry.At Value × Nat) : Type :=
  (x.2 + counter x.1 ≡ s₀ + c₀) × Below (counter x.1) m

def never (x : Entry.At Value × Nat) (v : Count s₀ c₀ 0 x) : Empty := v.2.zero

def bodyHolds (n : Nat) : (m : Nat) → (x : Entry.At Value × Nat) → Count s₀ c₀ (m + 1) x →
    body.Holds G Never n
      (Spec.Later (fun e => Final s₀ c₀ (.inl e)) (Count s₀ c₀ m)
        (fun y => Final s₀ c₀ (.inr y))) x
  | _, (⟨⟨_, .here⟩, .cons 0 (.cons _ .nil)⟩, s), v =>
      Continuation.Holds.copair _
        (Diagram.Holds.stepResponse machine ⟨.isZero, .cons .here .nil⟩ _
          (b := (⟨⟨_, .here⟩, .nil⟩, s)) .refl (Diagram.Holds.exit _ v.1))
  | _, (⟨⟨_, .here⟩, .cons (c + 1) (.cons a .nil)⟩, s), v =>
      Continuation.Holds.copair _
        (Diagram.Holds.stepResponse machine ⟨.isZero, .cons .here .nil⟩ _
          (b := (⟨⟨_, .there .here⟩, .nil⟩, s)) .refl
          (Diagram.Holds.stepResponse machine ⟨.pred, .cons .here .nil⟩ _
            (b := (value c, s)) .refl
            (Diagram.Holds.stepResponse machine ⟨.emit, .cons (.there (.there .here)) .nil⟩ _
              (b := (value (s + a), s + 1)) .refl
              (Diagram.Holds.exit _ ((succAdd s c).trans v.1, v.2.pred)))))

/-- The specification of the countdown with a number of unrollings. A witness of the
precondition shows that the counter is less than that number. -/
def bounded (n : Nat) :
    DepPoly.{0, 0, 0, 0} ((Diagram.interface Value [(), ()] [Out]).runtime Nat Unit) where
  Pre x := Below (x.1.lookup .here) n
  Post x _ := Final x.2 (x.1.lookup .here)

def countdownHolds (n : Nat) (env : All Value [(), ()]) (s : Nat)
    (pre : (bounded n).Pre (env, s)) :
    countdown.Holds G Never n ((bounded n).Post (env, s) pre) (env, s) :=
  Diagram.Holds.seq (S := sig) (Count s (env.lookup .here) n) enter loop
    (Diagram.Holds.exit _ (.refl, pre))
    fun _ start =>
      Continuation.Holds.loopCounted (Count s (env.lookup .here)) body
        (bodyHolds s (env.lookup .here) n) (never s (env.lookup .here)) start

variable (stop : Free (sig.interface Value) (Exits.At [Out] Value))

def countdownImpl (n : Nat) : ImplDep (bounded n) G (countdown.impl stop n).thread :=
  Diagram.Holds.impl (fun x pre => countdownHolds n x.1 x.2 pre) fun _ _ _ e => e.elim

set_option smartUnfolding false in
/-- From the counter 2, with each number of unrollings that is three or more. -/
def atExit (k a s : Nat) :
    Final s 2 (machine.run (countdown.run stop (k + 3) (inputs 2 a) .pure) s) :=
  ((countdownImpl stop (k + 3)).run machine.graphEvidence) (inputs 2 a, s) ⟨k, .refl⟩

set_option smartUnfolding false in
def runtimeAtExit (k a s : Nat) :
    (Identity.transport (fun j => Fin (j + 1)) (atExit stop k a s)
      ⟨s + 2, Nat.lt_succ_self _⟩).val ≡ s + 2 := .refl

set_option smartUnfolding false in
/-- From a smaller counter with the same specification: the counter 1 with three or more
unrollings. -/
def atExitOne (k a s : Nat) :
    Final s 1 (machine.run (countdown.run stop (k + 3) (inputs 1 a) .pure) s) :=
  ((countdownImpl stop (k + 3)).run machine.graphEvidence) (inputs 1 a, s) ⟨k + 1, .refl⟩

set_option smartUnfolding false in
def runtimeAtExitOne (k a s : Nat) :
    (Identity.transport (fun j => Fin (j + 1)) (atExitOne stop k a s)
      ⟨s + 1, Nat.lt_succ_self _⟩).val ≡ s + 1 := .refl

/-! A loop in a loop, with a real bound. The inner loop counts the value down. At the value
zero, the outer step tests the counter: at zero it exits, and at a successor it exits to the
outer entrance with the predecessor. One number of unrollings is for the two loops, so each
family has a count with slack. -/

/-- The body of the inner loop. Its exits are the inner entrance, the outer entrance, and the
exit of the two loops. -/
def innerBody : Continuation sig Entry [Entry, Entry, Out] :=
  .one (.step ⟨.isZero, .cons (.there .here) .nil⟩ fun
    | ⟨_, .here⟩ =>
        .step ⟨.isZero, .cons .here .nil⟩ fun
          | ⟨_, .here⟩ =>
              .exit ⟨_, .there (.there .here), Boundary.only _, .cons (.there .here) .nil⟩
          | ⟨_, .there .here⟩ =>
              .step ⟨.pred, .cons .here .nil⟩ (.one
                (.exit ⟨_, .there .here, Boundary.only _,
                  .cons .here (.cons (.there (.there .here)) .nil)⟩))
    | ⟨_, .there .here⟩ =>
        .step ⟨.pred, .cons (.there .here) .nil⟩ (.one
          (.exit (Exits.At.here ⟨Boundary.only _, .cons (.there .here) (.cons .here .nil)⟩))))

def inner : Continuation sig Entry [Entry, Out] := .loop innerBody

def outer : Continuation sig Entry [Out] := .loop inner

/-- The two loops from the two inputs. -/
def twoLoops : Diagram sig [(), ()] [Out] := .seq enter outer

/-- The value of an entrance. -/
def amount (k : Entry.At Value) : Nat := (Boundary.onlyValues k).lookup (.there .here)

/-- A number that has a smaller number is not zero. -/
def Below.positive {c n : Nat} (h : Below c n) : Below 0 n := ⟨h.1 + c, h.2⟩

/-- The condition at a result of the two loops: no stop, and the first runtime at the exit. -/
def Same (s₁ : Nat) : Unit ⊕ (Exits.At [Out] Value × Nat) → Type
  | .inl _ => Empty
  | .inr y => y.2 ≡ s₁

variable (n s₁ : Nat)

/-- The family of the outer loop: the counter is less than the count, and the value is less
than the number of unrollings. -/
abbrev Outer (m : Nat) (x : Entry.At Value × Nat) : Type :=
  (x.2 ≡ s₁) × Below (counter x.1) m × Below (amount x.1) n

/-- The condition at a result of the inner loop, for a count of the outer loop. -/
abbrev AfterInner (mo : Nat) : Unit ⊕ (Exits.At [Entry, Out] Value × Nat) → Type :=
  Spec.Later (fun e => Same s₁ (.inl e)) (Outer n s₁ mo) (fun y => Same s₁ (.inr y))

/-- The family of the inner loop, for a count of the outer loop: the value is less than the
count, and the counter is less than the count of the outer loop plus one. -/
abbrev Inner (mo m : Nat) (x : Entry.At Value × Nat) : Type :=
  (x.2 ≡ s₁) × Below (amount x.1) m × Below (counter x.1) (mo + 1) × Below 0 n

/-- The evidence of the body of the inner loop, by the constructors. -/
def innerBodyHolds (mo : Nat) : (m : Nat) → (x : Entry.At Value × Nat) →
    Inner n s₁ mo (m + 1) x →
    innerBody.Holds G Never n
      (Spec.Later (fun e => AfterInner n s₁ mo (.inl e)) (Inner n s₁ mo m)
        (fun y => AfterInner n s₁ mo (.inr y))) x
  | _, (⟨⟨_, .here⟩, .cons 0 (.cons 0 .nil)⟩, s), v =>
      Continuation.Holds.copair _
        (Diagram.Holds.stepResponse machine ⟨.isZero, .cons (.there .here) .nil⟩ _
          (b := (⟨⟨_, .here⟩, .nil⟩, s)) .refl
          (Diagram.Holds.stepResponse machine ⟨.isZero, .cons .here .nil⟩ _
            (b := (⟨⟨_, .here⟩, .nil⟩, s)) .refl (Diagram.Holds.exit _ v.1)))
  | _, (⟨⟨_, .here⟩, .cons (c + 1) (.cons 0 .nil)⟩, s), v =>
      Continuation.Holds.copair _
        (Diagram.Holds.stepResponse machine ⟨.isZero, .cons (.there .here) .nil⟩ _
          (b := (⟨⟨_, .here⟩, .nil⟩, s)) .refl
          (Diagram.Holds.stepResponse machine ⟨.isZero, .cons .here .nil⟩ _
            (b := (⟨⟨_, .there .here⟩, .nil⟩, s)) .refl
            (Diagram.Holds.stepResponse machine ⟨.pred, .cons .here .nil⟩ _
              (b := (value c, s)) .refl
              (Diagram.Holds.exit _ (v.1, v.2.2.1.pred, v.2.2.2)))))
  | _, (⟨⟨_, .here⟩, .cons _ (.cons (a + 1) .nil)⟩, s), v =>
      Continuation.Holds.copair _
        (Diagram.Holds.stepResponse machine ⟨.isZero, .cons (.there .here) .nil⟩ _
          (b := (⟨⟨_, .there .here⟩, .nil⟩, s)) .refl
          (Diagram.Holds.stepResponse machine ⟨.pred, .cons (.there .here) .nil⟩ _
            (b := (value a, s)) .refl
            (Diagram.Holds.exit _ (v.1, v.2.1.pred, v.2.2.1, v.2.2.2))))

/-- The evidence of the inner loop at each entrance of the outer loop: the body of the outer
loop. The inner loop takes its family at the number of unrollings. -/
def innerHolds (mo : Nat) (y : Entry.At Value × Nat) (v : Outer n s₁ (mo + 1) y) :
    inner.Holds G Never n (AfterInner n s₁ mo) y :=
  Continuation.Holds.loopCounted (Inner n s₁ mo) innerBody (innerBodyHolds n s₁ mo)
    (fun _ w => w.2.1.zero) (x := y) (v.1, v.2.2, v.2.1, v.2.2.positive)

/-- The specification of the two loops with a number of unrollings: the counter and the value
are less than that number. -/
def twoLoopsBounded (n : Nat) :
    DepPoly.{0, 0, 0, 0} ((Diagram.interface Value [(), ()] [Out]).runtime Nat Unit) where
  Pre x := Below (x.1.lookup .here) n × Below (x.1.lookup (.there .here)) n
  Post x _ := Same x.2

/-- The evidence of the two loops with the bound, by the constructors. -/
def twoLoopsHolds (env : All Value [(), ()]) (s : Nat) (pre : (twoLoopsBounded n).Pre (env, s)) :
    twoLoops.Holds G Never n ((twoLoopsBounded n).Post (env, s) pre) (env, s) :=
  Diagram.Holds.seq (S := sig) (Outer n s n) enter outer
    (Diagram.Holds.exit _ (.refl, pre.1, pre.2))
    fun _ start =>
      Continuation.Holds.loopCounted (Outer n s) inner (innerHolds n s)
        (fun _ w => w.2.1.zero) start

/-- The verified implementation of the approximant of the two loops, with no evidence for the
computation at the limit. -/
def twoLoopsImpl : ImplDep (twoLoopsBounded n) G (twoLoops.impl stop n).thread :=
  Diagram.Holds.impl (fun x pre => twoLoopsHolds n x.1 x.2 pre) fun _ _ _ e => e.elim

set_option smartUnfolding false in
/-- From the counter 1 and the value 2, with each number of unrollings that is three or more.
The inner loop has three iterations and then one, and the outer loop has two. -/
def twoLoopsAtExit (k s : Nat) :
    Same s (machine.run (twoLoops.run stop (k + 3) (inputs 1 2) .pure) s) :=
  ((twoLoopsImpl stop (k + 3)).run machine.graphEvidence) (inputs 1 2, s) (⟨k + 1, .refl⟩, ⟨k, .refl⟩)

set_option smartUnfolding false in
/-- The evidence of the two loops is consumed through a dependent payload, for an arbitrary
runtime and an arbitrary computation at the limit. -/
def twoLoopsRuntime (k s : Nat) :
    (Identity.transport (fun j => Fin (j + 1)) (twoLoopsAtExit stop k s)
      ⟨s, Nat.lt_succ_self _⟩).val ≡ s := .refl

end Draft.Checks.Specification.Bound

namespace Draft.Checks.Specification.Optimize

open Draft Draft.Checks.Countdown Draft.Checks.Specification
open Draft.Checks.Specification.Invariant (counter succAdd Inv Final Always)

/-! A loop with no limit along a derivation. The evidence of the first diagram is by the
constructors. The map that forgets the bound gives its verified diagram, the derivation with a
rule under the loop moves it to the second diagram, and the verified diagram of the second
diagram gives the condition at the result of a run of the second diagram over the moved
witness. The checks have no evidence for a computation at the limit: for this postcondition no
computation has it, because the runtime of the machine only grows. -/

/-- The first diagram: the loop whose exit is an exit past a continuation. -/
def countdownPast : Diagram sig [(), ()] [Out] := .seq enter loopPast

/-- The second diagram: the countdown loop. -/
def countdownN : Diagram sig [(), ()] [Out] := .seq enter loopN

/-- The specification of the two diagrams, for each counter. The exit has the first runtime
plus the counter, and a stop has no evidence. -/
def unlimited :
    DepPoly.{0, 0, 0, 0} ((Diagram.interface Value [(), ()] [Out]).runtime Nat Unit) where
  Pre _ := Unit
  Post x _ := Final x.2 (x.1.lookup .here)

variable (s₀ c₀ : Nat)

/-- The evidence of the body of the first loop at each entrance with the invariant, by the
constructors of the family. The exit from the loop is a composite of an exit past a
continuation and that continuation. -/
def bodyPastHolds (n : Nat) : (x : Entry.At Value × Nat) → Inv s₀ c₀ x →
    bodyPast.Holds G Always n
      (Spec.Later (fun e => Final s₀ c₀ (.inl e)) (Inv s₀ c₀) (fun y => Final s₀ c₀ (.inr y))) x
  | (⟨⟨_, .here⟩, .cons 0 (.cons _ .nil)⟩, s), inv =>
      Continuation.Holds.copair _
        (Diagram.Holds.stepResponse machine ⟨.isZero, .cons .here .nil⟩ _
          (b := (⟨⟨_, .here⟩, .nil⟩, s)) .refl
          (Diagram.Holds.seq (S := sig) (fun _ => Empty) _ skipped
            (Diagram.Holds.exit _ inv) fun _ e => e.elim))
  | (⟨⟨_, .here⟩, .cons (c + 1) (.cons a .nil)⟩, s), inv =>
      Continuation.Holds.copair _
        (Diagram.Holds.stepResponse machine ⟨.isZero, .cons .here .nil⟩ _
          (b := (⟨⟨_, .there .here⟩, .nil⟩, s)) .refl
          (Diagram.Holds.stepResponse machine ⟨.pred, .cons .here .nil⟩ _
            (b := (value c, s)) .refl
            (Diagram.Holds.stepResponse machine ⟨.emit, .cons (.there (.there .here)) .nil⟩ _
              (b := (value (s + a), s + 1)) .refl
              (Diagram.Holds.exit _ ((succAdd s c).trans inv)))))

/-- The evidence of the first loop at each entrance with the invariant. The loop has no
count. -/
def loopPastHolds (n : Nat) (x : Entry.At Value × Nat) (start : Inv s₀ c₀ x) :
    loopPast.Holds G Always n (Final s₀ c₀) x :=
  Continuation.Holds.loop (Inv s₀ c₀) bodyPast (bodyPastHolds s₀ c₀ n) (fun _ _ => ()) start

/-- The evidence of the first diagram, by the constructors of the family. -/
def pastHolds (n : Nat) (env : All Value [(), ()]) (s : Nat) (pre : unlimited.Pre (env, s)) :
    countdownPast.Holds G Always n (unlimited.Post (env, s) pre) (env, s) :=
  Diagram.Holds.seq (S := sig) (Inv s (env.lookup .here)) enter loopPast
    (Diagram.Holds.exit _ .refl)
    fun y start => loopPastHolds s (env.lookup .here) n y start

/-- The verified diagram of the first diagram: the evidence with no bound. -/
def pastVerified : countdownPast.Verified G unlimited :=
  Diagram.Holds.verified fun x pre => pastHolds 0 x.1 x.2 pre

/-- The derivation from the first diagram to the second: the rule under the loop, under the
composite. -/
def optimize : Diagram.Derivation (Rules.exitPast sig) countdownPast countdownN :=
  .seq (.agree (Diagram.Agreement.refl _)) pastToExit

/-- The verified diagram of the second diagram, along the derivation. -/
def movedVerified : countdownN.Verified G unlimited :=
  Diagram.Derivation.verified (Rules.exitPastSound G) optimize pastVerified

/-- The moved witness of the second diagram, from the counter 2. -/
def movedWitness (a s : Nat) : (Diagram.spec G countdownN).Pre (inputs 2 a, s) :=
  (movedVerified (inputs 2 a, s) ()).1

/-- The witness of the loop of the second diagram, after the exit to the entrance. -/
def movedLoopWitness (a s : Nat) : (Continuation.spec G loopN).Pre (entry 2 a, s) :=
  (movedWitness a s).2 (.inr (Exits.At.here (entry 2 a), s)) ⟨.refl⟩

/-- One iteration over the moved witness. -/
abbrev StepMoved (a s : Nat) := (iterSpec G bodyN).iterate (movedLoopWitness a s).2.2

set_option smartUnfolding false in
/-- The first iteration, with the invariant witness at the next entrance. -/
def firstMoved (a s : Nat) : (i : (movedLoopWitness a s).1 (entry 1 (s + a), s + 1)) ×
    StepMoved a s ⟨(entry 2 a, s), (movedLoopWitness a s).2.1⟩ (.inr ⟨(entry 1 (s + a), s + 1), i⟩) :=
  ⟨_, ⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s), .refl, .inr (value 1, s), .refl,
      .inr (value (s + a), s + 1), .refl, ⟨.refl⟩⟩, .refl⟩

set_option smartUnfolding false in
/-- The second iteration. -/
def secondMoved (a s : Nat) : (i : (movedLoopWitness a s).1 (entry 0 ((s + 1) + (s + a)), s + 2)) ×
    StepMoved a s ⟨(entry 1 (s + a), s + 1), (firstMoved a s).1⟩
      (.inr ⟨(entry 0 ((s + 1) + (s + a)), s + 2), i⟩) :=
  ⟨_, ⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s + 1), .refl, .inr (value 0, s + 1), .refl,
      .inr (value ((s + 1) + (s + a)), s + 2), .refl, ⟨.refl⟩⟩, .refl⟩

set_option smartUnfolding false in
/-- The last iteration: the exit. -/
def lastMoved (a s : Nat) :
    StepMoved a s ⟨(entry 0 ((s + 1) + (s + a)), s + 2), (secondMoved a s).1⟩
      (.inl (.inr (out ((s + 1) + (s + a)), s + 2))) :=
  ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s + 2), .refl, ⟨.refl⟩⟩

/-- The run of the loop over the moved witness, from the counter 2. -/
def loopRunMoved (a s : Nat) :
    (Continuation.spec G loopN).Post (entry 2 a, s) (movedLoopWitness a s)
      (.inr (out ((s + 1) + (s + a)), s + 2)) :=
  .next (firstMoved a s).2 (.next (secondMoved a s).2 (.exit (lastMoved a s)))

/-- The run of the second diagram over the moved witness. -/
def movedRun (a s : Nat) :
    (Diagram.spec G countdownN).Post (inputs 2 a, s) (movedWitness a s)
      (.inr (out ((s + 1) + (s + a)), s + 2)) :=
  ⟨.inr (Exits.At.here (entry 2 a), s), ⟨.refl⟩, loopRunMoved a s⟩

set_option smartUnfolding false in
/-- The moved verified diagram gives the condition at the result of a run of the second
diagram over the moved witness: the identity of the runtime at the exit, for an arbitrary
value and an arbitrary runtime. The run goes back along the map of the derivation to a run of
the first diagram, and through the invariant of each iteration. -/
def movedRuntime (a s : Nat) :
    (movedVerified (inputs 2 a, s) ()).2 (.inr (out ((s + 1) + (s + a)), s + 2))
      (movedRun a s) ≡ (Identity.refl : s + 2 ≡ s + 2) := .refl

/-! The second chain: the evidence of the loop alone moves, gets the bound again, and is a
part under the constructor of a composite. -/

/-- The evidence of the second loop with the bound, from the evidence of the first loop: the
witness along the map of the derivation, the bound from the condition at the limit that each
runtime has, and the condition at the result of each run along the map of the runs. -/
def movedLoop (n : Nat) (x : Entry.At Value × Nat) (start : Inv s₀ c₀ x) :
    loopN.Holds G Always n (Final s₀ c₀) x :=
  Continuation.Holds.ofAlways (fun _ => ())
    ((pastToExit.spec (Rules.exitPastSound G)).1 x (loopPastHolds s₀ c₀ 0 x start).parts.1.1).1
    fun o run =>
      ((loopPastHolds s₀ c₀ 0 x start).parts.2 o
        ((((pastToExit.spec (Rules.exitPastSound G)).1 x
          (loopPastHolds s₀ c₀ 0 x start).parts.1.1).2 o).to run)).result

/-- The evidence of the second diagram, by the constructor of a composite, with the moved
evidence of the loop as its later part. -/
def partHolds (n : Nat) (env : All Value [(), ()]) (s : Nat) (pre : unlimited.Pre (env, s)) :
    countdownN.Holds G Always n (unlimited.Post (env, s) pre) (env, s) :=
  Diagram.Holds.seq (S := sig) (Inv s (env.lookup .here)) enter loopN
    (Diagram.Holds.exit _ .refl)
    fun y start => movedLoop s (env.lookup .here) n y start

/-- The witness of the second diagram that this evidence has, from the counter 2. -/
def partWitness (a s : Nat) : (Diagram.spec G countdownN).Pre (inputs 2 a, s) :=
  (partHolds 0 (inputs 2 a) s ()).parts.1.1

/-- The witness of the loop of the second diagram, after the exit to the entrance. -/
def partLoopWitness (a s : Nat) : (Continuation.spec G loopN).Pre (entry 2 a, s) :=
  (partWitness a s).2 (.inr (Exits.At.here (entry 2 a), s)) ⟨.refl⟩

/-- One iteration over that witness. -/
abbrev StepPart (a s : Nat) := (iterSpec G bodyN).iterate (partLoopWitness a s).2.2

set_option smartUnfolding false in
/-- The first iteration, with the invariant witness at the next entrance. -/
def firstPart (a s : Nat) : (i : (partLoopWitness a s).1 (entry 1 (s + a), s + 1)) ×
    StepPart a s ⟨(entry 2 a, s), (partLoopWitness a s).2.1⟩ (.inr ⟨(entry 1 (s + a), s + 1), i⟩) :=
  ⟨_, ⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s), .refl, .inr (value 1, s), .refl,
      .inr (value (s + a), s + 1), .refl, ⟨.refl⟩⟩, .refl⟩

set_option smartUnfolding false in
/-- The second iteration. -/
def secondPart (a s : Nat) : (i : (partLoopWitness a s).1 (entry 0 ((s + 1) + (s + a)), s + 2)) ×
    StepPart a s ⟨(entry 1 (s + a), s + 1), (firstPart a s).1⟩
      (.inr ⟨(entry 0 ((s + 1) + (s + a)), s + 2), i⟩) :=
  ⟨_, ⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s + 1), .refl, .inr (value 0, s + 1), .refl,
      .inr (value ((s + 1) + (s + a)), s + 2), .refl, ⟨.refl⟩⟩, .refl⟩

set_option smartUnfolding false in
/-- The last iteration: the exit. -/
def lastPart (a s : Nat) :
    StepPart a s ⟨(entry 0 ((s + 1) + (s + a)), s + 2), (secondPart a s).1⟩
      (.inl (.inr (out ((s + 1) + (s + a)), s + 2))) :=
  ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s + 2), .refl, ⟨.refl⟩⟩

/-- The run of the loop over that witness, from the counter 2. -/
def loopRunPart (a s : Nat) :
    (Continuation.spec G loopN).Post (entry 2 a, s) (partLoopWitness a s)
      (.inr (out ((s + 1) + (s + a)), s + 2)) :=
  .next (firstPart a s).2 (.next (secondPart a s).2 (.exit (lastPart a s)))

/-- The run of the second diagram over that witness. -/
def partRun (a s : Nat) :
    (Diagram.spec G countdownN).Post (inputs 2 a, s) (partWitness a s)
      (.inr (out ((s + 1) + (s + a)), s + 2)) :=
  ⟨.inr (Exits.At.here (entry 2 a), s), ⟨.refl⟩, loopRunPart a s⟩

set_option smartUnfolding false in
/-- The evidence of the second diagram gives the condition at the result of a run over its
witness. The moved evidence of the loop is a part of it. -/
def partRuntime (a s : Nat) :
    ((partHolds 0 (inputs 2 a) s ()).parts.2 (.inr (out ((s + 1) + (s + a)), s + 2))
      (partRun a s)).result ≡ (Identity.refl : s + 2 ≡ s + 2) := .refl

/-! A real bound along a derivation. The second exit equation holds in each congruence, so the
approximants of the two diagrams have one machine at each number of unrollings. The evidence
of the machine of the countdown, from the family with a count, moves along the derivation to
the machine of the loop whose exit is an exit past a continuation. No constructor gives the
evidence of that loop. -/

open Draft.Checks.Specification.Bound (bounded countdownImpl)

/-- The second exit equation holds in each congruence. -/
def exitPastSound.{w} {α : Type} {eqv : Free.Congruence.{0, 0, 0, w} (sig.interface Value) α} :
    (Rules.exitPast sig).Sound eqv :=
  ⟨fun stop n => Diagram.ExitPast.sound stop n, fun _ _ => fun r => nomatch r⟩

variable (stop : Free (sig.interface Value) (Exits.At [Out] Value))

/-- The evidence of the machine of the countdown, from the family with a count. -/
def boundedEvidence (n : Nat) : Evidence (bounded n) (machine.impl (countdownN.impl stop n)) :=
  (countdownImpl stop n).run machine.graphEvidence

/-- The evidence of the machine of the loop whose exit is an exit past a continuation, along
the derivation. -/
def boundedMoved (n : Nat) : Evidence (bounded n) (machine.impl (countdownPast.impl stop n)) :=
  Diagram.Derivation.evidence (m := machine) exitPastSound (.symm optimize) stop n
    (boundedEvidence stop n)

set_option smartUnfolding false in
/-- From the counter 2, with each number of unrollings that is three or more. -/
def boundedMovedAtExit (k a s : Nat) :
    Final s 2 (machine.run (countdownPast.run stop (k + 3) (inputs 2 a) .pure) s) :=
  boundedMoved stop (k + 3) (inputs 2 a, s) ⟨k, .refl⟩

set_option smartUnfolding false in
/-- The moved evidence is consumed through a dependent payload, for an arbitrary value, an
arbitrary runtime, and an arbitrary computation at the limit. -/
def boundedMovedRuntime (k a s : Nat) :
    (Identity.transport (fun j => Fin (j + 1)) (boundedMovedAtExit stop k a s)
      ⟨s + 2, Nat.lt_succ_self _⟩).val ≡ s + 2 := .refl

end Draft.Checks.Specification.Optimize

namespace Draft.Checks.Specification.Peel

open Draft Draft.Checks.Countdown Draft.Checks.Specification
open Draft.Checks.Specification.Invariant (Inv Final Always loopHolds)
open Draft.Checks.Specification.Optimize (unlimited)
open Draft.Checks.Specification.Bound (Below Count never)

/-! The peel of the countdown loop. The peeled diagram has the exit to the entrance, one copy
of the body, and then the loop. -/

/-- The diagram of each case of the body of the countdown loop. -/
abbrev each : (c : Entry.Case) → Diagram sig c.1 [Entry, Out] :=
  Boundary.family (F := fun Δ => Diagram sig Δ [Entry, Out]) (.cons iteration .nil)

/-- The peeled diagram. -/
def countdownPeeled : Diagram sig [(), ()] [Out] := .seq enter (Continuation.peeled each)

/-- The evidence of the peeled diagram, for a loop with no limit: the evidence of the loop
along the peel is the later part under the constructor of a composite. -/
def peeledHolds (n : Nat) (env : All Value [(), ()]) (s : Nat) (pre : unlimited.Pre (env, s)) :
    countdownPeeled.Holds G Always n (unlimited.Post (env, s) pre) (env, s) :=
  Diagram.Holds.seq (S := sig) (Inv s (env.lookup .here)) enter (Continuation.peeled each)
    (Diagram.Holds.exit _ .refl)
    fun y start =>
      Continuation.Holds.peel each (fun _ => ()) (loopHolds s (env.lookup .here) 0 y start)

/-- The witness of the peeled diagram that this evidence has, from the counter 2. -/
def peeledWitness (a s : Nat) : (Diagram.spec G countdownPeeled).Pre (inputs 2 a, s) :=
  (peeledHolds 0 (inputs 2 a) s ()).parts.1.1

/-- The witness of the copy of the body, and then the loop, after the exit to the entrance. -/
def copyWitness (a s : Nat) :
    (Diagram.spec G ((each ⟨_, .here⟩).seq loop)).Pre (inputs 2 a, s) :=
  (peeledWitness a s).2 (.inr (Exits.At.here (entry 2 a), s)) ⟨.refl⟩

set_option smartUnfolding false in
/-- The run of the copy of the body, to the entrance of the loop. -/
def copyRun (a s : Nat) :
    (Diagram.spec G iteration).Post (inputs 2 a, s) (copyWitness a s).1
      (.inr (Exits.At.here (entry 1 (s + a)), s + 1)) :=
  ⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s), .refl, .inr (value 1, s), .refl,
    .inr (value (s + a), s + 1), .refl, ⟨.refl⟩⟩

/-- The witness of the loop after the copy of the body. -/
def afterCopy (a s : Nat) : (Continuation.spec G loop).Pre (entry 1 (s + a), s + 1) :=
  (copyWitness a s).2 (.inr (Exits.At.here (entry 1 (s + a)), s + 1)) (copyRun a s)

/-- One iteration of the loop over that witness. -/
abbrev StepPeeled (a s : Nat) := (iterSpec G body).iterate (afterCopy a s).2.2

set_option smartUnfolding false in
/-- The iteration of the loop, with the invariant witness at the next entrance. -/
def secondPeeled (a s : Nat) : (i : (afterCopy a s).1 (entry 0 ((s + 1) + (s + a)), s + 2)) ×
    StepPeeled a s ⟨(entry 1 (s + a), s + 1), (afterCopy a s).2.1⟩
      (.inr ⟨(entry 0 ((s + 1) + (s + a)), s + 2), i⟩) :=
  ⟨_, ⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s + 1), .refl, .inr (value 0, s + 1), .refl,
      .inr (value ((s + 1) + (s + a)), s + 2), .refl, ⟨.refl⟩⟩, .refl⟩

set_option smartUnfolding false in
/-- The last iteration: the exit. -/
def lastPeeled (a s : Nat) :
    StepPeeled a s ⟨(entry 0 ((s + 1) + (s + a)), s + 2), (secondPeeled a s).1⟩
      (.inl (.inr (out ((s + 1) + (s + a)), s + 2))) :=
  ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s + 2), .refl, ⟨.refl⟩⟩

/-- The run of the peeled diagram over the witness, from the counter 2. The run of the copy
of the body is the first iteration, and the loop has the others. -/
def peeledRun (a s : Nat) :
    (Diagram.spec G countdownPeeled).Post (inputs 2 a, s) (peeledWitness a s)
      (.inr (out ((s + 1) + (s + a)), s + 2)) :=
  ⟨.inr (Exits.At.here (entry 2 a), s), ⟨.refl⟩,
    ⟨.inr (Exits.At.here (entry 1 (s + a)), s + 1), copyRun a s,
      .next (secondPeeled a s).2 (.exit (lastPeeled a s))⟩⟩

set_option smartUnfolding false in
/-- The evidence along the peel gives the condition at the result of a run of the peeled
diagram: the identity of the runtime at the exit, for an arbitrary value and an arbitrary
runtime. The run goes back along the peel to a run of the loop. -/
def peeledRuntime (a s : Nat) :
    ((peeledHolds 0 (inputs 2 a) s ()).parts.2 (.inr (out ((s + 1) + (s + a)), s + 2))
      (peeledRun a s)).result ≡ (Identity.refl : s + 2 ≡ s + 2) := .refl

variable (stop : Free (sig.interface Value) (Exits.At [Out] Value))

/-- The specification of the peeled diagram with a number of unrollings. A witness of the
precondition shows that the counter is less than that number plus one: the copy of the body
is one iteration, and the loop has the others. -/
def boundedPeeled (n : Nat) :
    DepPoly.{0, 0, 0, 0} ((Diagram.interface Value [(), ()] [Out]).runtime Nat Unit) where
  Pre x := Below (x.1.lookup .here) (n + 1)
  Post x _ := Final x.2 (x.1.lookup .here)

/-- The evidence of the peeled diagram with a real bound, by the constructors. The copy of the
body goes from the family at one more than the number of unrollings to the family at that
number, and the loop takes it. -/
def peeledBounded (n : Nat) (env : All Value [(), ()]) (s : Nat)
    (pre : (boundedPeeled n).Pre (env, s)) :
    countdownPeeled.Holds G Never n ((boundedPeeled n).Post (env, s) pre) (env, s) :=
  Diagram.Holds.seq (S := sig) (Count s (env.lookup .here) (n + 1)) enter
    (Continuation.peeled each) (Diagram.Holds.exit _ (.refl, pre))
    fun y first =>
      Continuation.Holds.copair _
        (Diagram.Holds.seq (S := sig) (Count s (env.lookup .here) n) (each y.1.1) loop
          (Continuation.Holds.uncopair each
            (Bound.bodyHolds s (env.lookup .here) n n y first))
          fun _ start =>
            Continuation.Holds.loopCounted (Count s (env.lookup .here)) body
              (Bound.bodyHolds s (env.lookup .here) n) (never s (env.lookup .here)) start)

/-- The verified implementation of the approximant of the peeled diagram, with no evidence for
the computation at the limit. -/
def peeledBoundedImpl (n : Nat) :
    ImplDep (boundedPeeled n) G (countdownPeeled.impl stop n).thread :=
  Diagram.Holds.impl (fun x pre => peeledBounded n x.1 x.2 pre) fun _ _ _ e => e.elim

set_option smartUnfolding false in
/-- The evidence at the result of the run of the peeled diagram, from the counter 2 with two
or more unrollings and the empty condition at the limit. -/
def boundedAtExit (k a s : Nat) :
    Final s 2 (machine.run (countdownPeeled.run stop (k + 2) (inputs 2 a) .pure) s) :=
  ((peeledBoundedImpl stop (k + 2)).run machine.graphEvidence) (inputs 2 a, s) ⟨k, .refl⟩

set_option smartUnfolding false in
/-- The evidence with the real bound is consumed through a dependent payload, for an arbitrary
computation at the limit. -/
def boundedRuntime (k a s : Nat) :
    (Identity.transport (fun j => Fin (j + 1)) (boundedAtExit stop k a s)
      ⟨s + 2, Nat.lt_succ_self _⟩).val ≡ s + 2 := .refl

end Draft.Checks.Specification.Peel

/-- info: 'Draft.Checks.Specification.thresholdTwo' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.thresholdTwo

/-- info: 'Draft.Checks.Specification.roundTrip' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.roundTrip

/-- info: 'Draft.Checks.Specification.limitFree' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.limitFree

/-- info: 'Draft.Checks.Specification.thresholdNested' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.thresholdNested

/-- info: 'Draft.Checks.Specification.roundTripNested' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.roundTripNested

/-- info: 'Draft.Checks.Specification.ExitEquations.loopOfWhole' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.ExitEquations.loopOfWhole

/-- info: 'Draft.Checks.Specification.ExitEquations.loopOfWholeBack' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.ExitEquations.loopOfWholeBack

/-- info: 'Draft.Checks.Specification.ExitEquations.unrolledLength' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.ExitEquations.unrolledLength

/-- info: 'Draft.Checks.Specification.ExitEquations.unrolledBack' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.ExitEquations.unrolledBack

/-- info: 'Draft.Checks.Specification.ExitEquations.fixpointBack' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.ExitEquations.fixpointBack

/-- info: 'Draft.Checks.Specification.movedRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.movedRun

/-- info: 'Draft.Checks.Specification.movedBack' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.movedBack

/-- info: 'Draft.Checks.Specification.movedRound' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.movedRound

/-- info: 'Draft.Checks.Specification.roundOne' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.roundOne

/-- info: 'Draft.Checks.Specification.wholeBack' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.wholeBack

/-- info: 'Draft.Checks.Specification.wholeRound' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.wholeRound

/-- info: 'Draft.Checks.Specification.wholeRoundBack' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.wholeRoundBack

/-- info: 'Draft.Checks.Specification.pastRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.pastRun

/-- info: 'Draft.Checks.Specification.pastBack' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.pastBack

/-- info: 'Draft.Checks.Specification.Invariant.runtimeAtExit' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.Invariant.runtimeAtExit

/-- info: 'Draft.Checks.Specification.Bound.runtimeAtExit' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.Bound.runtimeAtExit

/-- info: 'Draft.Checks.Specification.Bound.runtimeAtExitOne' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.Bound.runtimeAtExitOne

/-- info: 'Draft.Checks.Specification.Bound.twoLoopsRuntime' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.Bound.twoLoopsRuntime

/-- info: 'Draft.Checks.Specification.Optimize.movedRuntime' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.Optimize.movedRuntime

/-- info: 'Draft.Checks.Specification.Optimize.partRuntime' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.Optimize.partRuntime

/-- info: 'Draft.Checks.Specification.Optimize.boundedMovedRuntime' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.Optimize.boundedMovedRuntime

/-- info: 'Draft.Checks.Specification.Peel.peeledRuntime' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.Peel.peeledRuntime

/-- info: 'Draft.Checks.Specification.Peel.boundedRuntime' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Specification.Peel.boundedRuntime
