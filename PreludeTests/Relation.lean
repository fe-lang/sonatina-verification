import Prelude

/-! Checks for `Prelude.Relation`: paths, accessibility, computations, and loops. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude
open scoped Prelude

namespace PreludeTests

-- Execution paths retain both labels and lengths, including self-loops.
inductive Tick : Nat → Nat → Type where
  | tick (n : Nat) (label : Bool) : Tick n n

def once : Steps Tick 0 0 := .single (.tick 0 true)
def twice : Steps Tick 0 0 := once.append (.single (.tick 0 false))

#guard once.length == 1
#guard twice.length == 2
#guard ((twice.append once).map id (fun p => p)).length == 3

def pathAssociativity : (twice.append once).append twice ≡ twice.append (once.append twice) :=
  twice.appendAssoc once twice

def pathFold : (0 : Nat) = 0 :=
  twice.foldProp (fun _ => rfl) Eq.trans (fun p => by cases p; rfl)

-- Accessibility drives a computable, dependent eliminator.
inductive Pred : Nat → Nat → Type where
  | step (n : Nat) : Pred n (n + 1)

/-- The target of a step, by a match whose index is a variable. -/
def Pred.target : {m k : Nat} → Pred m k → k ≡ m + 1
  | _, _, .step _ => .refl

def accessible : (n : Nat) → Accessible Pred n
  | 0 => .intro (fun _ p =>
      (Identity.transport (Nat.rec Unit fun _ _ => Empty) p.target ()).elim)
  | n + 1 => .intro (fun _ p =>
      Identity.transport (Accessible Pred) (Identity.cong Nat.pred p.target) (accessible n))

def countDown (n : Nat) : Nat :=
  Accessible.fold (R := Pred) (P := fun _ => Nat)
    (fun x recurse => match x with
      | 0 => 0
      | n + 1 => recurse n (.step n) + 1) n (accessible n)

#guard countDown 12 == 12

-- The fold computes in the kernel through the accessibility witness.
def countDownStep (n : Nat) : countDown (n + 1) ≡ countDown n + 1 := .refl

/-- info: 'PreludeTests.countDownStep' does not depend on any axioms -/
#guard_msgs in
#print axioms countDownStep

/-- info: 'Prelude.Steps.appendAssoc' does not depend on any axioms -/
#guard_msgs in
#print axioms Steps.appendAssoc

/-! ### Computations -/

namespace GraphChecks

/-- A computation whose runs have data: a run from `b` to `c` is a number below `c`, when `c`
is `b + 1`. -/
def after : Rel.{0, 0, 0} Nat Nat := fun b c => (b + 1 ≡ c) × Fin c

/-- A run of the graph of the successor and then the computation, with the runs of the graph
at a higher level. -/
def composite (n : Nat) (i : Fin (n + 2)) :
    Rel.seq (Rel.lift.{0, 0, 0, 1} (Rel.graph Nat.succ)) after n (n + 2) :=
  ⟨n + 1, ⟨.refl⟩, .refl, i⟩

-- The law gives the run of the computation at the value of the function, for an arbitrary
-- input and arbitrary data, and its inverse gives the first run.
def graphSeqTo (n : Nat) (i : Fin (n + 2)) :
    (Rel.graphSeq Nat.succ after n (n + 2)).to (composite n i) ≡ (.refl, i) := .refl

def graphSeqBack (n : Nat) (i : Fin (n + 2)) :
    (Rel.graphSeq Nat.succ after n (n + 2)).invTo (composite n i) ≡ .refl := .refl

/-- info: 'Prelude.Rel.graphSeq' does not depend on any axioms -/
#guard_msgs in
#print axioms Rel.graphSeq

end GraphChecks

/-! ### Loops -/

namespace LoopChecks

def distribute {S U V : Type} : S × (U ⊕ V) → (S × U) ⊕ (S × V)
  | (s, .inl u) => .inl (s, u)
  | (s, .inr v) => .inr (s, v)

/-- Add the counter to the state and count down. The first component is the runtime. -/
def body : Nat × Nat → Nat × (Unit ⊕ Nat)
  | (s, 0) => (s, .inl ())
  | (s, n + 1) => (s + (n + 1), .inr n)

def loop (x : Nat × Nat) : (Nat × Unit) ⊕ (Nat × Nat) := distribute (body x)

abbrev Run (s : Nat) : Type := Loop (Rel.graph loop) (s, 3) (s + 3 + 2 + 1, ())

/-- The run from the counter 3, for an arbitrary initial state. -/
def run3 (s : Nat) : Run s :=
  .next .refl (.next .refl (.next .refl (.exit .refl)))

def decreases : (a a' : Nat × Nat) → loop a ≡ .inr a' → a'.2 < a.2
  | (_, 0), _, e => (Identity.inlNotInr e).elim
  | (_, n + 1), _, e =>
    Identity.transport (fun v : Nat × Nat => v.2 < n + 1) (Identity.inrInject e)
      (Nat.lt_succ_self n)

def measured (s : Nat) : Loop.Domain loop (s, 3) :=
  Loop.Domain.ofMeasure loop (fun a => a.2) decreases 4 (s, 3) (Nat.lt_succ_self 3)

-- The run, the result on the domain evidence, and the function with fuel agree.
def lengthCheck (s : Nat) : (run3 s).length ≡ 4 := .refl
def measuredCheck (s : Nat) : (measured s).eval ≡ (s + 3 + 2 + 1, ()) := .refl
def domainCheck (s : Nat) : (run3 s).domain.eval ≡ (s + 3 + 2 + 1, ()) := .refl
def fuelCheck (s : Nat) : Loop.fuel loop 4 (s, 3) ≡ some (s + 3 + 2 + 1, ()) := .refl
def fuelCompleteCheck (s : Nat) : Loop.fuelComplete loop (run3 s) ≡ .refl := .refl
def fuelSoundCheck (s : Nat) :
    (Loop.fuelSound loop 9 (s, 3) (s + 3 + 2 + 1, ()) .refl).length ≡ 4 := .refl

#guard Loop.fuel loop 9 (10, 3) == some (16, ())
#guard Loop.fuel loop 3 (10, 3) == none

-- The domain evidence from the measure and the evidence from the run are one witness.
def domainUniqueCheck (s : Nat) :
    Loop.Domain.unique (measured s) (run3 s).domain ≡ .refl := .refl

-- A run is a path of three continue steps and one exit step.
def pathCheck (s : Nat) : ((Loop.path _ _ _).to (run3 s)).2.1.length ≡ 3 := .refl
def pathRoundTrip (s : Nat) : (Loop.path _ _ _).invTo (run3 s) ≡ .refl := .refl

-- The fixpoint maps are inverse on the run.
def fixpointRoundTrip (s : Nat) : (Loop.fixpoint _ _ _).invTo (run3 s) ≡ .refl := .refl

-- Unrolling changes the length of the run, and its inverse gives the first run again.
def unrolling (s : Nat) : Iso (Run s) (Loop (Rel.graph loop).twice (s, 3) (s + 3 + 2 + 1, ())) :=
  Loop.unrolling (Rel.graph loop) _ _

def unrollLength (s : Nat) : ((unrolling s).to (run3 s)).length ≡ 2 := .refl
def unrollRoundTrip (s : Nat) : (unrolling s).inv ((unrolling s).to (run3 s)) ≡ run3 s := .refl
def unrollRoundTripIsRefl (s : Nat) : (unrolling s).invTo (run3 s) ≡ .refl := .refl

-- A mark for one iteration of the run moves to the unrolled run and back.
abbrev Mark (s : Nat) (r : Run s) : Type := Fin r.length

def markCheck (s : Nat) (i : Fin 4) :
    (unrolling s).back (Mark s) (run3 s) ((unrolling s).across (Mark s) (run3 s) i) ≡ i := .refl
def markRoundTripIsRefl (s : Nat) (i : Fin 4) :
    (unrolling s).backAcross (Mark s) (run3 s) i ≡ .refl := .refl

-- The two runs have one result, and a family on the result consumes the identity.
def resultCheck (s : Nat) :
    Identity.transport (fun p : Nat × Unit => Fin (p.1 + 1))
      (Loop.resultUnique (run3 s) ((unrolling s).inv ((unrolling s).to (run3 s))))
      ⟨0, Nat.zero_lt_succ _⟩ ≡ ⟨0, Nat.zero_lt_succ _⟩ := .refl

-- The maps of strength, naturality, and uniformity keep the run.
def strengthCheck (s c : Nat) :
    Loop.strengthTo (Loop.strengthFrom c (run3 s)) ≡ ⟨.refl, run3 s⟩ := .refl
def strengthRoundTripIsRefl (s c : Nat) : Loop.strengthToFrom c (run3 s) ≡ .refl := .refl
def naturalCheck (s : Nat) :
    (Loop.naturalTo (Loop.naturalFrom (K := Rel.graph Prod.fst) (run3 s) .refl)).2.1 ≡ run3 s :=
  .refl
def uniformCheck (s : Nat) :
    Loop.uniformFrom (G := Rel.graph loop) id
      (fun _ t p => ⟨t, p, match t with | .inl _ => .refl | .inr _ => .refl⟩)
      (Loop.uniformTo (F := Rel.graph loop) id
        (fun _ t p => match t, p with | .inl _, p => p | .inr _, p => p) (run3 s))
      _ .refl ≡ run3 s := .refl

/-- A body with two continue cases: the outer case above the counter 1, and the inner case
at the counter 1. -/
def split : Nat × Nat → ((Nat × Unit) ⊕ (Nat × Nat)) ⊕ (Nat × Nat)
  | (s, 0) => .inl (.inl (s, ()))
  | (s, 1) => .inr (s + 1, 0)
  | (s, n + 2) => .inl (.inr (s + (n + 2), n + 1))

def merged3 (s : Nat) : Loop (Rel.merged (Rel.graph split)) (s, 3) (s + 3 + 2 + 1, ()) :=
  .next ⟨.inl (.inr (s + 3, 2)), .refl, .refl⟩
    (.next ⟨.inl (.inr (s + 3 + 2, 1)), .refl, .refl⟩
      (.next ⟨.inr (s + 3 + 2 + 1, 0), .refl, .refl⟩
        (.exit ⟨.inl (.inl (s + 3 + 2 + 1, ())), .refl, .refl⟩)))

-- The codiagonal maps give three runs of the inner loop, and the first run again.
def codiagonalLength (s : Nat) : (Loop.codiagonalTo (merged3 s)).length ≡ 3 := .refl
def codiagonalCheck (s : Nat) :
    Loop.codiagonalFrom (Loop.codiagonalTo (merged3 s)) ≡ merged3 s := .refl

/-- info: 'Prelude.Loop.elimUnique' does not depend on any axioms -/
#guard_msgs in
#print axioms Loop.elimUnique

/-- info: 'Prelude.Loop.fixpoint' does not depend on any axioms -/
#guard_msgs in
#print axioms Loop.fixpoint

/-- info: 'Prelude.Loop.unrolling' does not depend on any axioms -/
#guard_msgs in
#print axioms Loop.unrolling

/-- info: 'Prelude.Loop.Domain.unique' does not depend on any axioms -/
#guard_msgs in
#print axioms Loop.Domain.unique

/-- info: 'PreludeTests.LoopChecks.markRoundTripIsRefl' does not depend on any axioms -/
#guard_msgs in
#print axioms markRoundTripIsRefl

/-- info: 'PreludeTests.LoopChecks.domainUniqueCheck' does not depend on any axioms -/
#guard_msgs in
#print axioms domainUniqueCheck

/-- info: 'PreludeTests.LoopChecks.fuelSoundCheck' does not depend on any axioms -/
#guard_msgs in
#print axioms fuelSoundCheck

end LoopChecks

/-! ### Loops at different universe levels -/

namespace LevelChecks

/-- A body with the state in `Type` and the result in `Type 1`: count down, and exit with the
type of the bounded numbers of the initial state. -/
def body : Nat × Nat → Type ⊕ (Nat × Nat)
  | (s, 0) => .inl (Fin (s + 1))
  | (s, n + 1) => .inr (s, n)

abbrev Run (s : Nat) : Type 1 := Loop (Rel.graph body) (s, 2) (Fin (s + 1))

def run2 (s : Nat) : Run s := .next .refl (.next .refl (.exit .refl))

def lengthCheck (s : Nat) : (run2 s).length ≡ 3 := .refl
def fuelCheck (s : Nat) : Loop.fuel body 3 (s, 2) ≡ some (Fin (s + 1)) := .refl
def domainCheck (s : Nat) : (run2 s).domain.eval ≡ Fin (s + 1) := .refl
def fixpointRoundTrip (s : Nat) : (Loop.fixpoint _ _ _).invTo (run2 s) ≡ .refl := .refl
def unrollRoundTrip (s : Nat) : (Loop.unrolling _ _ _).invTo (run2 s) ≡ .refl := .refl

-- The result is a type, and an element of it moves along the identity of the two results.
def resultCheck (s : Nat) :
    Identity.cast (Loop.resultUnique (run2 s) ((Loop.unrolling _ _ _).inv
      ((Loop.unrolling _ _ _).to (run2 s)))) (0 : Fin (s + 1)) ≡ 0 := .refl

-- A computation on the result at a third level: the exit case of naturality.
def naturalCheck (s : Nat) :
    (Loop.naturalTo (Loop.naturalFrom (K := Rel.graph (fun X : Type => ULift.{2} X))
      (run2 s) .refl)).2.1 ≡ run2 s := .refl

/-- info: 'PreludeTests.LevelChecks.fixpointRoundTrip' does not depend on any axioms -/
#guard_msgs in
#print axioms fixpointRoundTrip

/-- info: 'PreludeTests.LevelChecks.naturalCheck' does not depend on any axioms -/
#guard_msgs in
#print axioms naturalCheck

end LevelChecks

end PreludeTests
