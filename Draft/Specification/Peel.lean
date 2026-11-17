import Draft.Specification.Verified

/-! The peel of a loop.

The peeled continuation of a loop has one copy of the body, and then the loop. The peel is a
map of specifications: a witness of the precondition of the loop gives a witness of the
precondition of the peeled continuation, and a run of the peeled continuation over that
witness gives a run of the loop over the first witness. The run of the copy of the body is the
first iteration of the run of the loop. The evidence of the loop gives the evidence of the
peeled continuation along this map, for a condition at the limit that each runtime has. -/

set_option autoImplicit false
set_option genInjectivity false

universe w z a b v w' z' c d

open Prelude Container

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E)) {K : Boundary Ty} {Qs : Exits Ty}
  (each : (c : K.Case) → Diagram S c.1 (K :: Qs))

/-- One copy of the body of a loop, and then the loop. -/
abbrev Continuation.peeled : Continuation S K Qs :=
  .copair fun c => .seq (each c) (.loop (.copair each))

section Maps

variable {Inv : K.At X × R → Type z}
  (keeps : (iterSpec r (Continuation.copair each)).Keeps Inv) (x : K.At X × R) (i : Inv x)

/-- The witness of the loop at an exit of the copy of the body: the invariant at the next
entrance. -/
def Continuation.peelExit (s' : R) : (e' : Exits.At (K :: Qs) X) →
    (Diagram.spec r (each x.1.1)).Post (x.1.2, x.2) (keeps x i).1 (.inr (e', s')) →
    Spec.exitPre
      (fun k => (Continuation.spec r (Continuation.loop (.copair each))).Pre (k, s')) e' :=
  Exits.At.cases
    (motive := fun e' =>
      (Diagram.spec r (each x.1.1)).Post (x.1.2, x.2) (keeps x i).1 (.inr (e', s')) →
      Spec.exitPre
        (fun k => (Continuation.spec r (Continuation.loop (.copair each))).Pre (k, s')) e')
    (fun k post => ⟨Inv, (keeps x i).2 (k, s') post, keeps⟩) (fun _ _ => PUnit.unit)

/-- The witness of the loop at each result of the copy of the body. -/
def Continuation.peelWitness : (m : E ⊕ (Exits.At (K :: Qs) X × R)) →
    (Diagram.spec r (each x.1.1)).Post (x.1.2, x.2) (keeps x i).1 m →
    Spec.resumePre (fun (y : Exits.At (K :: Qs) X × R) =>
      Spec.exitPre
        (fun k => (Continuation.spec r (Continuation.loop (.copair each))).Pre (k, y.2)) y.1) m
  | .inl _, _ => PUnit.unit
  | .inr y, post => Continuation.peelExit r each keeps x i y.2 y.1 post

/-- A run of the loop, from the run of the copy of the body to an exit and the run after that
exit. -/
def Continuation.peelExitRun (s' : R) (o : E ⊕ (Qs.At X × R)) : (e' : Exits.At (K :: Qs) X) →
    (post : (Diagram.spec r (each x.1.1)).Post (x.1.2, x.2) (keeps x i).1 (.inr (e', s'))) →
    Spec.atExit (fun k => (Continuation.spec r (Continuation.loop (.copair each))).Pre (k, s'))
      (fun k p o => (Continuation.spec r (Continuation.loop (.copair each))).Post (k, s') p o)
      (fun q o => Spec.Result (Sum.inr (q, s') : E ⊕ (Qs.At X × R)) o) e'
      (Continuation.peelExit r each keeps x i s' e' post) o →
    Loop ((iterSpec r (Continuation.copair each)).iterate keeps) ⟨x, i⟩ o :=
  Exits.At.cases
    (motive := fun e' =>
      (post : (Diagram.spec r (each x.1.1)).Post (x.1.2, x.2) (keeps x i).1 (.inr (e', s'))) →
      Spec.atExit (fun k => (Continuation.spec r (Continuation.loop (.copair each))).Pre (k, s'))
        (fun k p o => (Continuation.spec r (Continuation.loop (.copair each))).Post (k, s') p o)
        (fun q o => Spec.Result (Sum.inr (q, s') : E ⊕ (Qs.At X × R)) o) e'
        (Continuation.peelExit r each keeps x i s' e' post) o →
      Loop ((iterSpec r (Continuation.copair each)).iterate keeps) ⟨x, i⟩ o)
    (fun k post tail =>
      Loop.next (F := (iterSpec r (Continuation.copair each)).iterate keeps)
        (a' := (⟨(k, s'), (keeps x i).2 (k, s') post⟩ : (y : K.At X × R) × Inv y))
        ⟨post, .refl⟩ tail)
    (fun _ post tail =>
      Identity.transport
        (fun o => Loop ((iterSpec r (Continuation.copair each)).iterate keeps) ⟨x, i⟩ o)
        tail.down (Loop.exit post))

/-- A run of the loop, from the run of the copy of the body and the run after its result. -/
def Continuation.peelRun (o : E ⊕ (Qs.At X × R)) : (m : E ⊕ (Exits.At (K :: Qs) X × R)) →
    (post : (Diagram.spec r (each x.1.1)).Post (x.1.2, x.2) (keeps x i).1 m) →
    Spec.resumePost
      (fun (y : Exits.At (K :: Qs) X × R) p o =>
        Spec.atExit
          (fun k => (Continuation.spec r (Continuation.loop (.copair each))).Pre (k, y.2))
          (fun k p o => (Continuation.spec r (Continuation.loop (.copair each))).Post (k, y.2) p o)
          (fun q o => Spec.Result (Sum.inr (q, y.2) : E ⊕ (Qs.At X × R)) o) y.1 p o)
      m (Continuation.peelWitness r each keeps x i m post) o →
    Loop ((iterSpec r (Continuation.copair each)).iterate keeps) ⟨x, i⟩ o
  | .inl _, post, tail =>
      Identity.transport
        (fun o => Loop ((iterSpec r (Continuation.copair each)).iterate keeps) ⟨x, i⟩ o)
        tail.down (Loop.exit post)
  | .inr y, post, tail => Continuation.peelExitRun r each keeps x i y.2 o y.1 post tail

end Maps

variable (x : K.At X × R)

/-- A witness of the precondition of the loop gives a witness of the precondition of one copy
of the body, and then the loop. -/
def Continuation.peelPre (p : (Continuation.spec r (Continuation.loop (.copair each))).Pre x) :
    (Continuation.spec r (Continuation.peeled each)).Pre x :=
  ⟨(p.2.2 x p.2.1).1, Continuation.peelWitness r each p.2.2 x p.2.1⟩

/-- A run of one copy of the body, and then the loop, over that witness gives a run of the
loop over the first witness. -/
def Continuation.peelPost (p : (Continuation.spec r (Continuation.loop (.copair each))).Pre x)
    (o : E ⊕ (Qs.At X × R))
    (run : (Continuation.spec r (Continuation.peeled each)).Post x
      (Continuation.peelPre r each x p) o) :
    (Continuation.spec r (Continuation.loop (.copair each))).Post x p o :=
  Continuation.peelRun r each p.2.2 x p.2.1 o run.1 run.2.1 run.2.2

section Evidence

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  {r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E)} {L : R → Type c} {n : Nat}
  {K : Boundary Ty} {Qs : Exits Ty}

/-- The evidence of one copy of the body, and then the loop, from the evidence of the loop,
for a condition at the limit that each runtime has. The witness and the condition at the
result of each run are along the peel. -/
def Continuation.Holds.peel (each : (c : K.Case) → Diagram S c.1 (K :: Qs))
    (always : (s : R) → L s) {P : E ⊕ (Qs.At X × R) → Type v} {x : K.At X × R} {m : Nat}
    (h : (Continuation.loop (.copair each)).Holds r L m P x) :
    (Continuation.peeled each).Holds r L n P x :=
  Continuation.Holds.ofAlways always (Continuation.peelPre r each x h.parts.1.1)
    fun o run => (h.parts.2 o (Continuation.peelPost r each x h.parts.1.1 o run)).result

end Evidence

end Draft
