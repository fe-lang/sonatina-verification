import Draft.Specification.Verified

/-! The specification of a diagram for the graph of a machine.

The graph of a machine is a specification of the calls. A witness of the precondition of a step
is a witness of the precondition after the response of the machine, a run of a step is a run
after that response, and the bound of a step is the bound after that response. Each diagram has
a witness of its precondition for the graph of a machine. -/

set_option autoImplicit false
set_option genInjectivity false

universe w z a b v w' z' c d

open Prelude Container

namespace Draft

section Graph

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  (m : Machine (S.interface X) R E) {Γ : List Ty} {Qs : Exits Ty}
  (call : (S.interface (Port Γ)).Shape)
  (next : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs) (a : All X Γ × R)

abbrev StepPre : E ⊕ ((S.output call.1).At X × R) → Type 1 :=
  Spec.resumePre fun (y : (S.output call.1).At X × R) =>
    (Diagram.spec m.graph (next y.1.1)).Pre (y.1.2.append a.1, y.2)

abbrev StepPost (x : E ⊕ ((S.output call.1).At X × R)) (p : StepPre m call next a x)
    (o : E ⊕ (Qs.At X × R)) : Type :=
  Spec.resumePost
    (fun (y : (S.output call.1).At X × R) p o =>
      (Diagram.spec m.graph (next y.1.1)).Post (y.1.2.append a.1, y.2) p o) x p o

/-- For the graph of a machine, a witness of the precondition of a step is a witness of the
precondition after the response of the machine. -/
def stepPre (h : StepPre m call next a (m (⟨call.1, a.1.select call.2⟩, a.2))) :
    (Diagram.spec m.graph (Diagram.step call next)).Pre a :=
  ⟨PUnit.unit, fun _ e => Identity.transport (StepPre m call next a) e h⟩

/-- For the graph of a machine, a run of a step over that witness is a run after the response
of the machine. -/
def stepPost (h : StepPre m call next a (m (⟨call.1, a.1.select call.2⟩, a.2)))
    (o : E ⊕ (Qs.At X × R))
    (run : (Diagram.spec m.graph (Diagram.step call next)).Post a
      (stepPre m call next a h) o) :
    StepPost m call next a (m (⟨call.1, a.1.select call.2⟩, a.2)) h o :=
  Identity.ind
    (fun (x : E ⊕ ((S.output call.1).At X × R)) (e : m (⟨call.1, a.1.select call.2⟩, a.2) ≡ x) =>
      StepPost m call next a x (Identity.transport (StepPre m call next a) e h) o →
        StepPost m call next a (m (⟨call.1, a.1.select call.2⟩, a.2)) h o)
    (fun run => run) run.2.1 run.2.2

end Graph

section GraphBound

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  (m : Machine (S.interface X) R E)

mutual

/-- The witness of the precondition of a diagram, for the graph of a machine: each step has
the witness after the response of the machine. -/
def Diagram.graphWitness : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    (a : All X Γ × R) → (Diagram.spec m.graph d).Pre a
  | _, _, .exit _, _ => PUnit.unit
  | _, _, .step call next, a =>
      stepPre m call next a
        (Sum.casesOn (motive := fun x => StepPre m call next a x)
          (m (⟨call.1, a.1.select call.2⟩, a.2)) (fun _ => PUnit.unit)
          (fun y => Diagram.graphWitness (next y.1.1) (y.1.2.append a.1, y.2)))
  | _, Qs, .seq (K := K) first next, a =>
      ⟨Diagram.graphWitness first a, fun x _ =>
        Sum.casesOn
          (motive := fun x =>
            Spec.resumePre (fun (y : Exits.At (K :: Qs) X × R) =>
              Spec.exitPre (fun k => (Continuation.spec m.graph next).Pre (k, y.2)) y.1) x)
          x (fun _ => PUnit.unit)
          (fun y =>
            Exits.At.cases
              (motive := fun e =>
                Spec.exitPre (fun k => (Continuation.spec m.graph next).Pre (k, y.2)) e)
              (fun k => Continuation.graphWitness next (k, y.2)) (fun _ => PUnit.unit) y.1)⟩

def Continuation.graphWitness : {P : Boundary Ty} → {Qs : Exits Ty} →
    (k : Continuation S P Qs) → (a : P.At X × R) → (Continuation.spec m.graph k).Pre a
  | _, _, .copair each, a => Diagram.graphWitness (each a.1.1) (a.1.2, a.2)
  | _, _, .frame (K := K) kept args shared next, a =>
      ⟨Diagram.graphWitness shared (a.1.2.select (args a.1.1), a.2), fun x _ =>
        Sum.casesOn
          (motive := fun x =>
            Spec.resumePre (fun (y : Exits.At [K] X × R) =>
              Spec.exitPre (fun out =>
                (Continuation.spec m.graph next).Pre
                  (⟨Boundary.pair (kept a.1.1).1 out.1,
                    out.2.append (a.1.2.select (kept a.1.1).2)⟩, y.2)) y.1) x)
          x (fun _ => PUnit.unit)
          (fun y =>
            Exits.At.cases
              (motive := fun e =>
                Spec.exitPre (fun out =>
                  (Continuation.spec m.graph next).Pre
                    (⟨Boundary.pair (kept a.1.1).1 out.1,
                      out.2.append (a.1.2.select (kept a.1.1).2)⟩, y.2)) e)
              (fun _ => Continuation.graphWitness next _) (fun _ => PUnit.unit) y.1)⟩
  | _, _, .loop body, _ =>
      ⟨fun _ => PUnit, PUnit.unit, fun a' _ =>
        ⟨Continuation.graphWitness body a', fun _ _ => PUnit.unit⟩⟩

end

variable (L : R → Type c) (n : Nat) {Γ : List Ty} {Qs : Exits Ty}
  (call : (S.interface (Port Γ)).Shape)
  (next : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs) (a : All X Γ × R)

/-- For the graph of a machine, the bound of a step is the bound after the response of the
machine. -/
def stepWithin (h : StepPre m call next a (m (⟨call.1, a.1.select call.2⟩, a.2)))
    (w : Spec.resumeOn
      (fun (y : (S.output call.1).At X × R) p =>
        (next y.1.1).Within m.graph L n (y.1.2.append a.1, y.2) p)
      (m (⟨call.1, a.1.select call.2⟩, a.2)) h) :
    (Diagram.step call next).Within m.graph L n a (stepPre m call next a h) :=
  fun _ e =>
    Identity.ind
      (fun (x : E ⊕ ((S.output call.1).At X × R))
          (e : m (⟨call.1, a.1.select call.2⟩, a.2) ≡ x) =>
        Spec.resumeOn
          (fun (y : (S.output call.1).At X × R) p =>
            (next y.1.1).Within m.graph L n (y.1.2.append a.1, y.2) p)
          x (Identity.transport (StepPre m call next a) e h))
      w e

end GraphBound

/-- The result of an iteration that a result of the body of a loop gives. -/
def result {Ty : Type} {X : Ty → Type} {R E : Type} {K : Boundary Ty} {Qs : Exits Ty} :
    E ⊕ (Exits.At (K :: Qs) X × R) → (E ⊕ (Qs.At X × R)) ⊕ (K.At X × R)
  | .inl e => .inl (.inl e)
  | .inr m => Exits.At.elim (fun k => .inr (k, m.2)) (fun q => .inl (.inr (q, m.2))) m.1


end Draft
