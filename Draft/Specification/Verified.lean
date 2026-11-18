import Draft.Verified
import Draft.Specification.Soundness

/-! Verified diagrams.

A bound of a diagram over a witness of its precondition, for a number of unrollings and a
condition at the limit: each run over the witness reaches the limit of a loop only at a runtime
with the condition. A witness with its bound gives the evidence of the approximant, for a
computation at the limit that has evidence at each runtime with the condition.

A verified diagram, for a specification of its interface with a runtime, is a map into the
specification of the diagram: a witness of the precondition of the diagram, and the
postcondition at the result of each run over that witness.

The specification of a diagram with a bound has the witness of the diagram with its bound as
the witness of its precondition, and the runs of the diagram. The evidence of a diagram at an
input, for a condition at each result of a run, is the evidence of one call of that
specification. Its constructors have the forms of a diagram. An exit has its condition. A step
has a witness of the precondition of its call, the condition at each stop, and the evidence of
the diagram of each response, which receives the postcondition. A composite and a frame have a
condition at the boundary of the later part. A loop has an invariant that gives the condition
at the limit, or a family on the entrances with a count: the number of the unrollings that are
sufficient. The body goes from the family at one more to the family at the next entrance, no
entrance has the family at zero, and the entrance has the family at the number of unrollings.
The evidence at each input with a witness of a specification of the interface gives the
verified implementation of the approximant.

A specification of the calls with no runtime is the case of the unit runtime with no stop. The
evidence of a diagram for such a specification is the evidence at the unit runtime, and its
constructors have no runtime. The condition at the limit is one type, and the constructor of a
loop has the family with a count.

The map that forgets the bound gives the verified diagram. For a condition at the limit that
each runtime has, each witness of the precondition of a diagram has the bound, and a witness
with the condition at the result of each run gives the evidence again. -/

set_option autoImplicit false
set_option genInjectivity false

universe w z a b v w' z' c d

open Prelude Container

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}

variable (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E))

/-- A verified diagram, for a specification of its interface with a runtime: a map into the
specification of the diagram. At each input with a witness of the precondition of the
specification, it has a witness of the precondition of the diagram, and the postcondition of
the specification at the result of each run over that witness. -/
abbrev Diagram.Verified {Γ : List Ty} {Qs : Exits Ty}
    (q : DepPoly.{0, 0, w', z'} ((Diagram.interface X Γ Qs).runtime R E)) (d : Diagram S Γ Qs) :
    Type (max w (z + 1) w' z') :=
  q.Map (Diagram.spec r d)

/-- A diagram with its external contract, under the specification of its calls. -/
structure VerifiedDiagram {Γ : List Ty} {Qs : Exits Ty}
    (q : DepPoly.{0, 0, w', z'} ((Diagram.interface X Γ Qs).runtime R E)) where
  diagram : Diagram S Γ Qs
  verification : diagram.Verified r q

section Evidence

section AtExit

variable {K : Boundary Ty} {Qs : Exits Ty} {B : Type} {Mid : K.At X → Type v}
  {Tail : Qs.At X → Type v} {pre : K.At X → Type a} {post : (k : K.At X) → pre k → B → Type b}
  {tailPost : Qs.At X → B → Type b} {on : (k : K.At X) → pre k → Type c} {P : B → Type v}
  (witness : (k : K.At X) → Mid k → pre k)

/-- The witness at an exit, from the condition at the exit. -/
def Spec.exitWitness :
    (x : Exits.At (K :: Qs) X) → Exits.At.elim Mid Tail x → Spec.exitPre pre x :=
  Exits.At.cases (motive := fun x => Exits.At.elim Mid Tail x → Spec.exitPre pre x)
    witness (fun _ _ => PUnit.unit)

/-- The bound at an exit, over that witness. -/
def Spec.exitWithin (within : (k : K.At X) → (mid : Mid k) → on k (witness k mid)) :
    (x : Exits.At (K :: Qs) X) → (h : Exits.At.elim Mid Tail x) →
    Spec.exitOn pre on x (Spec.exitWitness witness x h) :=
  Exits.At.cases
    (motive := fun x => (h : Exits.At.elim Mid Tail x) →
      Spec.exitOn pre on x (Spec.exitWitness witness x h))
    within (fun _ _ => PUnit.unit)

/-- The condition at the result of a run after an exit, over that witness. -/
def Spec.exitResult
    (result : (k : K.At X) → (mid : Mid k) → (o : B) → post k (witness k mid) o → P o)
    (tailResult : (q : Qs.At X) → Tail q → (o : B) → tailPost q o → P o) :
    (x : Exits.At (K :: Qs) X) → (h : Exits.At.elim Mid Tail x) → (o : B) →
    Spec.atExit pre post tailPost x (Spec.exitWitness witness x h) o → P o :=
  Exits.At.cases
    (motive := fun x => (h : Exits.At.elim Mid Tail x) → (o : B) →
      Spec.atExit pre post tailPost x (Spec.exitWitness witness x h) o → P o)
    result tailResult

end AtExit

section Later

variable {K : Boundary Ty} {Qs : Exits Ty} {B : Type}

/-- The condition at a result of a part of a diagram that has a later part: a condition at a
stop, a condition at an exit to the later part, and a condition at each other exit. -/
def Spec.Later (Stop : E → Type v) (Mid : K.At X × R → Type v) (Tail : Qs.At X × R → Type v) :
    E ⊕ (Exits.At (K :: Qs) X × R) → Type v
  | .inl e => Stop e
  | .inr y => Exits.At.elim (fun k => Mid (k, y.2)) (fun q => Tail (q, y.2)) y.1

variable {Stop : E → Type v} {Mid : K.At X × R → Type v} {Tail : Qs.At X × R → Type v}
  {pre : K.At X × R → Type a} {post : (y : K.At X × R) → pre y → E ⊕ B → Type b}
  {tailPost : Qs.At X × R → E ⊕ B → Type b} {on : (y : K.At X × R) → pre y → Type c}
  {P : E ⊕ B → Type v} (witness : (y : K.At X × R) → Mid y → pre y)

/-- The witness of the later part at each result of the first part. -/
def Spec.laterWitness :
    (m : E ⊕ (Exits.At (K :: Qs) X × R)) → Spec.Later Stop Mid Tail m →
    Spec.resumePre
      (fun (y : Exits.At (K :: Qs) X × R) => Spec.exitPre (fun k => pre (k, y.2)) y.1) m
  | .inl _, _ => PUnit.unit
  | .inr y, h =>
      Spec.exitWitness (Mid := fun k => Mid (k, y.2)) (Tail := fun q => Tail (q, y.2))
        (pre := fun k => pre (k, y.2)) (fun k mid => witness (k, y.2) mid) y.1 h

/-- The bound of the later part at each result of the first part. -/
def Spec.laterWithin (within : (y : K.At X × R) → (mid : Mid y) → on y (witness y mid)) :
    (m : E ⊕ (Exits.At (K :: Qs) X × R)) → (h : Spec.Later Stop Mid Tail m) →
    Spec.resumeOn
      (fun (y : Exits.At (K :: Qs) X × R) p =>
        Spec.exitOn (fun k => pre (k, y.2)) (fun k p => on (k, y.2) p) y.1 p)
      m (Spec.laterWitness witness m h)
  | .inl _, _ => PUnit.unit
  | .inr y, h =>
      Spec.exitWithin (Mid := fun k => Mid (k, y.2)) (Tail := fun q => Tail (q, y.2))
        (pre := fun k => pre (k, y.2)) (on := fun k p => on (k, y.2) p)
        (fun k mid => witness (k, y.2) mid) (fun k mid => within (k, y.2) mid) y.1 h

/-- The condition at the result of each run of the later part, after a result of the first
part. -/
def Spec.laterResult (stopResult : (e : E) → Stop e → P (.inl e))
    (result : (y : K.At X × R) → (mid : Mid y) → (o : E ⊕ B) → post y (witness y mid) o → P o)
    (tailResult : (y : Qs.At X × R) → Tail y → (o : E ⊕ B) → tailPost y o → P o) :
    (m : E ⊕ (Exits.At (K :: Qs) X × R)) → (h : Spec.Later Stop Mid Tail m) → (o : E ⊕ B) →
    Spec.resumePost
      (fun (y : Exits.At (K :: Qs) X × R) p o =>
        Spec.atExit (fun k => pre (k, y.2)) (fun k p o => post (k, y.2) p o)
          (fun q o => tailPost (q, y.2) o) y.1 p o)
      m (Spec.laterWitness witness m h) o → P o
  | .inl e, h, _, run => Identity.transport P run.down (stopResult e h)
  | .inr y, h, o, run =>
      Spec.exitResult (Mid := fun k => Mid (k, y.2)) (Tail := fun q => Tail (q, y.2))
        (pre := fun k => pre (k, y.2)) (post := fun k p o => post (k, y.2) p o)
        (tailPost := fun q o => tailPost (q, y.2) o) (P := P)
        (fun k mid => witness (k, y.2) mid)
        (fun k mid o tail => result (k, y.2) mid o tail)
        (fun q t o tail => tailResult (q, y.2) t o tail) y.1 h o run

end Later

variable (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E)) (L : R → Type c) (n : Nat)

/-- The specification of a diagram with a bound, for a number of unrollings and a condition at
the limit: a witness of the precondition has a witness of the precondition of the diagram and
its bound. The runs are the runs of the diagram. -/
def Diagram.specWithin {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs) :
    Spec.{max w (z + 1) c, z} (All X Γ × R) (E ⊕ (Qs.At X × R)) :=
  ⟨fun x => (p : (Diagram.spec r d).Pre x) × d.Within r L n x p,
    fun x p o => (Diagram.spec r d).Post x p.1 o⟩

/-- The specification of a continuation with a bound. -/
def Continuation.specWithin {K : Boundary Ty} {Qs : Exits Ty} (k : Continuation S K Qs) :
    Spec.{max w (z + 1) c, z} (K.At X × R) (E ⊕ (Qs.At X × R)) :=
  ⟨fun x => (p : (Continuation.spec r k).Pre x) × k.Within r L n x p,
    fun x p o => (Continuation.spec r k).Post x p.1 o⟩

/-- The evidence of a diagram at an input, for a condition at each result of a run: the
evidence of one call of the specification of the diagram with the bound. -/
abbrev Diagram.Holds {Γ : List Ty} {Qs : Exits Ty} (P : E ⊕ (Qs.At X × R) → Type v)
    (d : Diagram S Γ Qs) (x : All X Γ × R) : Type _ :=
  FreeDep (d.specWithin r L n) P (Free.call (C := ⟨All X Γ × R, fun _ => E ⊕ (Qs.At X × R)⟩) x)

/-- The evidence of a continuation at an input, for a condition at each result of a run. -/
abbrev Continuation.Holds {K : Boundary Ty} {Qs : Exits Ty} (P : E ⊕ (Qs.At X × R) → Type v)
    (k : Continuation S K Qs) (x : K.At X × R) : Type _ :=
  FreeDep (k.specWithin r L n) P (Free.call (C := ⟨K.At X × R, fun _ => E ⊕ (Qs.At X × R)⟩) x)

section Constructors

variable {r L n} {Γ : List Ty} {Qs : Exits Ty} {P : E ⊕ (Qs.At X × R) → Type v}
  {env : All X Γ} {s : R}

/-- The evidence of an exit: its condition at the runtime. -/
def Diagram.Holds.exit (out : Qs.At (Port Γ)) (h : P (.inr (out.select env, s))) :
    (Diagram.exit (S := S) out).Holds r L n P (env, s) :=
  .request ⟨PUnit.unit, PUnit.unit⟩ fun _ run => .pure (Identity.transport P run.down h)

section Step

variable (call : (S.interface (Port Γ)).Shape)
  (rest : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs)
  (admit : r.Pre (⟨call.1, env.select call.2⟩, s))
  (stopped : (e : E) → r.Post (⟨call.1, env.select call.2⟩, s) admit (.inl e) → P (.inl e))
  (next : (y : (S.output call.1).At X × R) →
    r.Post (⟨call.1, env.select call.2⟩, s) admit (.inr y) →
    (rest y.1.1).Holds r L n P (y.1.2.append env, y.2))

/-- The witness after each response of the call of a step. -/
def Diagram.Holds.stepWitness :
    (x : E ⊕ ((S.output call.1).At X × R)) →
    r.Post (⟨call.1, env.select call.2⟩, s) admit x →
    Spec.resumePre (fun (y : (S.output call.1).At X × R) =>
      (Diagram.spec r (rest y.1.1)).Pre (y.1.2.append env, y.2)) x
  | .inl _, _ => PUnit.unit
  | .inr y, post => (next y post).parts.1.1

/-- The bound after each response of the call of a step. -/
def Diagram.Holds.stepWithin :
    (x : E ⊕ ((S.output call.1).At X × R)) →
    (post : r.Post (⟨call.1, env.select call.2⟩, s) admit x) →
    Spec.resumeOn
      (fun (y : (S.output call.1).At X × R) p =>
        (rest y.1.1).Within r L n (y.1.2.append env, y.2) p)
      x (Diagram.Holds.stepWitness call rest admit next x post)
  | .inl _, _ => PUnit.unit
  | .inr y, post => (next y post).parts.1.2

/-- The condition at the result of each run after a response of the call of a step. -/
def Diagram.Holds.stepResult :
    (x : E ⊕ ((S.output call.1).At X × R)) →
    (post : r.Post (⟨call.1, env.select call.2⟩, s) admit x) → (o : E ⊕ (Qs.At X × R)) →
    Spec.resumePost
      (fun (y : (S.output call.1).At X × R) p o =>
        (Diagram.spec r (rest y.1.1)).Post (y.1.2.append env, y.2) p o)
      x (Diagram.Holds.stepWitness call rest admit next x post) o → P o
  | .inl e, post, _, run => Identity.transport P run.down (stopped e post)
  | .inr y, post, o, run => ((next y post).parts.2 o run).result

/-- The evidence of a step: a witness of the precondition of the call at the runtime, the
condition at each stop, and the evidence of the diagram of each response from the next
runtime, which receives the postcondition. -/
def Diagram.Holds.step : (Diagram.step call rest).Holds r L n P (env, s) :=
  .request
    ⟨⟨admit, Diagram.Holds.stepWitness call rest admit next⟩,
      Diagram.Holds.stepWithin call rest admit next⟩
    fun o run =>
      .pure (Diagram.Holds.stepResult call rest admit stopped next run.1 run.2.1 o run.2.2)

end Step

/-- The evidence of a step for the graph of a machine, at a call where the machine gives a
response: the evidence of the diagram of that response from its next runtime. -/
def Diagram.Holds.stepResponse (m : Machine (S.interface X) R E)
    (call : (S.interface (Port Γ)).Shape)
    (rest : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs)
    {b : (S.output call.1).At X × R} (known : m (⟨call.1, env.select call.2⟩, s) ≡ .inr b)
    (next : (rest b.1.1).Holds m.graph L n P (b.1.2.append env, b.2)) :
    (Diagram.step call rest).Holds m.graph L n P (env, s) :=
  Diagram.Holds.step (r := m.graph) (env := env) (s := s) call rest PUnit.unit
    (fun _ post => (Identity.inrNotInl (known.symm.trans post)).elim)
    (fun _ post =>
      Identity.transport
        (fun (c : (S.output call.1).At X × R) =>
          (rest c.1.1).Holds m.graph L n P (c.1.2.append env, c.2))
        (Identity.inrInject (known.symm.trans post)) next)

/-- The evidence of a composite, for a condition at the boundary of the continuation with its
runtime: the evidence of the first diagram, with that condition at each exit to the boundary,
and the evidence of the continuation at each case with the condition. -/
def Diagram.Holds.seq {K : Boundary Ty} (Mid : K.At X × R → Type v)
    (first : Diagram S Γ (K :: Qs)) (next : Continuation S K Qs)
    (firstH : first.Holds r L n
      (Spec.Later (fun e => P (.inl e)) Mid (fun y => P (.inr y))) (env, s))
    (nextH : (y : K.At X × R) → Mid y → next.Holds r L n P y) :
    (Diagram.seq first next).Holds r L n P (env, s) :=
  .request
    ⟨⟨firstH.parts.1.1, fun m post =>
        Spec.laterWitness (Stop := fun e => P (.inl e)) (Mid := Mid) (Tail := fun y => P (.inr y))
          (pre := fun y => (Continuation.spec r next).Pre y)
          (fun y mid => (nextH y mid).parts.1.1) m (firstH.parts.2 m post).result⟩,
      firstH.parts.1.2, fun m post =>
        Spec.laterWithin (Stop := fun e => P (.inl e)) (Mid := Mid) (Tail := fun y => P (.inr y))
          (pre := fun y => (Continuation.spec r next).Pre y)
          (on := fun y p => next.Within r L n y p)
          (fun y mid => (nextH y mid).parts.1.1) (fun y mid => (nextH y mid).parts.1.2) m
          (firstH.parts.2 m post).result⟩
    fun o run =>
      .pure
        (Spec.laterResult (Stop := fun e => P (.inl e)) (Mid := Mid) (Tail := fun y => P (.inr y))
          (pre := fun y => (Continuation.spec r next).Pre y)
          (post := fun y p o => (Continuation.spec r next).Post y p o)
          (tailPost := fun y o => Spec.Result (Sum.inr y : E ⊕ (Qs.At X × R)) o) (P := P)
          (fun y mid => (nextH y mid).parts.1.1) (fun _ h => h)
          (fun y mid o tail => ((nextH y mid).parts.2 o tail).result)
          (fun _ h _ tail => Identity.transport P tail.down h)
          run.1 (firstH.parts.2 run.1 run.2.1).result o run.2.2)

end Constructors

section Constructors

variable {r L n} {K : Boundary Ty} {Qs : Exits Ty} {P : E ⊕ (Qs.At X × R) → Type v}

/-- The evidence of a copairing: the evidence of the diagram of the case. -/
def Continuation.Holds.copair {x : K.At X × R} (each : (c : K.Case) → Diagram S c.1 Qs)
    (h : (each x.1.1).Holds r L n P (x.1.2, x.2)) :
    (Continuation.copair each).Holds r L n P x :=
  .request h.parts.1 fun o run => .pure (h.parts.2 o run).result

/-- The evidence of a frame, for a condition at the exit of its diagram with its runtime: the
evidence of the diagram at the selected values, and the evidence of the continuation at the
case of the bypass, the kept values, and each exit with the condition. -/
def Continuation.Holds.frame {M B : Boundary Ty} {Δ : List Ty} {x : B.At X × R}
    (Mid : K.At X × R → Type v) (kept : (c : B.Case) → M.At (Port c.1))
    (args : (c : B.Case) → PortMap c.1 Δ) (shared : Diagram S Δ [K])
    (next : Continuation S (M.product K) Qs)
    (sharedH : shared.Holds r L n
      (Spec.Later (fun e => P (.inl e)) Mid (fun y => Exits.At.ofNil y.1))
      (x.1.2.select (args x.1.1), x.2))
    (nextH : (y : K.At X × R) → Mid y → next.Holds r L n P (After kept x y)) :
    (Continuation.frame kept args shared next).Holds r L n P x :=
  .request
    ⟨⟨sharedH.parts.1.1, fun m post =>
        Spec.laterWitness (Stop := fun e => P (.inl e)) (Mid := Mid)
          (Tail := fun y => Exits.At.ofNil y.1)
          (pre := fun y => (Continuation.spec r next).Pre (After kept x y))
          (fun y mid => (nextH y mid).parts.1.1) m (sharedH.parts.2 m post).result⟩,
      sharedH.parts.1.2, fun m post =>
        Spec.laterWithin (Stop := fun e => P (.inl e)) (Mid := Mid)
          (Tail := fun y => Exits.At.ofNil y.1)
          (pre := fun y => (Continuation.spec r next).Pre (After kept x y))
          (on := fun y p => next.Within r L n (After kept x y) p)
          (fun y mid => (nextH y mid).parts.1.1) (fun y mid => (nextH y mid).parts.1.2) m
          (sharedH.parts.2 m post).result⟩
    fun o run =>
      .pure
        (Spec.laterResult (Stop := fun e => P (.inl e)) (Mid := Mid)
          (Tail := fun y => Exits.At.ofNil y.1)
          (pre := fun y => (Continuation.spec r next).Pre (After kept x y))
          (post := fun y p o => (Continuation.spec r next).Post (After kept x y) p o)
          (tailPost := fun y _ => Exits.At.ofNil y.1) (P := P)
          (fun y mid => (nextH y mid).parts.1.1) (fun _ h => h)
          (fun y mid o tail => ((nextH y mid).parts.2 o tail).result)
          (fun y _ _ _ => Exits.At.ofNil y.1)
          run.1 (sharedH.parts.2 run.1 run.2.1).result o run.2.2)

end Constructors

section Loop

variable {r L n} {K : Boundary Ty} {Qs : Exits Ty} {P : E ⊕ (Qs.At X × R) → Type z}
  (Inv : K.At X × R → Type z) (body : Continuation S K (K :: Qs))
  (bodyH : (y : K.At X × R) → Inv y →
    body.Holds r L n (Spec.Later (fun e => P (.inl e)) Inv (fun y => P (.inr y))) y)
  (atLimit : (y : K.At X × R) → Inv y → L y.2)

/-- The body keeps the invariant. -/
def Continuation.Holds.loopKeeps : (iterSpec r body).Keeps Inv :=
  fun y i => ⟨(bodyH y i).parts.1.1, fun y' post =>
    ((bodyH y i).parts.2 (.inr (Exits.At.here y'.1, y'.2)) post).result⟩

/-- The bound of the loop for each number of unrollings: the invariant gives the condition at
the limit. -/
def Continuation.Holds.loopBound : (m : Nat) → (y : (x : K.At X × R) × Inv x) →
    Spec.Bound (iterSpec r body) (Continuation.Holds.loopKeeps Inv body bodyH)
      (fun x p => body.Within r L n x p) (fun x => L x.2) m y
  | 0, y => ⟨atLimit y.1 y.2⟩
  | m + 1, y =>
      ⟨(bodyH y.1 y.2).parts.1.2, fun x' post =>
        Continuation.Holds.loopBound m
          ⟨x', (Continuation.Holds.loopKeeps Inv body bodyH y.1 y.2).2 x' post⟩⟩

/-- The condition of the loop at the result of an iteration that ends the loop. -/
def Continuation.Holds.loopExit (y : (x : K.At X × R) × Inv x) :
    (o : E ⊕ (Qs.At X × R)) →
    (iterSpec r body).iterate (Continuation.Holds.loopKeeps Inv body bodyH) y (.inl o) → P o
  | .inl e, post => ((bodyH y.1 y.2).parts.2 (.inl e) post).result
  | .inr q, post => ((bodyH y.1 y.2).parts.2 (.inr (Exits.At.there K q.1, q.2)) post).result

/-- The evidence of a loop, for an invariant at the entrance: the evidence of the body at each
entrance with the invariant, with the invariant at each exit to the entrance. The invariant
gives the condition at the limit. -/
def Continuation.Holds.loop {x : K.At X × R} (start : Inv x) :
    (Continuation.loop body).Holds r L n P x :=
  .request
    ⟨⟨Inv, start, Continuation.Holds.loopKeeps Inv body bodyH⟩,
      Continuation.Holds.loopBound Inv body bodyH atLimit n ⟨x, start⟩⟩
    fun _ run =>
      .pure
        (Loop.elim (R := fun (_ : (x : K.At X × R) × Inv x) (o : E ⊕ (Qs.At X × R)) => P o)
          (fun y _ post => Continuation.Holds.loopExit Inv body bodyH y _ post)
          (fun _ _ _ _ rest => rest) run)

end Loop

section Counted

variable {r L n} {K : Boundary Ty} {Qs : Exits Ty} {P : E ⊕ (Qs.At X × R) → Type z}
  (V : Nat → K.At X × R → Type z) (body : Continuation S K (K :: Qs))
  (bodyH : (m : Nat) → (y : K.At X × R) → V (m + 1) y →
    body.Holds r L n (Spec.Later (fun e => P (.inl e)) (V m) (fun y => P (.inr y))) y)
  (never : (y : K.At X × R) → V 0 y → Empty)

/-- The body keeps the family with a count. The count at the next entrance is one less. -/
def Continuation.Holds.countedKeeps : (iterSpec r body).Keeps fun y => (m : Nat) × V m y
  | y, ⟨0, v⟩ => (never y v).elim
  | y, ⟨m + 1, v⟩ =>
      ⟨(bodyH m y v).parts.1.1, fun y' post =>
        ⟨m, ((bodyH m y v).parts.2 (.inr (Exits.At.here y'.1, y'.2)) post).result⟩⟩

/-- The bound of the loop from an entrance with a count, for that number of unrollings. -/
def Continuation.Holds.countedBound : (m : Nat) → (y : K.At X × R) → (v : V m y) →
    Spec.Bound (iterSpec r body) (Continuation.Holds.countedKeeps V body bodyH never)
      (fun x p => body.Within r L n x p) (fun x => L x.2) m ⟨y, ⟨m, v⟩⟩
  | 0, y, v => (never y v).elim
  | m + 1, y, v =>
      ⟨(bodyH m y v).parts.1.2, fun y' post =>
        Continuation.Holds.countedBound m y'
          ((bodyH m y v).parts.2 (.inr (Exits.At.here y'.1, y'.2)) post).result⟩

/-- The condition of the loop at the result of an iteration that ends the loop. -/
def Continuation.Holds.countedExit :
    (y : (x : K.At X × R) × ((m : Nat) × V m x)) → (o : E ⊕ (Qs.At X × R)) →
    (iterSpec r body).iterate (Continuation.Holds.countedKeeps V body bodyH never) y (.inl o) →
    P o
  | ⟨y, 0, v⟩, _, _ => (never y v).elim
  | ⟨y, m + 1, v⟩, .inl e, post => ((bodyH m y v).parts.2 (.inl e) post).result
  | ⟨y, m + 1, v⟩, .inr q, post =>
      ((bodyH m y v).parts.2 (.inr (Exits.At.there K q.1, q.2)) post).result

/-- The evidence of a loop, for a family on the entrances with a count: the number of the
unrollings that are sufficient. The body goes from the family at one more to the family at
each exit to the entrance. No entrance has the family at zero, and the entrance has the family
at the number of unrollings. The invariant is the family with its count. -/
def Continuation.Holds.loopCounted {x : K.At X × R} (start : V n x) :
    (Continuation.loop body).Holds r L n P x :=
  .request
    ⟨⟨fun y => (m : Nat) × V m y, ⟨n, start⟩,
        Continuation.Holds.countedKeeps V body bodyH never⟩,
      Continuation.Holds.countedBound V body bodyH never n x start⟩
    fun _ run =>
      .pure
        (Loop.elim
          (R := fun (_ : (x : K.At X × R) × ((m : Nat) × V m x)) (o : E ⊕ (Qs.At X × R)) => P o)
          (fun y _ post => Continuation.Holds.countedExit V body bodyH never y _ post)
          (fun _ _ _ _ rest => rest) run)

end Counted

section Approximant

variable {r L n}

/-- The evidence of a diagram at an input gives the evidence of the computation of each
approximant from that input, for a computation at the limit that has evidence at each runtime
with the condition at the limit. -/
def Diagram.Holds.evidence {Γ : List Ty} {Qs : Exits Ty} {P : E ⊕ (Qs.At X × R) → Type v}
    {d : Diagram S Γ Qs} {x : All X Γ × R} (h : d.Holds r L n P x)
    {stop : Free (S.interface X) (Qs.At X)}
    (limit : (s' : R) → L s' → FreeDep r P (stop.thread s')) :
    FreeDep r P ((d.impl stop n).thread x) :=
  Diagram.evidenceAt r L limit n d x.1 x.2 h.parts.1.1 h.parts.1.2 .pure fun m run =>
    Sum.casesOn (motive := fun m => P m → FreeDep r P (Free.resume .pure m))
      m (fun _ p => .pure p) (fun _ p => .pure p) (h.parts.2 m run).result

/-- The evidence of a diagram at each input with a witness of the precondition of a
specification of its interface, for the postcondition of that witness, gives the verified
implementation of each approximant. -/
def Diagram.Holds.impl {Γ : List Ty} {Qs : Exits Ty}
    {q : DepPoly.{0, 0, w', z'} ((Diagram.interface X Γ Qs).runtime R E)} {d : Diagram S Γ Qs}
    (h : (x : All X Γ × R) → (pre : q.Pre x) → d.Holds r L n (q.Post x pre) x)
    {stop : Free (S.interface X) (Qs.At X)}
    (limit : (x : All X Γ × R) → (pre : q.Pre x) → (s' : R) → L s' →
      FreeDep r (q.Post x pre) (stop.thread s')) :
    ImplDep q r (d.impl stop n).thread :=
  fun x pre => Diagram.Holds.evidence (h x pre) (limit x pre)

/-- The verified implementation of one approximant. A bound is indexed by the admission
carried by the diagram. Its cutoff obligation is needed only at a reachable limit. -/
def VerifiedDiagram.implement {Γ : List Ty} {Qs : Exits Ty}
    {q : DepPoly.{0, 0, w', z'} ((Diagram.interface X Γ Qs).runtime R E)}
    (d : VerifiedDiagram r q) (stop : Free (S.interface X) (Qs.At X)) (n : Nat)
    {L : R → Type c}
    (bound : ∀ x pre, d.diagram.Within r L n x (d.verification x pre).1)
    (cutoff : ∀ x pre s, L s → FreeDep r (q.Post x pre) (stop.thread s)) : VerifiedImpl q r :=
  ⟨(d.diagram.impl stop n).thread,
    Diagram.Holds.impl (d := d.diagram) (n := n) (fun x pre =>
      let v := d.verification x pre
      .request ⟨v.1, bound x pre⟩ fun o run => .pure (v.2 o run)) cutoff⟩

end Approximant

end Evidence

section Still

/-- The evidence of a diagram at the values of its context, for a specification of its calls
with no runtime, a condition at the limit, and a condition at each exit: the evidence at the
unit runtime. -/
abbrev Diagram.HoldsStill (r₀ : DepPoly.{0, 0, w, z} (S.interface X)) (L : Type c) (n : Nat)
    {Γ : List Ty} {Qs : Exits Ty} (P : Qs.At X → Type v) (d : Diagram S Γ Qs) (env : All X Γ) :
    Type _ :=
  d.Holds r₀.still (fun _ => L) n (Still P) (env, PUnit.unit)

/-- The evidence of a continuation at a case with its values, with no runtime. -/
abbrev Continuation.HoldsStill (r₀ : DepPoly.{0, 0, w, z} (S.interface X)) (L : Type c) (n : Nat)
    {K : Boundary Ty} {Qs : Exits Ty} (P : Qs.At X → Type v) (k : Continuation S K Qs)
    (x : K.At X) : Type _ :=
  k.Holds r₀.still (fun _ => L) n (Still P) (x, PUnit.unit)

variable {r₀ : DepPoly.{0, 0, w, z} (S.interface X)} {L : Type c} {n : Nat}

/-- The condition at a result of a part with a later part, from the condition at each exit. -/
def Still.later {K : Boundary Ty} {Qs : Exits Ty} (Mid : K.At X → Type v) (P : Qs.At X → Type v) :
    (m : Empty ⊕ (Exits.At (K :: Qs) X × PUnit.{1})) → Still (Exits.At.elim Mid P) m →
    Spec.Later (fun e => Still P (.inl e)) (fun (y : K.At X × PUnit.{1}) => Mid y.1)
      (fun y => Still P (.inr y)) m
  | .inl e, _ => nomatch e
  | .inr _, h => h

/-- The condition at a result of the diagram of a frame, from the condition at its exit. -/
def Still.only {K : Boundary Ty} {Qs : Exits Ty} (Mid : K.At X → Type v) (P : Qs.At X → Type v) :
    (m : Empty ⊕ (Exits.At [K] X × PUnit.{1})) → Still (Exits.At.only Mid) m →
    Spec.Later (fun e => Still P (.inl e)) (fun (y : K.At X × PUnit.{1}) => Mid y.1)
      (fun y => Exits.At.ofNil y.1) m
  | .inl e, _ => nomatch e
  | .inr _, h => h

section Constructors

variable {Γ : List Ty} {Qs : Exits Ty} {P : Qs.At X → Type v} {env : All X Γ}

/-- The evidence of an exit: its condition. -/
def Diagram.HoldsStill.exit (out : Qs.At (Port Γ)) (h : P (out.select env)) :
    (Diagram.exit (S := S) out).HoldsStill r₀ L n P env :=
  Diagram.Holds.exit out h

/-- The evidence of a step: a witness of the precondition of the operation, and the evidence of
the diagram of each response, which receives the postcondition of the response. -/
def Diagram.HoldsStill.step (call : (S.interface (Port Γ)).Shape)
    (rest : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs)
    (admit : r₀.Pre ⟨call.1, env.select call.2⟩)
    (next : (resp : (S.output call.1).At X) → r₀.Post ⟨call.1, env.select call.2⟩ admit resp →
      (rest resp.1).HoldsStill r₀ L n P (resp.2.append env)) :
    (Diagram.step call rest).HoldsStill r₀ L n P env :=
  Diagram.Holds.step (r := r₀.still) call rest admit (fun e _ => nomatch e)
    (fun y post => next y.1 post)

/-- The evidence of a composite, for a condition at the boundary of the continuation. -/
def Diagram.HoldsStill.seq {K : Boundary Ty} (Mid : K.At X → Type v)
    (first : Diagram S Γ (K :: Qs)) (next : Continuation S K Qs)
    (firstH : first.HoldsStill r₀ L n (Exits.At.elim Mid P) env)
    (nextH : (k : K.At X) → Mid k → next.HoldsStill r₀ L n P k) :
    (Diagram.seq first next).HoldsStill r₀ L n P env :=
  Diagram.Holds.seq (fun y => Mid y.1) first next (FreeDep.mapQ (Still.later Mid P) _ firstH)
    (fun y mid => nextH y.1 mid)

end Constructors

section Constructors

variable {K : Boundary Ty} {Qs : Exits Ty}

/-- The evidence of a copairing: the evidence of the diagram of the case. -/
def Continuation.HoldsStill.copair {P : Qs.At X → Type v} {x : K.At X}
    (each : (c : K.Case) → Diagram S c.1 Qs) (h : (each x.1).HoldsStill r₀ L n P x.2) :
    (Continuation.copair each).HoldsStill r₀ L n P x :=
  Continuation.Holds.copair each h

/-- The evidence of a frame, for a condition at the exit of its diagram. -/
def Continuation.HoldsStill.frame {P : Qs.At X → Type v} {M B : Boundary Ty} {Δ : List Ty}
    {x : B.At X} (Mid : K.At X → Type v) (kept : (c : B.Case) → M.At (Port c.1))
    (args : (c : B.Case) → PortMap c.1 Δ) (shared : Diagram S Δ [K])
    (next : Continuation S (M.product K) Qs)
    (sharedH : shared.HoldsStill r₀ L n (Exits.At.only Mid) (x.2.select (args x.1)))
    (nextH : (out : K.At X) → Mid out →
      next.HoldsStill r₀ L n P
        ⟨Boundary.pair (kept x.1).1 out.1, out.2.append (x.2.select (kept x.1).2)⟩) :
    (Continuation.frame kept args shared next).HoldsStill r₀ L n P x :=
  Continuation.Holds.frame (fun y => Mid y.1) kept args shared next
    (FreeDep.mapQ (Still.only Mid P) _ sharedH) (fun y mid => nextH y.1 mid)

/-- The evidence of a loop, for a family at the entrance with a count: the number of the
unrollings that are sufficient. The body goes from the family at one more to the family at the
next entrance, and no entrance has the family at zero. -/
def Continuation.HoldsStill.loopCounted {P : Qs.At X → Type z} {x : K.At X}
    (V : Nat → K.At X → Type z) (body : Continuation S K (K :: Qs))
    (bodyH : (m : Nat) → (k : K.At X) → V (m + 1) k →
      body.HoldsStill r₀ L n (Exits.At.elim (V m) P) k)
    (never : (k : K.At X) → V 0 k → Empty) (start : V n x) :
    (Continuation.loop body).HoldsStill r₀ L n P x :=
  Continuation.Holds.loopCounted (fun m y => V m y.1) body
    (fun m y v => FreeDep.mapQ (Still.later (V m) P) _ (bodyH m y.1 v)) (fun y v => never y.1 v)
    start

end Constructors

/-- The evidence of a diagram at each context with a witness of the precondition of a
specification of its interface, for the postcondition of that witness, gives the verified
implementation of each approximant, for a computation at the limit that has evidence of each
postcondition with the condition at the limit. -/
def Diagram.HoldsStill.impl {Γ : List Ty} {Qs : Exits Ty}
    {q₀ : DepPoly.{0, 0, w', z'} (Diagram.interface X Γ Qs)} {d : Diagram S Γ Qs}
    (h : (env : All X Γ) → (pre : q₀.Pre env) → d.HoldsStill r₀ L n (q₀.Post env pre) env)
    {stop : Free (S.interface X) (Qs.At X)}
    (limit : (env : All X Γ) → (pre : q₀.Pre env) → L → FreeDep r₀ (q₀.Post env pre) stop) :
    ImplDep q₀ r₀ (d.impl stop n) :=
  fun env pre =>
    FreeDep.ofStill _
      (Diagram.Holds.impl (q := q₀.still) (fun x pre => h x.1 pre)
        (fun x pre _ l => FreeDep.toStill stop (limit x.1 pre l)) (env, .unit) pre)

end Still

section Forget

variable {r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E)} {L : R → Type c} {n : Nat}

/-- The verified diagram of the evidence with a bound: the map that forgets the bound. -/
def Diagram.Holds.verified {Γ : List Ty} {Qs : Exits Ty}
    {q : DepPoly.{0, 0, w', z'} ((Diagram.interface X Γ Qs).runtime R E)} {d : Diagram S Γ Qs}
    (h : (x : All X Γ × R) → (pre : q.Pre x) → d.Holds r L n (q.Post x pre) x) :
    d.Verified r q :=
  (ImplDep.toMap (P := q) (Q := d.specWithin r L n) h).trans
    (fun _ p => ⟨p.1, fun _ run => run⟩)

/-- The evidence of a continuation with a bound, from a witness of its precondition and the
condition at the result of each run, for a condition at the limit that each runtime has. -/
def Continuation.Holds.ofAlways (always : (s : R) → L s) {K : Boundary Ty} {Qs : Exits Ty}
    {P : E ⊕ (Qs.At X × R) → Type v} {k : Continuation S K Qs} {x : K.At X × R}
    (p : (Continuation.spec r k).Pre x)
    (result : (o : E ⊕ (Qs.At X × R)) → (Continuation.spec r k).Post x p o → P o) :
    k.Holds r L n P x :=
  .request ⟨p, Continuation.withinAlways r L n always k x p⟩ fun o run => .pure (result o run)

end Forget

section Uncopair

variable {r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E)} {L : R → Type c} {n : Nat}
  {K : Boundary Ty} {Qs : Exits Ty}

/-- The evidence of the diagram of a case, from the evidence of a copairing. -/
def Continuation.Holds.uncopair (each : (c : K.Case) → Diagram S c.1 Qs)
    {P : E ⊕ (Qs.At X × R) → Type v} {x : K.At X × R}
    (h : (Continuation.copair each).Holds r L n P x) :
    (each x.1.1).Holds r L n P (x.1.2, x.2) :=
  .request h.parts.1 fun o run => .pure (h.parts.2 o run).result

end Uncopair

end Draft
