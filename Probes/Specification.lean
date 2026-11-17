import Draft.Checks.Countdown
import Draft.Runtime

set_option autoImplicit false
set_option genInjectivity false

open Prelude Container

/-! Probe: the specification of a diagram, from a specification of its calls with a runtime.

A specification of a computation has a precondition at each input, and the runs to each result
over a witness of the precondition. A response of a call is a response with the next runtime,
or a stop, and a result of a run is an exit with a runtime, or a stop. A witness of the
precondition of a diagram has a witness of the precondition of each call that a run can make.
The precondition of a loop is an invariant: a family on the entrances that the body keeps. The
runs of a loop are the loop of `Prelude.Relation` on the entrances with the family. One
iteration has the runs of the body at the result that the next entrance, the exit, or the stop
names.

A witness of the precondition of a diagram gives the evidence of the computation of the diagram
with each number of unrollings, for evidence of the rest at each result of a run. That is
soundness: the condition at the result of a run of the computation along the evidence is a run
of the diagram. Completeness is the converse: a run of the diagram, and then a run of the rest,
is a run of the computation along its evidence, from a threshold of the number of unrollings.

A verified diagram, for a specification of its interface with a runtime, is a map into the
specification of the diagram: a witness of the precondition of the diagram, and the
postcondition at the result of each run. It has the lift of a diagram with a runtime for each
number of unrollings. A bound is second evidence: each run over the witness reaches the limit
of a loop only at a runtime with a given condition. With the empty condition, the lift needs no
evidence for the computation at the limit.

The two exit equations hold for the specification. A witness for an exit to the boundary of a
continuation, and then the continuation, gives a witness for the continuation at the case of
the exit, and the converse. Over each witness, the runs of the composite are the runs of the
continuation, as an equivalence with its two round trips. The runs of an exit past a
continuation, and then the continuation, are the runs of that exit. The runs of a loop over a
witness are the loop of its iterations, by computation.

A cartesian map of specifications gives a witness of the second precondition from a witness
of the first, and an equivalence of the runs over the second witness and the runs over the
first, with its two round trips. A rule set holds for a specification of the calls when each
rule has a cartesian map between the specifications of its two sides, in each direction. A
derivation in such a rule set has these maps, by a recursion on the derivation, and a verified
diagram moves along them. The second exit equation is a rule with these maps, for each
specification of the calls.

A specification of the calls with no runtime is the case of the unit runtime with no stop. A
verified diagram at the unit runtime gives the verified implementation of each approximant with
no runtime.

In the form of the Prelude, the evidence of a diagram at an input, for a condition at each
result, is the evidence of one call of the interface of the diagram, for the specification of
the diagram. A verified diagram is the verified implementation with one call, from a
specification of the interface of the diagram to the specification of the diagram. The
constructors of that evidence have the forms of a diagram: an exit, a step, a copairing, and a
loop with an invariant.

The checks are on the countdown loop, for an arbitrary value and an arbitrary runtime: the
round trip of a run through the computation with a number of unrollings, the same for a loop
in a loop, the run that the result of the function meaning on a machine has, for an arbitrary
computation at the limit, the two exit equations and the laws of the loop at a run of the
specification, with their round trips, the equivalence of the runs over the witness that a
derivation gives, with its two round trips, the same for a derivation with the second exit
equation between two different loops, and the
condition at the result of a run over the witness that the constructors give, through the
invariant of each iteration. -/

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}

abbrev Spec (A B : Type) : Type 2 := DepPoly.{0, 0, 1, 0} ⟨A, fun _ => B⟩

def Spec.resumePre {M : Type} (P : M → Type 1) : E ⊕ M → Type 1
  | .inl _ => PUnit
  | .inr m => P m

def Spec.resumePost {M B : Type} {P : M → Type 1} (G : (m : M) → P m → E ⊕ B → Type) :
    (x : E ⊕ M) → Spec.resumePre P x → E ⊕ B → Type
  | .inl e, _, o => (Sum.inl e : E ⊕ B) ≡ o
  | .inr m, p, o => G m p o

def Exits.At.cases.{w} {K : Boundary Ty} {Qs : Exits Ty}
    {motive : Exits.At (K :: Qs) X → Type w}
    (head : (k : K.At X) → motive (Exits.At.here k))
    (tail : (q : Qs.At X) → motive (Exits.At.there K q)) (r : Exits.At (K :: Qs) X) : motive r :=
  Elem.consCases
    (motive := fun (Q : Boundary Ty) (i : Elem Q (K :: Qs)) => (q : Q.At X) → motive ⟨Q, i, q⟩)
    r.2.1 head (fun Q j q => tail ⟨Q, j, q⟩) r.2.2

abbrev Spec.exitPre {K : Boundary Ty} {Qs : Exits Ty} (headPre : K.At X → Type 1) :
    Exits.At (K :: Qs) X → Type 1 :=
  Exits.At.elim headPre fun _ => PUnit

def Spec.atExit {K : Boundary Ty} {Qs : Exits Ty} {B : Type} (headPre : K.At X → Type 1)
    (headPost : (k : K.At X) → headPre k → B → Type) (tailPost : Qs.At X → B → Type) :
    (r : Exits.At (K :: Qs) X) → Spec.exitPre headPre r → B → Type :=
  Exits.At.cases (motive := fun r => Spec.exitPre headPre r → B → Type)
    headPost (fun q _ o => tailPost q o)

/-- The result of the body of a loop that a result of an iteration names: a stop, an exit of
the loop, or the next entrance. -/
def unresult {K : Boundary Ty} {Qs : Exits Ty} :
    (E ⊕ (Qs.At X × R)) ⊕ (K.At X × R) → E ⊕ (Exits.At (K :: Qs) X × R)
  | .inl (.inl e) => .inl e
  | .inl (.inr y) => .inr (Exits.At.there K y.1, y.2)
  | .inr y => .inr (Exits.At.here y.1, y.2)

abbrev Spec.Keeps {A B : Type} (F : Spec A (B ⊕ A)) (Inv : A → Type) : Type 1 :=
  (a : A) → Inv a → (p : F.Pre a) × ((a' : A) → F.Post a p (.inr a') → Inv a')

def Spec.iterate {A B : Type} (F : Spec A (B ⊕ A)) {Inv : A → Type} (keeps : F.Keeps Inv) :
    Rel.{0, 0, 0} ((a : A) × Inv a) (B ⊕ ((a : A) × Inv a))
  | x, .inl b => F.Post x.1 (keeps x.1 x.2).1 (.inl b)
  | x, .inr y => (post : F.Post x.1 (keeps x.1 x.2).1 (.inr y.1)) × ((keeps x.1 x.2).2 y.1 post ≡ y.2)

def Spec.loopInv {A B : Type} (F : Spec A (B ⊕ A)) : Spec A B :=
  ⟨fun a => (Inv : A → Type) × (Inv a × F.Keeps Inv), fun a w b => Loop (F.iterate w.2.2) ⟨a, w.2.1⟩ b⟩

variable (r : DepPoly.{0, 0, 0, 0} ((S.interface X).runtime R E))

mutual

def Diagram.spec : {Γ : List Ty} → {Qs : Exits Ty} → Diagram S Γ Qs →
    Spec (All X Γ × R) (E ⊕ (Qs.At X × R))
  | _, Qs, .exit out =>
      ⟨fun _ => PUnit, fun a _ o => (Sum.inr (out.select a.1, a.2) : E ⊕ (Qs.At X × R)) ≡ o⟩
  | _, _, .step call next =>
      ⟨fun a =>
        (p : r.Pre (⟨call.1, a.1.select call.2⟩, a.2)) ×
          ((x : E ⊕ ((S.output call.1).At X × R)) → r.Post (⟨call.1, a.1.select call.2⟩, a.2) p x →
            Spec.resumePre (fun (y : (S.output call.1).At X × R) =>
              ((next y.1.1).spec).Pre (y.1.2.append a.1, y.2)) x),
        fun a pre o =>
          (x : E ⊕ ((S.output call.1).At X × R)) ×
            (post : r.Post (⟨call.1, a.1.select call.2⟩, a.2) pre.1 x) ×
              Spec.resumePost
                (fun (y : (S.output call.1).At X × R) p o =>
                  ((next y.1.1).spec).Post (y.1.2.append a.1, y.2) p o) x (pre.2 x post) o⟩
  | _, Qs, .seq (K := K) first next =>
      ⟨fun a =>
        (p : (first.spec).Pre a) ×
          ((m : E ⊕ (Exits.At (K :: Qs) X × R)) → (first.spec).Post a p m →
            Spec.resumePre (fun (y : Exits.At (K :: Qs) X × R) =>
              Spec.exitPre (fun k => (next.spec).Pre (k, y.2)) y.1) m),
        fun a pre o =>
          (m : E ⊕ (Exits.At (K :: Qs) X × R)) × (post : (first.spec).Post a pre.1 m) ×
            Spec.resumePost
              (fun (y : Exits.At (K :: Qs) X × R) p o =>
                Spec.atExit (fun k => (next.spec).Pre (k, y.2))
                  (fun k p o => (next.spec).Post (k, y.2) p o)
                  (fun q o => (Sum.inr (q, y.2) : E ⊕ (Qs.At X × R)) ≡ o) y.1 p o)
              m (pre.2 m post) o⟩

def Continuation.spec : {P : Boundary Ty} → {Qs : Exits Ty} → Continuation S P Qs →
    Spec (P.At X × R) (E ⊕ (Qs.At X × R))
  | _, _, .copair each =>
      ⟨fun a => ((each a.1.1).spec).Pre (a.1.2, a.2),
        fun a p o => ((each a.1.1).spec).Post (a.1.2, a.2) p o⟩
  | _, Qs, .frame (K := K) kept args shared next =>
      ⟨fun a =>
        (p : (shared.spec).Pre (a.1.2.select (args a.1.1), a.2)) ×
          ((m : E ⊕ (Exits.At [K] X × R)) →
            (shared.spec).Post (a.1.2.select (args a.1.1), a.2) p m →
            Spec.resumePre (fun (y : Exits.At [K] X × R) =>
              Spec.exitPre (fun out =>
                (next.spec).Pre
                  (⟨Boundary.pair (kept a.1.1).1 out.1,
                    out.2.append (a.1.2.select (kept a.1.1).2)⟩, y.2)) y.1) m),
        fun a pre o =>
          (m : E ⊕ (Exits.At [K] X × R)) ×
            (post : (shared.spec).Post (a.1.2.select (args a.1.1), a.2) pre.1 m) ×
              Spec.resumePost
                (fun (y : Exits.At [K] X × R) p o =>
                  Spec.atExit
                    (fun out =>
                      (next.spec).Pre
                        (⟨Boundary.pair (kept a.1.1).1 out.1,
                          out.2.append (a.1.2.select (kept a.1.1).2)⟩, y.2))
                    (fun out p o =>
                      (next.spec).Post
                        (⟨Boundary.pair (kept a.1.1).1 out.1,
                          out.2.append (a.1.2.select (kept a.1.1).2)⟩, y.2) p o)
                    (fun q _ => Exits.At.ofNil q) y.1 p o)
                m (pre.2 m post) o⟩
  | _, Qs, .loop (K := K) body =>
      Spec.loopInv (A := K.At X × R) (B := E ⊕ (Qs.At X × R))
        ⟨fun a => (body.spec).Pre a, fun a p t => (body.spec).Post a p (unresult t)⟩

end

/-- The specification of one iteration of a loop. -/
abbrev iterSpec {K : Boundary Ty} {Qs : Exits Ty} (body : Continuation S K (K :: Qs)) :
    Spec (K.At X × R) ((E ⊕ (Qs.At X × R)) ⊕ (K.At X × R)) :=
  ⟨fun a => (body.spec r).Pre a, fun a p t => (body.spec r).Post a p (unresult t)⟩

/-! The evidence of an approximant, from a witness of the precondition. -/

section Evidence

variable {α : Type} {F : E ⊕ (α × R) → Type} {stop : Free (S.interface X) α}
  (limit : (s₀ : R) → FreeDep r F (stop.thread s₀)) (n : Nat)

/-- For a witness of the precondition: the computation of the diagram with a number of
unrollings has evidence, when the rest has evidence at each result of a run over the
witness. -/
abbrev Diagram.Evidence (F : E ⊕ (α × R) → Type) (stop : Free (S.interface X) α)
    {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs)
    (env : All X Γ) (s : R) (pre : (d.spec r).Pre (env, s)) : Type :=
  (cont : Qs.At X → Free (S.interface X) α) →
    ((m : E ⊕ (Qs.At X × R)) → (d.spec r).Post (env, s) pre m →
      FreeDep r F (Free.resume cont m)) →
    FreeDep r F ((d.run stop n env cont).thread s)

abbrev Continuation.Evidence (F : E ⊕ (α × R) → Type) (stop : Free (S.interface X) α)
    {P : Boundary Ty} {Qs : Exits Ty}
    (k : Continuation S P Qs) (a : P.At X) (s : R) (pre : (k.spec r).Pre (a, s)) : Type :=
  (cont : Qs.At X → Free (S.interface X) α) →
    ((m : E ⊕ (Qs.At X × R)) → (k.spec r).Post (a, s) pre m →
      FreeDep r F (Free.resume cont m)) →
    FreeDep r F ((k.run stop n a cont).thread s)

/-- The evidence of the rest of the first diagram of a composite, at each of its results. -/
def seqRest {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (first : Diagram S Γ (K :: Qs))
    (next : Continuation S K Qs) (env : All X Γ) (s : R)
    (pre : ((Diagram.seq first next).spec r).Pre (env, s))
    (nextEv : (k : K.At X) → (s₁ : R) → (p : (next.spec r).Pre (k, s₁)) →
      next.Evidence r n F stop k s₁ p)
    (cont : Qs.At X → Free (S.interface X) α)
    (rest : (m : E ⊕ (Qs.At X × R)) → ((Diagram.seq first next).spec r).Post (env, s) pre m →
      FreeDep r F (Free.resume cont m)) :
    (m₁ : E ⊕ (Exits.At (K :: Qs) X × R)) → (first.spec r).Post (env, s) pre.1 m₁ →
    FreeDep r F (Free.resume (Exits.At.elim (fun k => next.run stop n k cont) cont) m₁)
  | .inl e, run₁ => rest (.inl e) ⟨.inl e, run₁, .refl⟩
  | .inr y, run₁ =>
      Exits.At.cases
        (motive := fun x => (first.spec r).Post (env, s) pre.1 (.inr (x, y.2)) →
          FreeDep r F ((Exits.At.elim (fun k => next.run stop n k cont) cont x).thread y.2))
        (fun k run₁ =>
          nextEv k y.2 (pre.2 (.inr (Exits.At.here k, y.2)) run₁) cont
            (fun m tail => rest m ⟨.inr (Exits.At.here k, y.2), run₁, tail⟩))
        (fun q run₁ => rest (.inr (q, y.2)) ⟨.inr (Exits.At.there K q, y.2), run₁, .refl⟩)
        y.1 run₁

/-- The evidence of the rest of the diagram of a frame, at each of its results. -/
def frameRest {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
    (kept : (c : P.Case) → M.At (Port c.1)) (args : (c : P.Case) → PortMap c.1 Δ)
    (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs) (a : P.At X) (s : R)
    (pre : ((Continuation.frame kept args shared next).spec r).Pre (a, s))
    (nextEv : (k : (M.product K).At X) → (s₁ : R) → (p : (next.spec r).Pre (k, s₁)) →
      next.Evidence r n F stop k s₁ p)
    (cont : Qs.At X → Free (S.interface X) α)
    (rest : (m : E ⊕ (Qs.At X × R)) →
      ((Continuation.frame kept args shared next).spec r).Post (a, s) pre m →
      FreeDep r F (Free.resume cont m)) :
    (m₁ : E ⊕ (Exits.At [K] X × R)) →
    (shared.spec r).Post (a.2.select (args a.1), s) pre.1 m₁ →
    FreeDep r F
      (Free.resume
        (Exits.At.only fun out =>
          next.run stop n
            ⟨Boundary.pair (kept a.1).1 out.1, out.2.append (a.2.select (kept a.1).2)⟩ cont)
        m₁)
  | .inl e, run₁ => rest (.inl e) ⟨.inl e, run₁, .refl⟩
  | .inr y, run₁ =>
      Exits.At.cases
        (motive := fun x =>
          (shared.spec r).Post (a.2.select (args a.1), s) pre.1 (.inr (x, y.2)) →
            FreeDep r F
              ((Exits.At.only (fun out =>
                next.run stop n
                  ⟨Boundary.pair (kept a.1).1 out.1,
                    out.2.append (a.2.select (kept a.1).2)⟩ cont) x).thread y.2))
        (fun out run₁ =>
          nextEv _ y.2 (pre.2 (.inr (Exits.At.here out, y.2)) run₁) cont
            (fun m tail => rest m ⟨.inr (Exits.At.here out, y.2), run₁, tail⟩))
        (fun q _ => Exits.At.ofNil q) y.1 run₁

section Loop

variable {K : Boundary Ty} {Qs : Exits Ty} (body : Continuation S K (K :: Qs))
  {Inv : K.At X × R → Type} (keeps : (iterSpec r body).Keeps Inv)
  (cont : Qs.At X → Free (S.interface X) α)

/-- The evidence of the rest of the body of a loop, at each of its results: the stop, the
unrollings that remain at the next entrance, or the rest of the loop at an exit. -/
def loopRest (j : Nat) (y : (a : K.At X × R) × Inv a)
    (again : (y' : (a : K.At X × R) × Inv a) →
      ((m : E ⊕ (Qs.At X × R)) → Loop ((iterSpec r body).iterate keeps) y' m →
        FreeDep r F (Free.resume cont m)) →
      FreeDep r F
        ((Continuation.unrolled stop (body.run stop n) j y'.1.1 cont).thread y'.1.2))
    (rest : (m : E ⊕ (Qs.At X × R)) → Loop ((iterSpec r body).iterate keeps) y m →
      FreeDep r F (Free.resume cont m)) :
    (m' : E ⊕ (Exits.At (K :: Qs) X × R)) → (body.spec r).Post y.1 (keeps y.1 y.2).1 m' →
    FreeDep r F
      (Free.resume
        (Exits.At.elim (fun k' => Continuation.unrolled stop (body.run stop n) j k' cont) cont)
        m')
  | .inl e, bodyRun => rest (.inl e) (.exit bodyRun)
  | .inr b, bodyRun =>
      Exits.At.cases
        (motive := fun x => (body.spec r).Post y.1 (keeps y.1 y.2).1 (.inr (x, b.2)) →
          FreeDep r F
            ((Exits.At.elim
              (fun k' => Continuation.unrolled stop (body.run stop n) j k' cont) cont
              x).thread b.2))
        (fun k' bodyRun =>
          again ⟨(k', b.2), (keeps y.1 y.2).2 (k', b.2) bodyRun⟩
            (fun m l =>
              rest m
                (Loop.next (F := (iterSpec r body).iterate keeps)
                  (a' := (⟨(k', b.2), (keeps y.1 y.2).2 (k', b.2) bodyRun⟩ :
                    (a : K.At X × R) × Inv a))
                  ⟨bodyRun, .refl⟩ l)))
        (fun q bodyRun => rest (.inr (q, b.2)) (.exit bodyRun))
        b.1 bodyRun

/-- The evidence of the unrollings of a loop, from the evidence of its body. -/
def loopEvidence
    (bodyEv : (a : K.At X) → (s₁ : R) → (p : (body.spec r).Pre (a, s₁)) →
      body.Evidence r n F stop a s₁ p) :
    (j : Nat) → (y : (a : K.At X × R) × Inv a) →
    ((m : E ⊕ (Qs.At X × R)) → Loop ((iterSpec r body).iterate keeps) y m →
      FreeDep r F (Free.resume cont m)) →
    FreeDep r F ((Continuation.unrolled stop (body.run stop n) j y.1.1 cont).thread y.1.2)
  | 0, y, _ => limit y.1.2
  | j + 1, y, rest =>
      bodyEv y.1.1 y.1.2 (keeps y.1 y.2).1 _
        (loopRest r n body keeps cont j y
          (fun y' rest' => loopEvidence bodyEv j y' rest') rest)

end Loop

mutual

/-- The evidence of each approximant of a diagram, from a witness of its precondition. -/
def Diagram.evidence : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    (env : All X Γ) → (s : R) → (pre : (d.spec r).Pre (env, s)) →
    d.Evidence r n F stop env s pre
  | _, _, .exit out, env, s, _ => fun _ rest => rest (.inr (out.select env, s)) .refl
  | _, Qs, .step call next, env, s, pre => fun cont rest =>
      FreeDep.request (r := r) (shape := (⟨call.1, env.select call.2⟩, s))
        (next := Sum.elim (fun e => .pure (.inl e))
          (fun (b : (S.output call.1).At X × R) =>
            ((next b.1.1).run stop n (b.1.2.append env) cont).thread b.2))
        pre.1
        fun x post =>
          Sum.casesOn
            (motive := fun x =>
              (p : Spec.resumePre (fun (y : (S.output call.1).At X × R) =>
                ((next y.1.1).spec r).Pre (y.1.2.append env, y.2)) x) →
              ((m : E ⊕ (Qs.At X × R)) →
                Spec.resumePost
                  (fun (y : (S.output call.1).At X × R) p o =>
                    ((next y.1.1).spec r).Post (y.1.2.append env, y.2) p o) x p m →
                FreeDep r F (Free.resume cont m)) →
              FreeDep r F
                (Sum.elim (fun e => Free.pure (.inl e))
                  (fun (b : (S.output call.1).At X × R) =>
                    ((next b.1.1).run stop n (b.1.2.append env) cont).thread b.2) x))
            x (fun e _ k => k (.inl e) .refl)
            (fun b p k => Diagram.evidence (next b.1.1) (b.1.2.append env) b.2 p cont k)
            (pre.2 x post) (fun m tail => rest m ⟨x, post, tail⟩)
  | _, _, .seq first next, env, s, pre => fun cont rest =>
      Diagram.evidence first env s pre.1 _
        (seqRest r n first next env s pre
          (fun k s₁ p => Continuation.evidence next k s₁ p) cont rest)

def Continuation.evidence : {P : Boundary Ty} → {Qs : Exits Ty} →
    (k : Continuation S P Qs) → (a : P.At X) → (s : R) → (pre : (k.spec r).Pre (a, s)) →
    k.Evidence r n F stop a s pre
  | _, _, .copair each, a, s, pre => fun cont rest =>
      Diagram.evidence (each a.1) a.2 s pre cont rest
  | _, _, .frame kept args shared next, a, s, pre => fun cont rest =>
      Diagram.evidence shared (a.2.select (args a.1)) s pre.1 _
        (frameRest r n kept args shared next a s pre
          (fun k s₁ p => Continuation.evidence next k s₁ p) cont rest)
  | _, _, .loop body, a, s, pre => fun cont rest =>
      loopEvidence r limit n body pre.2.2 cont
        (fun a s₁ p => Continuation.evidence body a s₁ p) n ⟨(a, s), pre.2.1⟩ rest

end

end Evidence

end Draft

#print axioms Draft.Diagram.evidence

/-! Completeness: a run of the diagram over the witness, and then a run of the rest along its
evidence, is a run of each approximant along its evidence, from a threshold. -/

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  (r : DepPoly.{0, 0, 0, 0} ((S.interface X).runtime R E))
  {α : Type} {F : E ⊕ (α × R) → Type} {stop : Free (S.interface X) α}
  (limit : (s₀ : R) → FreeDep r F (stop.thread s₀))

abbrev Diagram.Along {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs) (env : All X Γ) (s : R)
    (pre : (d.spec r).Pre (env, s)) (m : E ⊕ (Qs.At X × R))
    (run : (d.spec r).Post (env, s) pre m) : Type :=
  (N : Nat) × ((n : Nat) → N ≤ n → (cont : Qs.At X → Free (S.interface X) α) →
    (rest : (m : E ⊕ (Qs.At X × R)) → (d.spec r).Post (env, s) pre m →
      FreeDep r F (Free.resume cont m)) →
    (o : E ⊕ (α × R)) → FreeDep.Runs (Free.resume cont m) (rest m run) o →
    FreeDep.Runs ((d.run stop n env cont).thread s)
      (Diagram.evidence r limit n d env s pre cont rest) o)

abbrev Continuation.Along {P : Boundary Ty} {Qs : Exits Ty} (k : Continuation S P Qs)
    (a : P.At X) (s : R) (pre : (k.spec r).Pre (a, s)) (m : E ⊕ (Qs.At X × R))
    (run : (k.spec r).Post (a, s) pre m) : Type :=
  (N : Nat) × ((n : Nat) → N ≤ n → (cont : Qs.At X → Free (S.interface X) α) →
    (rest : (m : E ⊕ (Qs.At X × R)) → (k.spec r).Post (a, s) pre m →
      FreeDep r F (Free.resume cont m)) →
    (o : E ⊕ (α × R)) → FreeDep.Runs (Free.resume cont m) (rest m run) o →
    FreeDep.Runs ((k.run stop n a cont).thread s)
      (Continuation.evidence r limit n k a s pre cont rest) o)

/-- Completeness after the result of the first diagram of a composite. -/
def seqAlong {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (first : Diagram S Γ (K :: Qs))
    (next : Continuation S K Qs) (env : All X Γ) (s : R)
    (pre : ((Diagram.seq first next).spec r).Pre (env, s))
    (nextAlong : (k : K.At X) → (s₁ : R) → (p : (next.spec r).Pre (k, s₁)) →
      (m : E ⊕ (Qs.At X × R)) → (run : (next.spec r).Post (k, s₁) p m) →
      next.Along r limit k s₁ p m run)
    (m : E ⊕ (Qs.At X × R)) :
    (m₁ : E ⊕ (Exits.At (K :: Qs) X × R)) → (run₁ : (first.spec r).Post (env, s) pre.1 m₁) →
    (tail : Spec.resumePost
      (fun (y : Exits.At (K :: Qs) X × R) p o =>
        Spec.atExit (fun k => (next.spec r).Pre (k, y.2))
          (fun k p o => (next.spec r).Post (k, y.2) p o)
          (fun q o => (Sum.inr (q, y.2) : E ⊕ (Qs.At X × R)) ≡ o) y.1 p o)
      m₁ (pre.2 m₁ run₁) m) →
    (N : Nat) × ((n : Nat) → N ≤ n → (cont : Qs.At X → Free (S.interface X) α) →
      (rest : (m : E ⊕ (Qs.At X × R)) →
        ((Diagram.seq first next).spec r).Post (env, s) pre m →
        FreeDep r F (Free.resume cont m)) →
      (o : E ⊕ (α × R)) → FreeDep.Runs (Free.resume cont m) (rest m ⟨m₁, run₁, tail⟩) o →
      FreeDep.Runs (Free.resume (Exits.At.elim (fun k => next.run stop n k cont) cont) m₁)
        (seqRest r n first next env s pre
          (fun k s₁ p => Continuation.evidence r limit n next k s₁ p) cont rest m₁ run₁) o)
  | .inl e, run₁, tail =>
      ⟨0, fun _ _ cont rest o t =>
        Identity.ind
          (fun (m : E ⊕ (Qs.At X × R)) (tail : (Sum.inl e : E ⊕ (Qs.At X × R)) ≡ m) =>
            FreeDep.Runs (Free.resume cont m) (rest m ⟨.inl e, run₁, tail⟩) o →
              FreeDep.Runs (Free.resume cont (.inl e)) (rest (.inl e) ⟨.inl e, run₁, .refl⟩) o)
          (fun t => t) tail t⟩
  | .inr y, run₁, tail =>
      Exits.At.cases
        (motive := fun x =>
          (run₁ : (first.spec r).Post (env, s) pre.1 (.inr (x, y.2))) →
          (tail : Spec.atExit (fun k => (next.spec r).Pre (k, y.2))
            (fun k p o => (next.spec r).Post (k, y.2) p o)
            (fun q o => (Sum.inr (q, y.2) : E ⊕ (Qs.At X × R)) ≡ o) x
            (pre.2 (.inr (x, y.2)) run₁) m) →
          (N : Nat) × ((n : Nat) → N ≤ n → (cont : Qs.At X → Free (S.interface X) α) →
            (rest : (m : E ⊕ (Qs.At X × R)) →
              ((Diagram.seq first next).spec r).Post (env, s) pre m →
              FreeDep r F (Free.resume cont m)) →
            (o : E ⊕ (α × R)) →
            FreeDep.Runs (Free.resume cont m) (rest m ⟨.inr (x, y.2), run₁, tail⟩) o →
            FreeDep.Runs
              ((Exits.At.elim (fun k => next.run stop n k cont) cont x).thread y.2)
              (seqRest r n first next env s pre
                (fun k s₁ p => Continuation.evidence r limit n next k s₁ p) cont rest
                (.inr (x, y.2)) run₁) o))
        (fun k run₁ tail =>
          let ih := nextAlong k y.2 (pre.2 (.inr (Exits.At.here k, y.2)) run₁) m tail
          ⟨ih.1, fun n hn cont rest o t =>
            ih.2 n hn cont (fun m tail => rest m ⟨.inr (Exits.At.here k, y.2), run₁, tail⟩) o t⟩)
        (fun q run₁ tail =>
          ⟨0, fun _ _ cont rest o t =>
            Identity.ind
              (fun (m : E ⊕ (Qs.At X × R))
                  (tail : (Sum.inr (q, y.2) : E ⊕ (Qs.At X × R)) ≡ m) =>
                FreeDep.Runs (Free.resume cont m)
                    (rest m ⟨.inr (Exits.At.there K q, y.2), run₁, tail⟩) o →
                  FreeDep.Runs (Free.resume cont (.inr (q, y.2)))
                    (rest (.inr (q, y.2)) ⟨.inr (Exits.At.there K q, y.2), run₁, .refl⟩) o)
              (fun t => t) tail t⟩)
        y.1 run₁ tail

/-- Completeness after the result of the diagram of a frame. -/
def frameAlong {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
    (kept : (c : P.Case) → M.At (Port c.1)) (args : (c : P.Case) → PortMap c.1 Δ)
    (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs) (a : P.At X) (s : R)
    (pre : ((Continuation.frame kept args shared next).spec r).Pre (a, s))
    (nextAlong : (k : (M.product K).At X) → (s₁ : R) → (p : (next.spec r).Pre (k, s₁)) →
      (m : E ⊕ (Qs.At X × R)) → (run : (next.spec r).Post (k, s₁) p m) →
      next.Along r limit k s₁ p m run)
    (m : E ⊕ (Qs.At X × R)) :
    (m₁ : E ⊕ (Exits.At [K] X × R)) →
    (run₁ : (shared.spec r).Post (a.2.select (args a.1), s) pre.1 m₁) →
    (tail : Spec.resumePost
      (fun (y : Exits.At [K] X × R) p o =>
        Spec.atExit
          (fun out =>
            (next.spec r).Pre
              (⟨Boundary.pair (kept a.1).1 out.1,
                out.2.append (a.2.select (kept a.1).2)⟩, y.2))
          (fun out p o =>
            (next.spec r).Post
              (⟨Boundary.pair (kept a.1).1 out.1,
                out.2.append (a.2.select (kept a.1).2)⟩, y.2) p o)
          (fun q _ => Exits.At.ofNil q) y.1 p o)
      m₁ (pre.2 m₁ run₁) m) →
    (N : Nat) × ((n : Nat) → N ≤ n → (cont : Qs.At X → Free (S.interface X) α) →
      (rest : (m : E ⊕ (Qs.At X × R)) →
        ((Continuation.frame kept args shared next).spec r).Post (a, s) pre m →
        FreeDep r F (Free.resume cont m)) →
      (o : E ⊕ (α × R)) → FreeDep.Runs (Free.resume cont m) (rest m ⟨m₁, run₁, tail⟩) o →
      FreeDep.Runs
        (Free.resume
          (Exits.At.only fun out =>
            next.run stop n
              ⟨Boundary.pair (kept a.1).1 out.1, out.2.append (a.2.select (kept a.1).2)⟩ cont)
          m₁)
        (frameRest r n kept args shared next a s pre
          (fun k s₁ p => Continuation.evidence r limit n next k s₁ p) cont rest m₁ run₁) o)
  | .inl e, run₁, tail =>
      ⟨0, fun _ _ cont rest o t =>
        Identity.ind
          (fun (m : E ⊕ (Qs.At X × R)) (tail : (Sum.inl e : E ⊕ (Qs.At X × R)) ≡ m) =>
            FreeDep.Runs (Free.resume cont m) (rest m ⟨.inl e, run₁, tail⟩) o →
              FreeDep.Runs (Free.resume cont (.inl e)) (rest (.inl e) ⟨.inl e, run₁, .refl⟩) o)
          (fun t => t) tail t⟩
  | .inr y, run₁, tail =>
      Exits.At.cases
        (motive := fun x =>
          (run₁ : (shared.spec r).Post (a.2.select (args a.1), s) pre.1 (.inr (x, y.2))) →
          (tail : Spec.atExit
            (fun out =>
              (next.spec r).Pre
                (⟨Boundary.pair (kept a.1).1 out.1,
                  out.2.append (a.2.select (kept a.1).2)⟩, y.2))
            (fun out p o =>
              (next.spec r).Post
                (⟨Boundary.pair (kept a.1).1 out.1,
                  out.2.append (a.2.select (kept a.1).2)⟩, y.2) p o)
            (fun q _ => Exits.At.ofNil q) x (pre.2 (.inr (x, y.2)) run₁) m) →
          (N : Nat) × ((n : Nat) → N ≤ n → (cont : Qs.At X → Free (S.interface X) α) →
            (rest : (m : E ⊕ (Qs.At X × R)) →
              ((Continuation.frame kept args shared next).spec r).Post (a, s) pre m →
              FreeDep r F (Free.resume cont m)) →
            (o : E ⊕ (α × R)) →
            FreeDep.Runs (Free.resume cont m) (rest m ⟨.inr (x, y.2), run₁, tail⟩) o →
            FreeDep.Runs
              ((Exits.At.only (fun out =>
                next.run stop n
                  ⟨Boundary.pair (kept a.1).1 out.1,
                    out.2.append (a.2.select (kept a.1).2)⟩ cont) x).thread y.2)
              (frameRest r n kept args shared next a s pre
                (fun k s₁ p => Continuation.evidence r limit n next k s₁ p) cont rest
                (.inr (x, y.2)) run₁) o))
        (fun out run₁ tail =>
          let ih := nextAlong _ y.2 (pre.2 (.inr (Exits.At.here out, y.2)) run₁) m tail
          ⟨ih.1, fun n hn cont rest o t =>
            ih.2 n hn cont
              (fun m tail => rest m ⟨.inr (Exits.At.here out, y.2), run₁, tail⟩) o t⟩)
        (fun q _ _ => Exits.At.ofNil q) y.1 run₁ tail

end Draft

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  (r : DepPoly.{0, 0, 0, 0} ((S.interface X).runtime R E))
  {α : Type} {F : E ⊕ (α × R) → Type} {stop : Free (S.interface X) α}
  (limit : (s₀ : R) → FreeDep r F (stop.thread s₀))

section LoopAlong

variable {K : Boundary Ty} {Qs : Exits Ty} (body : Continuation S K (K :: Qs))
  {Inv : K.At X × R → Type} (keeps : (iterSpec r body).Keeps Inv)

/-- The evidence of the unrollings at the next entrance, for the witness that the body gives
and for an identical witness. -/
def nextAlign (n j : Nat) (y : (a : K.At X × R) × Inv a) (a' : K.At X × R)
    (post : (iterSpec r body).Post y.1 (keeps y.1 y.2).1 (.inr a')) :
    (i' : Inv a') → (e₂ : (keeps y.1 y.2).2 a' post ≡ i') →
    (cont : Qs.At X → Free (S.interface X) α) →
    (rest : (m : E ⊕ (Qs.At X × R)) → Loop ((iterSpec r body).iterate keeps) y m →
      FreeDep r F (Free.resume cont m)) →
    (o : E ⊕ (α × R)) →
    FreeDep.Runs ((Continuation.unrolled stop (body.run stop n) j a'.1 cont).thread a'.2)
      (loopEvidence r limit n body keeps cont
        (fun a s₁ p => Continuation.evidence r limit n body a s₁ p) j ⟨a', i'⟩
        (fun m l =>
          rest m
            (Loop.next (F := (iterSpec r body).iterate keeps)
              (a' := (⟨a', i'⟩ : (a : K.At X × R) × Inv a)) ⟨post, e₂⟩ l))) o →
    FreeDep.Runs ((Continuation.unrolled stop (body.run stop n) j a'.1 cont).thread a'.2)
      (loopEvidence r limit n body keeps cont
        (fun a s₁ p => Continuation.evidence r limit n body a s₁ p) j
        ⟨a', (keeps y.1 y.2).2 a' post⟩
        (fun m l =>
          rest m
            (Loop.next (F := (iterSpec r body).iterate keeps)
              (a' := (⟨a', (keeps y.1 y.2).2 a' post⟩ : (a : K.At X × R) × Inv a))
              ⟨post, .refl⟩ l))) o :=
  fun i' e₂ =>
    Identity.ind
      (fun (i' : Inv a') (e₂ : (keeps y.1 y.2).2 a' post ≡ i') =>
        (cont : Qs.At X → Free (S.interface X) α) →
        (rest : (m : E ⊕ (Qs.At X × R)) → Loop ((iterSpec r body).iterate keeps) y m →
          FreeDep r F (Free.resume cont m)) →
        (o : E ⊕ (α × R)) →
        FreeDep.Runs ((Continuation.unrolled stop (body.run stop n) j a'.1 cont).thread a'.2)
          (loopEvidence r limit n body keeps cont
            (fun a s₁ p => Continuation.evidence r limit n body a s₁ p) j ⟨a', i'⟩
            (fun m l =>
              rest m
                (Loop.next (F := (iterSpec r body).iterate keeps)
                  (a' := (⟨a', i'⟩ : (a : K.At X × R) × Inv a)) ⟨post, e₂⟩ l))) o →
        FreeDep.Runs ((Continuation.unrolled stop (body.run stop n) j a'.1 cont).thread a'.2)
          (loopEvidence r limit n body keeps cont
            (fun a s₁ p => Continuation.evidence r limit n body a s₁ p) j
            ⟨a', (keeps y.1 y.2).2 a' post⟩
            (fun m l =>
              rest m
                (Loop.next (F := (iterSpec r body).iterate keeps)
                  (a' := (⟨a', (keeps y.1 y.2).2 a' post⟩ : (a : K.At X × R) × Inv a))
                  ⟨post, .refl⟩ l))) o)
      (fun _ _ _ t => t) e₂

/-- Completeness of a loop, from the completeness of its body. -/
def loopAlong
    (bodyAlong : (a : K.At X) → (s₁ : R) → (p : (body.spec r).Pre (a, s₁)) →
      (m' : E ⊕ (Exits.At (K :: Qs) X × R)) → (run : (body.spec r).Post (a, s₁) p m') →
      body.Along r limit a s₁ p m' run) :
    {y : (a : K.At X × R) × Inv a} → {m : E ⊕ (Qs.At X × R)} →
    (l : Loop ((iterSpec r body).iterate keeps) y m) →
    (N : Nat) × ((n j : Nat) → N ≤ n → N ≤ j → (cont : Qs.At X → Free (S.interface X) α) →
      (rest : (m : E ⊕ (Qs.At X × R)) → Loop ((iterSpec r body).iterate keeps) y m →
        FreeDep r F (Free.resume cont m)) →
      (o : E ⊕ (α × R)) → FreeDep.Runs (Free.resume cont m) (rest m l) o →
      FreeDep.Runs ((Continuation.unrolled stop (body.run stop n) j y.1.1 cont).thread y.1.2)
        (loopEvidence r limit n body keeps cont
          (fun a s₁ p => Continuation.evidence r limit n body a s₁ p) j y rest) o)
  | y, .inl e, .exit bodyRun =>
      let ihb := bodyAlong y.1.1 y.1.2 (keeps y.1 y.2).1 (.inl e) bodyRun
      ⟨ihb.1 + 1, fun n j hn hj cont rest o t =>
        match j, hj with
        | 0, hj => absurd hj (Nat.not_succ_le_zero _)
        | j + 1, _ =>
            ihb.2 n (Nat.le_trans (Nat.le_add_right _ _) hn) _
              (loopRest r n body keeps cont j y
                (fun y' rest' =>
                  loopEvidence r limit n body keeps cont
                    (fun a s₁ p => Continuation.evidence r limit n body a s₁ p) j y' rest')
                rest) o t⟩
  | y, .inr b, .exit bodyRun =>
      let ihb :=
        bodyAlong y.1.1 y.1.2 (keeps y.1 y.2).1 (.inr (Exits.At.there K b.1, b.2)) bodyRun
      ⟨ihb.1 + 1, fun n j hn hj cont rest o t =>
        match j, hj with
        | 0, hj => absurd hj (Nat.not_succ_le_zero _)
        | j + 1, _ =>
            ihb.2 n (Nat.le_trans (Nat.le_add_right _ _) hn) _
              (loopRest r n body keeps cont j y
                (fun y' rest' =>
                  loopEvidence r limit n body keeps cont
                    (fun a s₁ p => Continuation.evidence r limit n body a s₁ p) j y' rest')
                rest) o t⟩
  | y, _, .next (a' := y') p l =>
      let ihb :=
        bodyAlong y.1.1 y.1.2 (keeps y.1 y.2).1 (.inr (Exits.At.here y'.1.1, y'.1.2)) p.1
      let ihl := loopAlong bodyAlong l
      ⟨ihb.1 + ihl.1 + 1, fun n j hn hj cont rest o t =>
        match j, hj with
        | 0, hj => absurd hj (Nat.not_succ_le_zero _)
        | j + 1, hj =>
            ihb.2 n
              (Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) hn) _
              (loopRest r n body keeps cont j y
                (fun y' rest' =>
                  loopEvidence r limit n body keeps cont
                    (fun a s₁ p => Continuation.evidence r limit n body a s₁ p) j y' rest')
                rest) o
              (nextAlign r limit body keeps n j y y'.1 p.1 y'.2 p.2 cont rest o
                (ihl.2 n j
                  (Nat.le_trans
                    (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)) hn)
                  (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_succ_le_succ hj)) cont
                  (fun m l' =>
                    rest m
                      (Loop.next (F := (iterSpec r body).iterate keeps) (a' := y') p l'))
                  o t))⟩

end LoopAlong

mutual

/-- Completeness: a run of a diagram over a witness, and then a run of the rest along its
evidence, is a run of each approximant along its evidence, from a threshold. -/
def Diagram.along : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) → (env : All X Γ) →
    (s : R) → (pre : (d.spec r).Pre (env, s)) → (m : E ⊕ (Qs.At X × R)) →
    (run : (d.spec r).Post (env, s) pre m) → d.Along r limit env s pre m run
  | _, Qs, .exit out, env, s, _, _, run =>
      ⟨0, fun _ _ cont rest o t =>
        Identity.ind
          (fun (m : E ⊕ (Qs.At X × R))
              (run : (Sum.inr (out.select env, s) : E ⊕ (Qs.At X × R)) ≡ m) =>
            FreeDep.Runs (Free.resume cont m) (rest m run) o →
              FreeDep.Runs (Free.resume cont (.inr (out.select env, s)))
                (rest (.inr (out.select env, s)) .refl) o)
          (fun t => t) run t⟩
  | _, Qs, .step call next, env, s, pre, m, run =>
      match run with
      | ⟨.inl e, post, tail⟩ =>
          ⟨0, fun _ _ cont rest o t =>
            ⟨.inl e, post,
              Identity.ind
                (fun (m : E ⊕ (Qs.At X × R)) (tail : (Sum.inl e : E ⊕ (Qs.At X × R)) ≡ m) =>
                  FreeDep.Runs (Free.resume cont m) (rest m ⟨.inl e, post, tail⟩) o →
                    FreeDep.Runs (Free.resume cont (.inl e))
                      (rest (.inl e) ⟨.inl e, post, .refl⟩) o)
                (fun t => t) tail t⟩⟩
      | ⟨.inr b, post, tail⟩ =>
          let ih :=
            Diagram.along (next b.1.1) (b.1.2.append env) b.2 (pre.2 (.inr b) post) m tail
          ⟨ih.1, fun n hn cont rest o t =>
            ⟨.inr b, post, ih.2 n hn cont (fun m tail => rest m ⟨.inr b, post, tail⟩) o t⟩⟩
  | _, _, .seq first next, env, s, pre, m, run =>
      let ih₁ := Diagram.along first env s pre.1 run.1 run.2.1
      let tl :=
        seqAlong r limit first next env s pre
          (fun k s₁ p m run => Continuation.along next k s₁ p m run) m run.1 run.2.1 run.2.2
      ⟨ih₁.1 + tl.1, fun n hn cont rest o t =>
        ih₁.2 n (Nat.le_trans (Nat.le_add_right _ _) hn) _
          (seqRest r n first next env s pre
            (fun k s₁ p => Continuation.evidence r limit n next k s₁ p) cont rest) o
          (tl.2 n (Nat.le_trans (Nat.le_add_left _ _) hn) cont rest o t)⟩

def Continuation.along : {P : Boundary Ty} → {Qs : Exits Ty} → (k : Continuation S P Qs) →
    (a : P.At X) → (s : R) → (pre : (k.spec r).Pre (a, s)) → (m : E ⊕ (Qs.At X × R)) →
    (run : (k.spec r).Post (a, s) pre m) → k.Along r limit a s pre m run
  | _, _, .copair each, a, s, pre, m, run => Diagram.along (each a.1) a.2 s pre m run
  | _, _, .frame kept args shared next, a, s, pre, m, run =>
      let ih₁ := Diagram.along shared (a.2.select (args a.1)) s pre.1 run.1 run.2.1
      let tl :=
        frameAlong r limit kept args shared next a s pre
          (fun k s₁ p m run => Continuation.along next k s₁ p m run) m run.1 run.2.1 run.2.2
      ⟨ih₁.1 + tl.1, fun n hn cont rest o t =>
        ih₁.2 n (Nat.le_trans (Nat.le_add_right _ _) hn) _
          (frameRest r n kept args shared next a s pre
            (fun k s₁ p => Continuation.evidence r limit n next k s₁ p) cont rest) o
          (tl.2 n (Nat.le_trans (Nat.le_add_left _ _) hn) cont rest o t)⟩
  | _, _, .loop body, _, _, pre, _, run =>
      let l :=
        loopAlong r limit body pre.2.2
          (fun a s₁ p m' run => Continuation.along body a s₁ p m' run) run
      ⟨l.1, fun n hn cont rest o t => l.2 n n hn hn cont rest o t⟩

end

end Draft

#print axioms Draft.Diagram.along

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  (r : DepPoly.{0, 0, 0, 0} ((S.interface X).runtime R E))
  (always : (a : ((S.interface X).runtime R E).Shape) → r.Pre a)

mutual

/-- A specification of the calls with a witness of each precondition gives a witness of the
precondition of each diagram. -/
def Diagram.witness : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    (a : All X Γ × R) → (d.spec r).Pre a
  | _, _, .exit _, _ => PUnit.unit
  | _, _, .step call next, a =>
      ⟨always _, fun x _ =>
        Sum.casesOn
          (motive := fun x =>
            Spec.resumePre (fun (y : (S.output call.1).At X × R) =>
              ((next y.1.1).spec r).Pre (y.1.2.append a.1, y.2)) x)
          x (fun _ => PUnit.unit) (fun y => Diagram.witness (next y.1.1) (y.1.2.append a.1, y.2))⟩
  | _, Qs, .seq (K := K) first next, a =>
      ⟨Diagram.witness first a, fun m _ =>
        Sum.casesOn
          (motive := fun m =>
            Spec.resumePre (fun (y : Exits.At (K :: Qs) X × R) =>
              Spec.exitPre (fun k => (next.spec r).Pre (k, y.2)) y.1) m)
          m (fun _ => PUnit.unit)
          (fun y =>
            Exits.At.cases
              (motive := fun e => Spec.exitPre (fun k => (next.spec r).Pre (k, y.2)) e)
              (fun k => Continuation.witness next (k, y.2)) (fun _ => PUnit.unit) y.1)⟩

def Continuation.witness : {P : Boundary Ty} → {Qs : Exits Ty} → (k : Continuation S P Qs) →
    (a : P.At X × R) → (k.spec r).Pre a
  | _, _, .copair each, a => Diagram.witness (each a.1.1) (a.1.2, a.2)
  | _, _, .frame (K := K) kept args shared next, a =>
      ⟨Diagram.witness shared (a.1.2.select (args a.1.1), a.2), fun m _ =>
        Sum.casesOn
          (motive := fun m =>
            Spec.resumePre (fun (y : Exits.At [K] X × R) =>
              Spec.exitPre (fun out =>
                (next.spec r).Pre
                  (⟨Boundary.pair (kept a.1.1).1 out.1,
                    out.2.append (a.1.2.select (kept a.1.1).2)⟩, y.2)) y.1) m)
          m (fun _ => PUnit.unit)
          (fun y =>
            Exits.At.cases
              (motive := fun e =>
                Spec.exitPre (fun out =>
                  (next.spec r).Pre
                    (⟨Boundary.pair (kept a.1.1).1 out.1,
                      out.2.append (a.1.2.select (kept a.1.1).2)⟩, y.2)) e)
              (fun out => Continuation.witness next _) (fun _ => PUnit.unit) y.1)⟩
  | _, _, .loop body, _ =>
      ⟨fun _ => PUnit, PUnit.unit, fun a' _ => ⟨Continuation.witness body a', fun _ _ => PUnit.unit⟩⟩

end

end Draft

namespace Draft.Checks.Specification

open Draft Draft.Checks.Countdown

/-- A machine with a response at each call. -/
def machine : Machine (sig.interface Value) Nat Unit := fun a => .inr (handle a.1 a.2)

abbrev G : DepPoly.{0, 0, 0, 0} ((sig.interface Value).runtime Nat Unit) := machine.graph

abbrev Res : Type := Unit ⊕ (Option (Exits.At [Out] Value) × Nat)

/-- The condition at a result of an approximant of a continuation, over a witness: the runs to
a stop, the runs to an exit, and no condition at the limit. -/
def Seen (k : Continuation sig Entry [Out]) (x : Entry.At Value × Nat) (w : (k.spec G).Pre x) :
    Res → Type
  | .inl e => (k.spec G).Post x w (.inl e)
  | .inr (some q, s') => (k.spec G).Post x w (.inr (q, s'))
  | .inr (none, _) => PUnit

/-- The rest that returns the run. -/
def returns (k : Continuation sig Entry [Out]) (x : Entry.At Value × Nat) (w : (k.spec G).Pre x) :
    (m : Unit ⊕ (Exits.At [Out] Value × Nat)) → (k.spec G).Post x w m →
    FreeDep G (Seen k x w)
      (Free.resume (fun q => (Free.pure (some q) : Free (sig.interface Value) _)) m)
  | .inl e, run => FreeDep.pure (Q := Seen k x w) (value := Sum.inl e) run
  | .inr y, run => FreeDep.pure (Q := Seen k x w) (value := Sum.inr (some y.1, y.2)) run

/-- The evidence at the limit: no condition. -/
def limitEv (k : Continuation sig Entry [Out]) (x : Entry.At Value × Nat) (w : (k.spec G).Pre x)
    (s₀ : Nat) :
    FreeDep G (Seen k x w)
      ((Free.pure none : Free (sig.interface Value) (Option (Exits.At [Out] Value))).thread s₀) :=
  FreeDep.pure (Q := Seen k x w) (value := Sum.inr (none, s₀)) PUnit.unit

/-! The loop of the countdown. -/

def keepsAll : (iterSpec G body).Keeps fun _ => PUnit :=
  fun a' _ => ⟨Continuation.witness G (fun _ => PUnit.unit) body a', fun _ _ => PUnit.unit⟩

def wit (c a s : Nat) : (loop.spec G).Pre (entry c a, s) := ⟨fun _ => PUnit, PUnit.unit, keepsAll⟩

abbrev StepS := (iterSpec G body).iterate keepsAll

set_option smartUnfolding false in
def goes (c a s : Nat) :
    StepS ⟨(entry (c + 1) a, s), PUnit.unit⟩ (.inr ⟨(entry c (s + a), s + 1), PUnit.unit⟩) :=
  ⟨⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s), .refl, .inr (value c, s), .refl,
      .inr (value (s + a), s + 1), .refl, .refl⟩,
    .refl⟩

set_option smartUnfolding false in
def ends (a s : Nat) : StepS ⟨(entry 0 a, s), PUnit.unit⟩ (.inl (.inr (out a, s))) :=
  ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s), .refl, .refl⟩

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

#print axioms Draft.Checks.Specification.thresholdTwo
#print axioms Draft.Checks.Specification.roundTrip

/-! ### The relation with the evidence of a diagram with a runtime -/

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  (r : DepPoly.{0, 0, 0, 0} ((S.interface X).runtime R E))

/-- A diagram is verified for its own specification, for each number of unrollings: the
evidence of a diagram with a runtime, with the runs as the conditions. It is the evidence of
the approximant, with the two conditions as one family. -/
def Diagram.verified (n : Nat) {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs)
    (env : All X Γ) (s : R) (pre : (d.spec r).Pre (env, s)) :
    d.StateDep r n (fun x s' => (d.spec r).Post (env, s) pre (.inr (x, s')))
      (fun e => (d.spec r).Post (env, s) pre (.inl e)) (fun _ => PUnit) env s :=
  @fun _ F _ stops limit cont done =>
    Diagram.evidence r (fun s₀ => limit s₀ PUnit.unit) n d env s pre cont fun m =>
      Sum.casesOn
        (motive := fun m => (d.spec r).Post (env, s) pre m → FreeDep r F (Free.resume cont m))
        m (fun e run => FreeDep.pure (Q := F) (value := Sum.inl e) (stops e run))
        (fun y run => done y.1 y.2 run)

/-- The converse: the evidence of a diagram with a runtime, with the runs as the conditions,
gives the evidence of the approximant with one family. -/
def Diagram.StateDep.toEvidence {n : Nat} {Γ : List Ty} {Qs : Exits Ty} {d : Diagram S Γ Qs}
    {env : All X Γ} {s : R} {pre : (d.spec r).Pre (env, s)}
    (dep : d.StateDep r n (fun x s' => (d.spec r).Post (env, s) pre (.inr (x, s')))
      (fun e => (d.spec r).Post (env, s) pre (.inl e)) (fun _ => PUnit) env s)
    {α : Type} {F : E ⊕ (α × R) → Type} {stop : Free (S.interface X) α}
    (limit : (s₀ : R) → FreeDep r F (stop.thread s₀)) : d.Evidence r n F stop env s pre :=
  fun _ rest =>
    dep (fun e run => (rest (.inl e) run).result) (fun s₀ _ => limit s₀)
      (fun x s' run => rest (.inr (x, s')) run)

/-! ### A bound on the runs, and the limit condition -/

/-- A condition after a result with a stop, over the witness after that result. -/
def Spec.resumeOn {M : Type} {P : M → Type 1} (W : (m : M) → P m → Type) :
    (x : E ⊕ M) → Spec.resumePre P x → Type
  | .inl _, _ => PUnit
  | .inr m, p => W m p

/-- A condition at an exit, over the witness at that exit. -/
def Spec.exitOn {K : Boundary Ty} {Qs : Exits Ty} (headPre : K.At X → Type 1)
    (W : (k : K.At X) → headPre k → Type) :
    (e : Exits.At (K :: Qs) X) → Spec.exitPre headPre e → Type :=
  Exits.At.cases (motive := fun e => Spec.exitPre headPre e → Type) W (fun _ _ => PUnit)

/-- The bound of a loop, for a number of unrollings. With no unrolling, the entrance has the
condition of the limit. With one more unrolling, the body has its bound, and each next
entrance that a run of the body gives has the bound with one unrolling less. -/
def Spec.Bound {A B : Type} (F : Spec A (B ⊕ A)) {Inv : A → Type} (keeps : F.Keeps Inv)
    (bodyOn : (a : A) → F.Pre a → Type) (atLimit : A → Type) : Nat → ((a : A) × Inv a) → Type
  | 0, y => atLimit y.1
  | m + 1, y =>
      bodyOn y.1 (keeps y.1 y.2).1 ×
        ((a' : A) → (post : F.Post y.1 (keeps y.1 y.2).1 (.inr a')) →
          Spec.Bound F keeps bodyOn atLimit m ⟨a', (keeps y.1 y.2).2 a' post⟩)

variable (r : DepPoly.{0, 0, 0, 0} ((S.interface X).runtime R E)) (L : R → Type)

mutual

/-- The bound of a diagram over a witness of its precondition, for a number of unrollings: each
run over the witness reaches the limit of a loop only at a runtime with the condition `L`. -/
def Diagram.Within (n : Nat) : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    (a : All X Γ × R) → (d.spec r).Pre a → Type
  | _, _, .exit _, _, _ => PUnit
  | _, _, .step call rest, a, pre =>
      (x : E ⊕ ((S.output call.1).At X × R)) →
        (post : r.Post (⟨call.1, a.1.select call.2⟩, a.2) pre.1 x) →
        Spec.resumeOn
          (fun (y : (S.output call.1).At X × R) p =>
            (rest y.1.1).Within n (y.1.2.append a.1, y.2) p) x (pre.2 x post)
  | _, Qs, .seq (K := K) first next, a, pre =>
      first.Within n a pre.1 ×
        ((m : E ⊕ (Exits.At (K :: Qs) X × R)) →
          (post : (first.spec r).Post a pre.1 m) →
          Spec.resumeOn
            (fun (y : Exits.At (K :: Qs) X × R) p =>
              Spec.exitOn (fun k => (next.spec r).Pre (k, y.2))
                (fun k p => next.Within n (k, y.2) p) y.1 p) m (pre.2 m post))

def Continuation.Within (n : Nat) : {P : Boundary Ty} → {Qs : Exits Ty} →
    (k : Continuation S P Qs) → (a : P.At X × R) → (k.spec r).Pre a → Type
  | _, _, .copair each, a, pre => (each a.1.1).Within n (a.1.2, a.2) pre
  | _, _, .frame (K := K) kept args shared next, a, pre =>
      shared.Within n (a.1.2.select (args a.1.1), a.2) pre.1 ×
        ((m : E ⊕ (Exits.At [K] X × R)) →
          (post : (shared.spec r).Post (a.1.2.select (args a.1.1), a.2) pre.1 m) →
          Spec.resumeOn
            (fun (y : Exits.At [K] X × R) p =>
              Spec.exitOn
                (fun out =>
                  (next.spec r).Pre
                    (⟨Boundary.pair (kept a.1.1).1 out.1,
                      out.2.append (a.1.2.select (kept a.1.1).2)⟩, y.2))
                (fun out p =>
                  next.Within n
                    (⟨Boundary.pair (kept a.1.1).1 out.1,
                      out.2.append (a.1.2.select (kept a.1.1).2)⟩, y.2) p) y.1 p)
            m (pre.2 m post))
  | _, _, .loop body, a, pre =>
      Spec.Bound (iterSpec r body) pre.2.2 (fun a p => body.Within n a p) (fun a => L a.2) n
        ⟨a, pre.2.1⟩

end

section At

variable {α : Type} {F : E ⊕ (α × R) → Type} {stop : Free (S.interface X) α}
  (limit : (s₀ : R) → L s₀ → FreeDep r F (stop.thread s₀)) (n : Nat)

/-- The evidence of the rest of the first diagram of a composite, with a bound. -/
def seqRestAt {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (first : Diagram S Γ (K :: Qs))
    (next : Continuation S K Qs) (env : All X Γ) (s : R)
    (pre : ((Diagram.seq first next).spec r).Pre (env, s))
    (within : (Diagram.seq first next).Within r L n (env, s) pre)
    (nextEv : (k : K.At X) → (s₁ : R) → (p : (next.spec r).Pre (k, s₁)) →
      next.Within r L n (k, s₁) p → next.Evidence r n F stop k s₁ p)
    (cont : Qs.At X → Free (S.interface X) α)
    (rest : (m : E ⊕ (Qs.At X × R)) → ((Diagram.seq first next).spec r).Post (env, s) pre m →
      FreeDep r F (Free.resume cont m)) :
    (m₁ : E ⊕ (Exits.At (K :: Qs) X × R)) → (first.spec r).Post (env, s) pre.1 m₁ →
    FreeDep r F (Free.resume (Exits.At.elim (fun k => next.run stop n k cont) cont) m₁)
  | .inl e, run₁ => rest (.inl e) ⟨.inl e, run₁, .refl⟩
  | .inr y, run₁ =>
      Exits.At.cases
        (motive := fun x => (first.spec r).Post (env, s) pre.1 (.inr (x, y.2)) →
          FreeDep r F ((Exits.At.elim (fun k => next.run stop n k cont) cont x).thread y.2))
        (fun k run₁ =>
          nextEv k y.2 (pre.2 (.inr (Exits.At.here k, y.2)) run₁)
            (within.2 (.inr (Exits.At.here k, y.2)) run₁) cont
            (fun m tail => rest m ⟨.inr (Exits.At.here k, y.2), run₁, tail⟩))
        (fun q run₁ => rest (.inr (q, y.2)) ⟨.inr (Exits.At.there K q, y.2), run₁, .refl⟩)
        y.1 run₁

/-- The evidence of the rest of the diagram of a frame, with a bound. -/
def frameRestAt {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
    (kept : (c : P.Case) → M.At (Port c.1)) (args : (c : P.Case) → PortMap c.1 Δ)
    (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs) (a : P.At X) (s : R)
    (pre : ((Continuation.frame kept args shared next).spec r).Pre (a, s))
    (within : (Continuation.frame kept args shared next).Within r L n (a, s) pre)
    (nextEv : (k : (M.product K).At X) → (s₁ : R) → (p : (next.spec r).Pre (k, s₁)) →
      next.Within r L n (k, s₁) p → next.Evidence r n F stop k s₁ p)
    (cont : Qs.At X → Free (S.interface X) α)
    (rest : (m : E ⊕ (Qs.At X × R)) →
      ((Continuation.frame kept args shared next).spec r).Post (a, s) pre m →
      FreeDep r F (Free.resume cont m)) :
    (m₁ : E ⊕ (Exits.At [K] X × R)) →
    (shared.spec r).Post (a.2.select (args a.1), s) pre.1 m₁ →
    FreeDep r F
      (Free.resume
        (Exits.At.only fun out =>
          next.run stop n
            ⟨Boundary.pair (kept a.1).1 out.1, out.2.append (a.2.select (kept a.1).2)⟩ cont)
        m₁)
  | .inl e, run₁ => rest (.inl e) ⟨.inl e, run₁, .refl⟩
  | .inr y, run₁ =>
      Exits.At.cases
        (motive := fun x =>
          (shared.spec r).Post (a.2.select (args a.1), s) pre.1 (.inr (x, y.2)) →
            FreeDep r F
              ((Exits.At.only (fun out =>
                next.run stop n
                  ⟨Boundary.pair (kept a.1).1 out.1,
                    out.2.append (a.2.select (kept a.1).2)⟩ cont) x).thread y.2))
        (fun out run₁ =>
          nextEv _ y.2 (pre.2 (.inr (Exits.At.here out, y.2)) run₁)
            (within.2 (.inr (Exits.At.here out, y.2)) run₁) cont
            (fun m tail => rest m ⟨.inr (Exits.At.here out, y.2), run₁, tail⟩))
        (fun q _ => Exits.At.ofNil q) y.1 run₁

section LoopAt

variable {K : Boundary Ty} {Qs : Exits Ty} (body : Continuation S K (K :: Qs))
  {Inv : K.At X × R → Type} (keeps : (iterSpec r body).Keeps Inv)
  (cont : Qs.At X → Free (S.interface X) α)

/-- The bound of a loop, for the body and the limit condition of a diagram. -/
abbrev LoopBound (j : Nat) (y : (a : K.At X × R) × Inv a) : Type :=
  Spec.Bound (iterSpec r body) keeps (fun a p => body.Within r L n a p) (fun a => L a.2) j y

/-- The evidence of the rest of the body of a loop, with the bound at each next entrance. -/
def loopRestAt (j : Nat) (y : (a : K.At X × R) × Inv a)
    (nexts : (a' : K.At X × R) →
      (post : (iterSpec r body).Post y.1 (keeps y.1 y.2).1 (.inr a')) →
      LoopBound r L n body keeps j ⟨a', (keeps y.1 y.2).2 a' post⟩)
    (again : (y' : (a : K.At X × R) × Inv a) → LoopBound r L n body keeps j y' →
      ((m : E ⊕ (Qs.At X × R)) → Loop ((iterSpec r body).iterate keeps) y' m →
        FreeDep r F (Free.resume cont m)) →
      FreeDep r F
        ((Continuation.unrolled stop (body.run stop n) j y'.1.1 cont).thread y'.1.2))
    (rest : (m : E ⊕ (Qs.At X × R)) → Loop ((iterSpec r body).iterate keeps) y m →
      FreeDep r F (Free.resume cont m)) :
    (m' : E ⊕ (Exits.At (K :: Qs) X × R)) → (body.spec r).Post y.1 (keeps y.1 y.2).1 m' →
    FreeDep r F
      (Free.resume
        (Exits.At.elim (fun k' => Continuation.unrolled stop (body.run stop n) j k' cont) cont)
        m')
  | .inl e, bodyRun => rest (.inl e) (.exit bodyRun)
  | .inr b, bodyRun =>
      Exits.At.cases
        (motive := fun x => (body.spec r).Post y.1 (keeps y.1 y.2).1 (.inr (x, b.2)) →
          FreeDep r F
            ((Exits.At.elim
              (fun k' => Continuation.unrolled stop (body.run stop n) j k' cont) cont
              x).thread b.2))
        (fun k' bodyRun =>
          again ⟨(k', b.2), (keeps y.1 y.2).2 (k', b.2) bodyRun⟩ (nexts (k', b.2) bodyRun)
            (fun m l =>
              rest m
                (Loop.next (F := (iterSpec r body).iterate keeps)
                  (a' := (⟨(k', b.2), (keeps y.1 y.2).2 (k', b.2) bodyRun⟩ :
                    (a : K.At X × R) × Inv a))
                  ⟨bodyRun, .refl⟩ l)))
        (fun q bodyRun => rest (.inr (q, b.2)) (.exit bodyRun))
        b.1 bodyRun

/-- The evidence of the unrollings of a loop, with a bound. -/
def loopEvidenceAt
    (bodyEv : (a : K.At X) → (s₁ : R) → (p : (body.spec r).Pre (a, s₁)) →
      body.Within r L n (a, s₁) p → body.Evidence r n F stop a s₁ p) :
    (j : Nat) → (y : (a : K.At X × R) × Inv a) → LoopBound r L n body keeps j y →
    ((m : E ⊕ (Qs.At X × R)) → Loop ((iterSpec r body).iterate keeps) y m →
      FreeDep r F (Free.resume cont m)) →
    FreeDep r F ((Continuation.unrolled stop (body.run stop n) j y.1.1 cont).thread y.1.2)
  | 0, y, bound, _ => limit y.1.2 bound
  | j + 1, y, bound, rest =>
      bodyEv y.1.1 y.1.2 (keeps y.1 y.2).1 bound.1 _
        (loopRestAt r L n body keeps cont j y bound.2
          (fun y' bound' rest' => loopEvidenceAt bodyEv j y' bound' rest') rest)

end LoopAt

mutual

/-- The evidence of an approximant of a diagram, from a witness of its precondition and a
bound: the limit of a loop is reached only at a runtime with the condition `L`. -/
def Diagram.evidenceAt : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    (env : All X Γ) → (s : R) → (pre : (d.spec r).Pre (env, s)) →
    d.Within r L n (env, s) pre → d.Evidence r n F stop env s pre
  | _, _, .exit out, env, s, _, _ => fun _ rest => rest (.inr (out.select env, s)) .refl
  | _, Qs, .step call next, env, s, pre, within => fun cont rest =>
      FreeDep.request (r := r) (shape := (⟨call.1, env.select call.2⟩, s))
        (next := Sum.elim (fun e => .pure (.inl e))
          (fun (b : (S.output call.1).At X × R) =>
            ((next b.1.1).run stop n (b.1.2.append env) cont).thread b.2))
        pre.1
        fun x post =>
          Sum.casesOn
            (motive := fun x =>
              (p : Spec.resumePre (fun (y : (S.output call.1).At X × R) =>
                ((next y.1.1).spec r).Pre (y.1.2.append env, y.2)) x) →
              Spec.resumeOn
                (fun (y : (S.output call.1).At X × R) p =>
                  (next y.1.1).Within r L n (y.1.2.append env, y.2) p) x p →
              ((m : E ⊕ (Qs.At X × R)) →
                Spec.resumePost
                  (fun (y : (S.output call.1).At X × R) p o =>
                    ((next y.1.1).spec r).Post (y.1.2.append env, y.2) p o) x p m →
                FreeDep r F (Free.resume cont m)) →
              FreeDep r F
                (Sum.elim (fun e => Free.pure (.inl e))
                  (fun (b : (S.output call.1).At X × R) =>
                    ((next b.1.1).run stop n (b.1.2.append env) cont).thread b.2) x))
            x (fun e _ _ k => k (.inl e) .refl)
            (fun b p w k =>
              Diagram.evidenceAt (next b.1.1) (b.1.2.append env) b.2 p w cont k)
            (pre.2 x post) (within x post) (fun m tail => rest m ⟨x, post, tail⟩)
  | _, _, .seq first next, env, s, pre, within => fun cont rest =>
      Diagram.evidenceAt first env s pre.1 within.1 _
        (seqRestAt r L n first next env s pre within
          (fun k s₁ p w => Continuation.evidenceAt next k s₁ p w) cont rest)

def Continuation.evidenceAt : {P : Boundary Ty} → {Qs : Exits Ty} →
    (k : Continuation S P Qs) → (a : P.At X) → (s : R) → (pre : (k.spec r).Pre (a, s)) →
    k.Within r L n (a, s) pre → k.Evidence r n F stop a s pre
  | _, _, .copair each, a, s, pre, within => fun cont rest =>
      Diagram.evidenceAt (each a.1) a.2 s pre within cont rest
  | _, _, .frame kept args shared next, a, s, pre, within => fun cont rest =>
      Diagram.evidenceAt shared (a.2.select (args a.1)) s pre.1 within.1 _
        (frameRestAt r L n kept args shared next a s pre within
          (fun k s₁ p w => Continuation.evidenceAt next k s₁ p w) cont rest)
  | _, _, .loop body, a, s, pre, within => fun cont rest =>
      loopEvidenceAt r L limit n body pre.2.2 cont
        (fun a s₁ p w => Continuation.evidenceAt body a s₁ p w) n ⟨(a, s), pre.2.1⟩ within rest

end

end At

/-- With a witness of the precondition and a bound, a diagram has the evidence of a diagram
with a runtime, with the condition `L` at the limit. -/
def Continuation.verifiedAt (n : Nat) {P : Boundary Ty} {Qs : Exits Ty} (k : Continuation S P Qs)
    (a : P.At X) (s : R) (pre : (k.spec r).Pre (a, s)) (within : k.Within r L n (a, s) pre) :
    k.StateDep r n (fun x s' => (k.spec r).Post (a, s) pre (.inr (x, s')))
      (fun e => (k.spec r).Post (a, s) pre (.inl e)) L a s :=
  @fun _ F _ stops limit cont done =>
    Continuation.evidenceAt r L limit n k a s pre within cont fun m =>
      Sum.casesOn
        (motive := fun m => (k.spec r).Post (a, s) pre m → FreeDep r F (Free.resume cont m))
        m (fun e run => FreeDep.pure (Q := F) (value := Sum.inl e) (stops e run))
        (fun y run => done y.1 y.2 run)

/-- With a witness of the precondition and a bound, a diagram has the evidence of a diagram
with a runtime, with the condition `L` at the limit. -/
def Diagram.verifiedAt (n : Nat) {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs)
    (env : All X Γ) (s : R) (pre : (d.spec r).Pre (env, s))
    (within : d.Within r L n (env, s) pre) :
    d.StateDep r n (fun x s' => (d.spec r).Post (env, s) pre (.inr (x, s')))
      (fun e => (d.spec r).Post (env, s) pre (.inl e)) L env s :=
  @fun _ F _ stops limit cont done =>
    Diagram.evidenceAt r L limit n d env s pre within cont fun m =>
      Sum.casesOn
        (motive := fun m => (d.spec r).Post (env, s) pre m → FreeDep r F (Free.resume cont m))
        m (fun e run => FreeDep.pure (Q := F) (value := Sum.inl e) (stops e run))
        (fun y run => done y.1 y.2 run)

/-! ### The verified diagram -/

/-- The evidence of a diagram for other conditions, from a map of the conditions. -/
def Diagram.StateDep.imp {n : Nat} {Γ : List Ty} {Qs : Exits Ty} {P P' : Qs.At X → R → Type}
    {Z Z' : E → Type} {L : R → Type} {d : Diagram S Γ Qs} {env : All X Γ} {s : R}
    (f : (x : Qs.At X) → (s' : R) → P x s' → P' x s') (g : (e : E) → Z e → Z' e)
    (dep : d.StateDep r n P Z L env s) : d.StateDep r n P' Z' L env s :=
  fun stops limit _ done =>
    dep (fun e z => stops e (g e z)) limit (fun x s' p => done x s' (f x s' p))

/-- A verified diagram, for a specification of its interface with a runtime: a map into the
specification of the diagram. At each input with a witness of the precondition of the
specification, it has a witness of the precondition of the diagram, and the postcondition of
the specification at the result of each run over that witness. -/
abbrev Diagram.Verified {Γ : List Ty} {Qs : Exits Ty}
    (q : DepPoly.{0, 0, 0, 0} ((Diagram.interface X Γ Qs).runtime R E)) (d : Diagram S Γ Qs) :
    Type 1 :=
  (a : All X Γ × R) → (pre : q.Pre a) →
    (w : (d.spec r).Pre a) × ((o : E ⊕ (Qs.At X × R)) → (d.spec r).Post a w o → q.Post a pre o)

/-- The bound of a verified diagram, for a number of unrollings and a condition at the limit:
the bound of the diagram over each of its witnesses. -/
abbrev Diagram.Verified.Bounded {Γ : List Ty} {Qs : Exits Ty}
    {q : DepPoly.{0, 0, 0, 0} ((Diagram.interface X Γ Qs).runtime R E)} {d : Diagram S Γ Qs}
    (v : d.Verified r q) (n : Nat) : Type :=
  (a : All X Γ × R) → (pre : q.Pre a) → d.Within r L n a (v a pre).1

/-- A verified diagram has the lift of a diagram with a runtime for each number of unrollings,
with no condition at the limit. -/
def Diagram.Verified.stateLift {Γ : List Ty} {Qs : Exits Ty}
    {q : DepPoly.{0, 0, 0, 0} ((Diagram.interface X Γ Qs).runtime R E)} {d : Diagram S Γ Qs}
    (v : d.Verified r q) (n : Nat) : d.StateLift r n q (fun _ _ _ => PUnit) :=
  fun env s pre =>
    Diagram.StateDep.imp r (fun x s' run => (v (env, s) pre).2 (.inr (x, s')) run)
      (fun e run => (v (env, s) pre).2 (.inl e) run)
      (Diagram.verified r n d env s (v (env, s) pre).1)

/-- A verified diagram with a bound has the lift of a diagram with a runtime, with the
condition of the bound at the limit. -/
def Diagram.Verified.stateLiftAt {Γ : List Ty} {Qs : Exits Ty}
    {q : DepPoly.{0, 0, 0, 0} ((Diagram.interface X Γ Qs).runtime R E)} {d : Diagram S Γ Qs}
    (v : d.Verified r q) (n : Nat) (bound : v.Bounded r L n) :
    d.StateLift r n q (fun _ _ => L) :=
  fun env s pre =>
    Diagram.StateDep.imp r (fun x s' run => (v (env, s) pre).2 (.inr (x, s')) run)
      (fun e run => (v (env, s) pre).2 (.inl e) run)
      (Diagram.verifiedAt r L n d env s (v (env, s) pre).1 (bound (env, s) pre))

end Draft

#print axioms Draft.Diagram.verified
#print axioms Draft.Diagram.StateDep.toEvidence
#print axioms Draft.Diagram.Verified.stateLift
#print axioms Draft.Diagram.Verified.stateLiftAt

/-! ### The graph of a machine -/

namespace Draft

section Graph

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  (m : Machine (S.interface X) R E) {Γ : List Ty} {Qs : Exits Ty}
  (call : (S.interface (Port Γ)).Shape)
  (next : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs) (a : All X Γ × R)

abbrev StepPre : E ⊕ ((S.output call.1).At X × R) → Type 1 :=
  Spec.resumePre fun (y : (S.output call.1).At X × R) =>
    ((next y.1.1).spec m.graph).Pre (y.1.2.append a.1, y.2)

abbrev StepPost (x : E ⊕ ((S.output call.1).At X × R)) (p : StepPre m call next a x)
    (o : E ⊕ (Qs.At X × R)) : Type :=
  Spec.resumePost
    (fun (y : (S.output call.1).At X × R) p o =>
      ((next y.1.1).spec m.graph).Post (y.1.2.append a.1, y.2) p o) x p o

/-- For the graph of a machine, a witness of the precondition of a step is a witness of the
precondition after the response of the machine. -/
def stepPre (h : StepPre m call next a (m (⟨call.1, a.1.select call.2⟩, a.2))) :
    ((Diagram.step call next).spec m.graph).Pre a :=
  ⟨PUnit.unit, fun _ e => Identity.transport (StepPre m call next a) e h⟩

/-- For the graph of a machine, a run of a step over that witness is a run after the response
of the machine. -/
def stepPost (h : StepPre m call next a (m (⟨call.1, a.1.select call.2⟩, a.2)))
    (o : E ⊕ (Qs.At X × R))
    (run : ((Diagram.step call next).spec m.graph).Post a
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
    (a : All X Γ × R) → (d.spec m.graph).Pre a
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
              Spec.exitPre (fun k => (next.spec m.graph).Pre (k, y.2)) y.1) x)
          x (fun _ => PUnit.unit)
          (fun y =>
            Exits.At.cases
              (motive := fun e =>
                Spec.exitPre (fun k => (next.spec m.graph).Pre (k, y.2)) e)
              (fun k => Continuation.graphWitness next (k, y.2)) (fun _ => PUnit.unit) y.1)⟩

def Continuation.graphWitness : {P : Boundary Ty} → {Qs : Exits Ty} →
    (k : Continuation S P Qs) → (a : P.At X × R) → (k.spec m.graph).Pre a
  | _, _, .copair each, a => Diagram.graphWitness (each a.1.1) (a.1.2, a.2)
  | _, _, .frame (K := K) kept args shared next, a =>
      ⟨Diagram.graphWitness shared (a.1.2.select (args a.1.1), a.2), fun x _ =>
        Sum.casesOn
          (motive := fun x =>
            Spec.resumePre (fun (y : Exits.At [K] X × R) =>
              Spec.exitPre (fun out =>
                (next.spec m.graph).Pre
                  (⟨Boundary.pair (kept a.1.1).1 out.1,
                    out.2.append (a.1.2.select (kept a.1.1).2)⟩, y.2)) y.1) x)
          x (fun _ => PUnit.unit)
          (fun y =>
            Exits.At.cases
              (motive := fun e =>
                Spec.exitPre (fun out =>
                  (next.spec m.graph).Pre
                    (⟨Boundary.pair (kept a.1.1).1 out.1,
                      out.2.append (a.1.2.select (kept a.1.1).2)⟩, y.2)) e)
              (fun out => Continuation.graphWitness next _) (fun _ => PUnit.unit) y.1)⟩
  | _, _, .loop body, _ =>
      ⟨fun _ => PUnit, PUnit.unit, fun a' _ =>
        ⟨Continuation.graphWitness body a', fun _ _ => PUnit.unit⟩⟩

end

variable (L : R → Type) (n : Nat) {Γ : List Ty} {Qs : Exits Ty}
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

def witN (c a s : Nat) : (loopN.spec G).Pre (entry c a, s) :=
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
    (run : (bodyN.spec G).Post (entry (c + 1) a, s)
      (Continuation.graphWitness machine bodyN (entry (c + 1) a, s)) m) :
    (Sum.inr (Exits.At.here (entry c (s + a)), s + 1) :
      Unit ⊕ (Exits.At [Entry, Out] Value × Nat)) ≡ m :=
  stepPost machine ⟨.emit, .cons (.there (.there .here)) .nil⟩ afterEmit
    (.cons c (inputs (c + 1) a), s) _ m
    (stepPost machine ⟨.pred, .cons .here .nil⟩ afterPred (inputs (c + 1) a, s) _ m
      (stepPost machine ⟨.isZero, .cons .here .nil⟩ afterTest (inputs (c + 1) a, s) _ m run))

set_option smartUnfolding false in
/-- Each run of the body from the counter zero is the exit of the loop. -/
def bodyDone (a s : Nat) (m : Unit ⊕ (Exits.At [Entry, Out] Value × Nat))
    (run : (bodyN.spec G).Post (entry 0 a, s)
      (Continuation.graphWitness machine bodyN (entry 0 a, s)) m) :
    (Sum.inr ((out a).there Entry, s) : Unit ⊕ (Exits.At [Entry, Out] Value × Nat)) ≡ m :=
  stepPost machine ⟨.isZero, .cons .here .nil⟩ afterTest (inputs 0 a, s) _ m run

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

/-- The evidence of the loop with the empty condition at the limit. -/
def evidenceN (c a s : Nat) :
    loopN.StateDep G (c + 1)
      (fun x s' => (loopN.spec G).Post (entry c a, s) (witN c a s) (.inr (x, s')))
      (fun e => (loopN.spec G).Post (entry c a, s) (witN c a s) (.inl e)) Never (entry c a) s :=
  Continuation.verifiedAt G Never (c + 1) loopN (entry c a) s (witN c a s) (bound (c + 1) c a s)

/-- The result of the function meaning on the machine has a run of the loop, for an arbitrary
computation at the limit. -/
def resultRun (stop : Free (sig.interface Value) (Exits.At [Out] Value)) (c a s : Nat) :
    (loopN.spec G).Post (entry c a, s) (witN c a s)
      (((loopN.run stop (c + 1) (entry c a) .pure).thread s).run machine) :=
  FreeDep.run (Section.graphEvidence machine)
    (evidenceN c a s
      (F := fun o => (loopN.spec G).Post (entry c a, s) (witN c a s) o)
      (stop := stop) (cont := .pure) (fun _ z => z) (fun _ e => nomatch e)
      (fun x s' p =>
        FreeDep.pure (Q := fun o => (loopN.spec G).Post (entry c a, s) (witN c a s) o)
          (value := Sum.inr (x, s')) p))

def lengthAt {c a s : Nat} {o : Unit ⊕ (Exits.At [Out] Value × Nat)}
    (run : (loopN.spec G).Post (entry c a, s) (witN c a s) o) : Nat :=
  Loop.length (F := (iterSpec G bodyN).iterate keepsN) run

set_option smartUnfolding false in
/-- From the counter 2 with three unrollings, the run has three runs of the body, for an
arbitrary computation at the limit, an arbitrary value, and an arbitrary runtime. -/
def limitFree (stop : Free (sig.interface Value) (Exits.At [Out] Value)) (a s : Nat) :
    lengthAt (resultRun stop 2 a s) ≡ 3 := .refl

end Draft.Checks.Specification

#print axioms Draft.Checks.Specification.limitFree

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

def witNested (c a s : Nat) : (nested.spec G).Pre (entry c a, s) :=
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
      .inr (value (s + a), s + 1), .refl, .refl⟩

set_option smartUnfolding false in
/-- A run of the inner loop to the exit of the outer loop. -/
def innerEnds (a s : Nat) :
    Loop StepInner ⟨(entry 0 a, s), PUnit.unit⟩ (.inr (Exits.At.there Entry (out a), s)) :=
  .exit ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s), .refl, .refl⟩

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

#print axioms Draft.Checks.Specification.thresholdNested

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

#print axioms Draft.Checks.Specification.roundTripNested

/-! ### The exit equations and the loop law -/

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  (r : DepPoly.{0, 0, 0, 0} ((S.interface X).runtime R E))
  {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty}

/-- The first exit equation, for the witnesses: a witness of the composite of an exit to the
boundary of a continuation and that continuation gives a witness of the continuation at the
case of the exit. -/
def Diagram.exitSeqPre (out : K.At (Port Γ)) (next : Continuation S K Qs) (a : All X Γ × R)
    (pre : ((Diagram.seq (.exit (Exits.At.here out)) next).spec r).Pre a) :
    (next.spec r).Pre (⟨out.1, a.1.select out.2⟩, a.2) :=
  pre.2 (.inr ((Exits.At.here out).select a.1, a.2)) .refl

/-- A witness of the continuation at the case of the exit gives a witness of the composite. -/
def Diagram.exitSeqPreInv (out : K.At (Port Γ)) (next : Continuation S K Qs) (a : All X Γ × R)
    (w : (next.spec r).Pre (⟨out.1, a.1.select out.2⟩, a.2)) :
    ((Diagram.seq (.exit (Exits.At.here out)) next).spec r).Pre a :=
  ⟨PUnit.unit, fun m e =>
    Identity.transport
      (fun m => Spec.resumePre (fun (y : Exits.At (K :: Qs) X × R) =>
        Spec.exitPre (fun k => (next.spec r).Pre (k, y.2)) y.1) m) e w⟩

/-- A witness of the continuation, as a witness of the composite and then as a witness of the
continuation, is the first witness. The identity holds by computation. -/
def Diagram.exitSeqPreRound (out : K.At (Port Γ)) (next : Continuation S K Qs)
    (a : All X Γ × R) (w : (next.spec r).Pre (⟨out.1, a.1.select out.2⟩, a.2)) :
    Diagram.exitSeqPre r out next a (Diagram.exitSeqPreInv r out next a w) ≡ w := .refl

/-- The first exit equation, for the runs over a witness: the runs of the composite are the
runs of the continuation at the case of the exit, with the two round trips. -/
def Diagram.exitSeqSpecRuns (out : K.At (Port Γ)) (next : Continuation S K Qs) (a : All X Γ × R)
    (pre : ((Diagram.seq (.exit (Exits.At.here out)) next).spec r).Pre a)
    (o : E ⊕ (Qs.At X × R)) :
    Iso (((Diagram.seq (.exit (Exits.At.here out)) next).spec r).Post a pre o)
      ((next.spec r).Post (⟨out.1, a.1.select out.2⟩, a.2) (Diagram.exitSeqPre r out next a pre)
        o) :=
  Identity.contract
    (x₀ := (Sum.inr ((Exits.At.here out).select a.1, a.2) : E ⊕ (Exits.At (K :: Qs) X × R)))
    (fun m e =>
      Spec.resumePost
        (fun (y : Exits.At (K :: Qs) X × R) p o =>
          Spec.atExit (fun k => (next.spec r).Pre (k, y.2))
            (fun k p o => (next.spec r).Post (k, y.2) p o)
            (fun q o => (Sum.inr (q, y.2) : E ⊕ (Qs.At X × R)) ≡ o) y.1 p o)
        m (pre.2 m e) o)

/-- The second exit equation, for the runs over a witness: the runs of the composite of an exit
past a continuation and that continuation are the runs of that exit, with the two round
trips. -/
def Diagram.exitPastSpecRuns (out : Qs.At (Port Γ)) (next : Continuation S K Qs) (a : All X Γ × R)
    (pre : ((Diagram.seq (.exit (out.there K)) next).spec r).Pre a) (o : E ⊕ (Qs.At X × R)) :
    Iso (((Diagram.seq (.exit (out.there K)) next).spec r).Post a pre o)
      (((Diagram.exit (S := S) out).spec r).Post a PUnit.unit o) :=
  Identity.contract
    (x₀ := (Sum.inr ((out.there K).select a.1, a.2) : E ⊕ (Exits.At (K :: Qs) X × R)))
    (fun m e =>
      Spec.resumePost
        (fun (y : Exits.At (K :: Qs) X × R) p o =>
          Spec.atExit (fun k => (next.spec r).Pre (k, y.2))
            (fun k p o => (next.spec r).Post (k, y.2) p o)
            (fun q o => (Sum.inr (q, y.2) : E ⊕ (Qs.At X × R)) ≡ o) y.1 p o)
        m (pre.2 m e) o)

/-- The runs of a loop over a witness are the runs of the loop of its iterations on the
entrances with the invariant. The identity holds by computation. -/
def Continuation.loopSpecRuns (body : Continuation S K (K :: Qs)) (a : K.At X × R)
    (w : ((Continuation.loop body).spec r).Pre a) (o : E ⊕ (Qs.At X × R)) :
    ((Continuation.loop body).spec r).Post a w o ≡
      Loop ((iterSpec r body).iterate w.2.2) ⟨a, w.2.1⟩ o :=
  .refl

end Draft

#print axioms Draft.Diagram.exitSeqSpecRuns
#print axioms Draft.Diagram.exitPastSpecRuns

/-! The checks on the countdown loop, for an arbitrary value and an arbitrary runtime: the first
exit equation at the run of the whole diagram, and the unrolling law and the fixpoint law of the
loop at the run from the counter 2. -/

namespace Draft.Checks.Specification.ExitEquations

open Draft Draft.Checks.Countdown Draft.Checks.Specification

/-- The witness of the whole diagram from the counter 2, from the witness of the loop. -/
def whole (a s : Nat) : (countdown.spec G).Pre (inputs 2 a, s) :=
  Diagram.exitSeqPreInv G ⟨Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩ loop
    (inputs 2 a, s) (wit 2 a s)

/-- The run of the whole diagram over that witness: the exit to the entrance, and the run of
the loop. -/
def fromTwo (a s : Nat) : (countdown.spec G).Post (inputs 2 a, s) (whole a s)
    (.inr (runsS 2 a s).1) :=
  ⟨.inr (Exits.At.here (entry 2 a), s), .refl, (runsS 2 a s).2⟩

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

#print axioms Draft.Checks.Specification.ExitEquations.loopOfWhole
#print axioms Draft.Checks.Specification.ExitEquations.loopOfWholeBack
#print axioms Draft.Checks.Specification.ExitEquations.unrolledLength
#print axioms Draft.Checks.Specification.ExitEquations.unrolledBack
#print axioms Draft.Checks.Specification.ExitEquations.fixpointBack

/-! ### A derivation gives a cartesian map of specifications -/

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}

/-- A cartesian map of specifications of one interface: a witness of the first precondition
gives a witness of the second, and the runs over the second witness are the runs over the
first, as an equivalence with its two round trips. -/
abbrev Spec.Cartesian {A B : Type} (P Q : Spec A B) : Type 1 :=
  (a : A) → (pre : P.Pre a) → (w : Q.Pre a) × ((o : B) → Iso (Q.Post a w o) (P.Post a pre o))

/-- The identity map of a specification is cartesian. -/
def Spec.Cartesian.id {A B : Type} (P : Spec A B) : Spec.Cartesian P P :=
  fun _ pre => ⟨pre, fun _ => Iso.refl _⟩

/-- The composite of two cartesian maps. -/
def Spec.Cartesian.comp {A B : Type} {P Q T : Spec A B} (f : Spec.Cartesian P Q)
    (g : Spec.Cartesian Q T) : Spec.Cartesian P T :=
  fun a pre => ⟨(g a (f a pre).1).1, fun o => ((g a (f a pre).1).2 o).trans ((f a pre).2 o)⟩

/-- A cartesian map in each direction. -/
abbrev Spec.Equiv {A B : Type} (P Q : Spec A B) : Type 1 :=
  Spec.Cartesian P Q × Spec.Cartesian Q P

/-- The identity maps. -/
def Spec.Equiv.refl {A B : Type} (P : Spec A B) : Spec.Equiv P P := ⟨.id P, .id P⟩

/-- The two maps in the other order. -/
def Spec.Equiv.symm {A B : Type} {P Q : Spec A B} (f : Spec.Equiv P Q) : Spec.Equiv Q P :=
  ⟨f.2, f.1⟩

/-- The composites of the maps of two pairs. -/
def Spec.Equiv.trans {A B : Type} {P Q T : Spec A B} (f : Spec.Equiv P Q) (g : Spec.Equiv Q T) :
    Spec.Equiv P T :=
  ⟨f.1.comp g.1, g.2.comp f.2⟩

section Resume

variable {M B : Type} {P P' : M → Type 1}

/-- A map of the witnesses after a response gives a map of the witnesses after a result with a
stop. -/
def Spec.resumeMapPre (f : (m : M) → P m → P' m) :
    (x : E ⊕ M) → Spec.resumePre (E := E) P x → Spec.resumePre (E := E) P' x
  | .inl _, p => p
  | .inr m, p => f m p

/-- An equivalence of the runs after a response, over the map of the witnesses, gives an
equivalence of the runs after a result with a stop. -/
def Spec.resumeIso {G : (m : M) → P m → E ⊕ B → Type} {G' : (m : M) → P' m → E ⊕ B → Type}
    (f : (m : M) → P m → P' m)
    (g : (m : M) → (p : P m) → (o : E ⊕ B) → Iso (G' m (f m p) o) (G m p o)) :
    (x : E ⊕ M) → (p : Spec.resumePre (E := E) P x) → (o : E ⊕ B) →
    Iso (Spec.resumePost G' x (Spec.resumeMapPre f x p) o) (Spec.resumePost G x p o)
  | .inl _, _, _ => Iso.refl _
  | .inr m, p, o => g m p o

end Resume

section Exit

variable {K : Boundary Ty} {Qs : Exits Ty} {B : Type} {H H' : K.At X → Type 1}

/-- A map of the witnesses at the first boundary gives a map of the witnesses at an exit. -/
def Spec.exitMapPre (f : (k : K.At X) → H k → H' k) :
    (x : Exits.At (K :: Qs) X) → Spec.exitPre H x → Spec.exitPre H' x :=
  Exits.At.cases (motive := fun x => Spec.exitPre H x → Spec.exitPre H' x) f (fun _ p => p)

/-- An equivalence of the runs at the first boundary, over the map of the witnesses, gives an
equivalence of the runs at an exit. -/
def Spec.exitIso {G : (k : K.At X) → H k → B → Type} {G' : (k : K.At X) → H' k → B → Type}
    {T : Qs.At X → B → Type} (f : (k : K.At X) → H k → H' k)
    (g : (k : K.At X) → (p : H k) → (o : B) → Iso (G' k (f k p) o) (G k p o)) :
    (x : Exits.At (K :: Qs) X) → (p : Spec.exitPre H x) → (o : B) →
    Iso (Spec.atExit H' G' T x (Spec.exitMapPre f x p) o) (Spec.atExit H G T x p o) :=
  Exits.At.cases
    (motive := fun x => (p : Spec.exitPre H x) → (o : B) →
      Iso (Spec.atExit H' G' T x (Spec.exitMapPre f x p) o) (Spec.atExit H G T x p o))
    g (fun _ _ _ => Iso.refl _)

end Exit

/-- A cartesian map of the bodies gives a cartesian map of the loops, with the same invariant.
The equivalence of the runs is one application of the agreement of the loops of two bodies
that agree. -/
def Spec.loopCartesian {A B : Type} {F F' : Spec A (B ⊕ A)} (f : Spec.Cartesian F F') :
    Spec.Cartesian F.loopInv F'.loopInv :=
  fun _ w =>
    let keeps' : F'.Keeps w.1 := fun a i =>
      ⟨(f a (w.2.2 a i).1).1, fun a' post =>
        (w.2.2 a i).2 a' (((f a (w.2.2 a i).1).2 (.inr a')).to post)⟩
    ⟨⟨w.1, w.2.1, keeps'⟩, fun o =>
      Loop.agreement (F := F'.iterate keeps') (G := F.iterate w.2.2)
        (fun y t =>
          match t with
          | .inl b => (f y.1 (w.2.2 y.1 y.2).1).2 (.inl b)
          | .inr y' =>
              Iso.sigmaBase ((f y.1 (w.2.2 y.1 y.2).1).2 (.inr y'.1))
                (fun post => (w.2.2 y.1 y.2).2 y'.1 post ≡ y'.2))
        _ o⟩

variable (r : DepPoly.{0, 0, 0, 0} ((S.interface X).runtime R E))

section Forms

variable {Γ : List Ty} {Qs : Exits Ty}

/-- A cartesian map for the diagram of each response gives a cartesian map of the steps. -/
def Diagram.stepCartesian (call : (S.interface (Port Γ)).Shape)
    {rest rest' : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs}
    (each : (c : (S.output call.1).Case) → Spec.Cartesian ((rest c).spec r) ((rest' c).spec r)) :
    Spec.Cartesian ((Diagram.step call rest).spec r) ((Diagram.step call rest').spec r) :=
  fun a pre =>
    ⟨⟨pre.1, fun x post =>
        Spec.resumeMapPre
          (fun (y : (S.output call.1).At X × R) p => (each y.1.1 (y.1.2.append a.1, y.2) p).1)
          x (pre.2 x post)⟩,
      fun o =>
        Iso.sigmaFiber fun x => Iso.sigmaFiber fun post =>
          Spec.resumeIso
            (fun (y : (S.output call.1).At X × R) p => (each y.1.1 (y.1.2.append a.1, y.2) p).1)
            (fun y p o => (each y.1.1 (y.1.2.append a.1, y.2) p).2 o)
            x (pre.2 x post) o⟩

/-- A cartesian map for the first diagram and a cartesian map for the continuation give a
cartesian map of the composites. -/
def Diagram.seqCartesian {K : Boundary Ty} {first first' : Diagram S Γ (K :: Qs)}
    {next next' : Continuation S K Qs} (head : Spec.Cartesian (first.spec r) (first'.spec r))
    (tail : Spec.Cartesian (next.spec r) (next'.spec r)) :
    Spec.Cartesian ((Diagram.seq first next).spec r) ((Diagram.seq first' next').spec r) :=
  fun a pre =>
    ⟨⟨(head a pre.1).1, fun m post =>
        Spec.resumeMapPre
          (fun (y : Exits.At (K :: Qs) X × R) p =>
            Spec.exitMapPre (fun k p => (tail (k, y.2) p).1) y.1 p)
          m (pre.2 m (((head a pre.1).2 m).to post))⟩,
      fun o =>
        Iso.sigmaFiber fun m =>
          Iso.sigma ((head a pre.1).2 m) fun post =>
            Spec.resumeIso
              (fun (y : Exits.At (K :: Qs) X × R) p =>
                Spec.exitMapPre (fun k p => (tail (k, y.2) p).1) y.1 p)
              (fun y p o =>
                Spec.exitIso (T := fun q o => (Sum.inr (q, y.2) : E ⊕ (Qs.At X × R)) ≡ o)
                  (fun k p => (tail (k, y.2) p).1)
                  (fun k p o => (tail (k, y.2) p).2 o) y.1 p o)
              m (pre.2 m (((head a pre.1).2 m).to post)) o⟩

end Forms

section Forms

variable {P : Boundary Ty} {Qs : Exits Ty}

/-- A cartesian map for the diagram of each case gives a cartesian map of the copairings. -/
def Continuation.copairCartesian {each each' : (c : P.Case) → Diagram S c.1 Qs}
    (cases : (c : P.Case) → Spec.Cartesian ((each c).spec r) ((each' c).spec r)) :
    Spec.Cartesian ((Continuation.copair each).spec r) ((Continuation.copair each').spec r) :=
  fun a pre => cases a.1.1 (a.1.2, a.2) pre

/-- A cartesian map for the body gives a cartesian map of the loops. -/
def Continuation.loopCartesian {body body' : Continuation S P (P :: Qs)}
    (same : Spec.Cartesian (body.spec r) (body'.spec r)) :
    Spec.Cartesian ((Continuation.loop body).spec r) ((Continuation.loop body').spec r) :=
  Spec.loopCartesian (F := iterSpec r body) (F' := iterSpec r body')
    fun a pre => ⟨(same a pre).1, fun t => (same a pre).2 (unresult t)⟩

end Forms

section Frame

variable {M K : Boundary Ty} {Qs : Exits Ty} {Δ c : List Ty}

/-- The precondition of a frame at the values of a case, with the kept ports and the port map
of that case as arguments. -/
abbrev FramePre (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs)
    (vals : All X c) (s : R) (kp : M.At (Port c)) (ag : PortMap c Δ) : Type 1 :=
  (p : (shared.spec r).Pre (vals.select ag, s)) ×
    ((m : E ⊕ (Exits.At [K] X × R)) → (shared.spec r).Post (vals.select ag, s) p m →
      Spec.resumePre (fun (y : Exits.At [K] X × R) =>
        Spec.exitPre (fun out =>
          (next.spec r).Pre
            (⟨Boundary.pair kp.1 out.1, out.2.append (vals.select kp.2)⟩, y.2)) y.1) m)

/-- The runs of a frame at the values of a case, over a witness. -/
abbrev FramePost (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs)
    (vals : All X c) (s : R) (kp : M.At (Port c)) (ag : PortMap c Δ)
    (pre : FramePre r shared next vals s kp ag) (o : E ⊕ (Qs.At X × R)) : Type :=
  (m : E ⊕ (Exits.At [K] X × R)) × (post : (shared.spec r).Post (vals.select ag, s) pre.1 m) ×
    Spec.resumePost
      (fun (y : Exits.At [K] X × R) p o =>
        Spec.atExit
          (fun out =>
            (next.spec r).Pre
              (⟨Boundary.pair kp.1 out.1, out.2.append (vals.select kp.2)⟩, y.2))
          (fun out p o =>
            (next.spec r).Post
              (⟨Boundary.pair kp.1 out.1, out.2.append (vals.select kp.2)⟩, y.2) p o)
          (fun q _ => Exits.At.ofNil q) y.1 p o)
      m (pre.2 m post) o

variable {shared shared' : Diagram S Δ [K]} {next next' : Continuation S (M.product K) Qs}

/-- A cartesian map for the diagram of a frame and a cartesian map for its continuation give a
cartesian map at the values of a case, for one choice of the kept ports and of the port map. -/
def frameCartesianAt (body : Spec.Cartesian (shared.spec r) (shared'.spec r))
    (tail : Spec.Cartesian (next.spec r) (next'.spec r)) (vals : All X c) (s : R)
    (kp : M.At (Port c)) (ag : PortMap c Δ) (pre : FramePre r shared next vals s kp ag) :
    (w : FramePre r shared' next' vals s kp ag) ×
      ((o : E ⊕ (Qs.At X × R)) →
        Iso (FramePost r shared' next' vals s kp ag w o)
          (FramePost r shared next vals s kp ag pre o)) :=
  ⟨⟨(body _ pre.1).1, fun m post =>
      Spec.resumeMapPre
        (fun (y : Exits.At [K] X × R) p =>
          Spec.exitMapPre (fun _ p => (tail (_, y.2) p).1) y.1 p)
        m (pre.2 m (((body _ pre.1).2 m).to post))⟩,
    fun o =>
      Iso.sigmaFiber fun m =>
        Iso.sigma ((body _ pre.1).2 m) fun post =>
          Spec.resumeIso
            (fun (y : Exits.At [K] X × R) p =>
              Spec.exitMapPre (fun _ p => (tail (_, y.2) p).1) y.1 p)
            (fun y p o =>
              Spec.exitIso (T := fun q _ => Exits.At.ofNil q)
                (fun _ p => (tail (_, y.2) p).1)
                (fun _ p o => (tail (_, y.2) p).2 o) y.1 p o)
            m (pre.2 m (((body _ pre.1).2 m).to post)) o⟩

/-- A cartesian map for the diagram of a frame and a cartesian map for its continuation give a
cartesian map of the frames. The kept ports and the port maps of the two frames are identical
at each case. -/
def Continuation.frameCartesian {P : Boundary Ty} {kept kept' : (c : P.Case) → M.At (Port c.1)}
    {args args' : (c : P.Case) → PortMap c.1 Δ}
    (keptSame : (c : P.Case) → kept c ≡ kept' c) (argsSame : (c : P.Case) → args c ≡ args' c)
    (body : Spec.Cartesian (shared.spec r) (shared'.spec r))
    (tail : Spec.Cartesian (next.spec r) (next'.spec r)) :
    Spec.Cartesian ((Continuation.frame kept args shared next).spec r)
      ((Continuation.frame kept' args' shared' next').spec r) :=
  fun a pre =>
    Identity.transport
      (fun kp' =>
        (w : FramePre r shared' next' a.1.2 a.2 kp' (args' a.1.1)) ×
          ((o : E ⊕ (Qs.At X × R)) →
            Iso (FramePost r shared' next' a.1.2 a.2 kp' (args' a.1.1) w o)
              (FramePost r shared next a.1.2 a.2 (kept a.1.1) (args a.1.1) pre o)))
      (keptSame a.1.1)
      (Identity.transport
        (fun ag' =>
          (w : FramePre r shared' next' a.1.2 a.2 (kept a.1.1) ag') ×
            ((o : E ⊕ (Qs.At X × R)) →
              Iso (FramePost r shared' next' a.1.2 a.2 (kept a.1.1) ag' w o)
                (FramePost r shared next a.1.2 a.2 (kept a.1.1) (args a.1.1) pre o)))
        (argsSame a.1.1) (frameCartesianAt r body tail a.1.2 a.2 (kept a.1.1) (args a.1.1) pre))

end Frame

mutual

/-- Two diagrams that agree have a cartesian map of their specifications in each direction. -/
def Diagram.Agreement.spec : {Γ : List Ty} → {Qs : Exits Ty} → {d e : Diagram S Γ Qs} →
    Diagram.Agreement d e → Spec.Equiv (d.spec r) (e.spec r)
  | _, _, _, _, .exit _ => .refl _
  | _, _, _, _, .step call each =>
      ⟨Diagram.stepCartesian r call fun c => (Diagram.Agreement.spec (each c)).1,
        Diagram.stepCartesian r call fun c => (Diagram.Agreement.spec (each c)).2⟩
  | _, _, _, _, .seq head tail =>
      ⟨Diagram.seqCartesian r (Diagram.Agreement.spec head).1 (Continuation.Agreement.spec tail).1,
        Diagram.seqCartesian r (Diagram.Agreement.spec head).2
          (Continuation.Agreement.spec tail).2⟩

def Continuation.Agreement.spec : {P : Boundary Ty} → {Qs : Exits Ty} →
    {k k' : Continuation S P Qs} → Continuation.Agreement k k' →
    Spec.Equiv (k.spec r) (k'.spec r)
  | _, _, _, _, .copair cases =>
      ⟨Continuation.copairCartesian r fun c => (Diagram.Agreement.spec (cases c)).1,
        Continuation.copairCartesian r fun c => (Diagram.Agreement.spec (cases c)).2⟩
  | _, _, _, _, .frame keptSame argsSame body tail =>
      ⟨Continuation.frameCartesian r keptSame argsSame (Diagram.Agreement.spec body).1
          (Continuation.Agreement.spec tail).1,
        Continuation.frameCartesian r (fun c => (keptSame c).symm) (fun c => (argsSame c).symm)
          (Diagram.Agreement.spec body).2 (Continuation.Agreement.spec tail).2⟩
  | _, _, _, _, .loop same =>
      ⟨Continuation.loopCartesian r (Continuation.Agreement.spec same).1,
        Continuation.loopCartesian r (Continuation.Agreement.spec same).2⟩

end

/-- Each rule of the set has a cartesian map of the specifications of its two sides, in each
direction. -/
structure Rules.SpecSound (T : Rules S) where
  diagram : {Γ : List Ty} → {Qs : Exits Ty} → {d e : Diagram S Γ Qs} → T.diagram d e →
    Spec.Equiv (d.spec r) (e.spec r)
  continuation : {P : Boundary Ty} → {Qs : Exits Ty} → {k k' : Continuation S P Qs} →
    T.continuation k k' → Spec.Equiv (k.spec r) (k'.spec r)

variable {r} {T : Rules S}

mutual

/-- A derivation gives a cartesian map of the specifications of its two diagrams, in each
direction. -/
def Diagram.Derivation.spec (ok : T.SpecSound r) : {Γ : List Ty} → {Qs : Exits Ty} →
    {d e : Diagram S Γ Qs} → Diagram.Derivation T d e → Spec.Equiv (d.spec r) (e.spec r)
  | _, _, _, _, .agree same => same.spec r
  | _, _, _, _, .rule x => ok.diagram x
  | _, _, _, _, .symm h => (Diagram.Derivation.spec ok h).symm
  | _, _, _, _, .trans h k => (Diagram.Derivation.spec ok h).trans (Diagram.Derivation.spec ok k)
  | _, _, _, _, .step call each =>
      ⟨Diagram.stepCartesian r call fun c => (Diagram.Derivation.spec ok (each c)).1,
        Diagram.stepCartesian r call fun c => (Diagram.Derivation.spec ok (each c)).2⟩
  | _, _, _, _, .seq head tail =>
      ⟨Diagram.seqCartesian r (Diagram.Derivation.spec ok head).1
          (Continuation.Derivation.spec ok tail).1,
        Diagram.seqCartesian r (Diagram.Derivation.spec ok head).2
          (Continuation.Derivation.spec ok tail).2⟩

def Continuation.Derivation.spec (ok : T.SpecSound r) : {P : Boundary Ty} → {Qs : Exits Ty} →
    {k k' : Continuation S P Qs} → Continuation.Derivation T k k' →
    Spec.Equiv (k.spec r) (k'.spec r)
  | _, _, _, _, .agree same => same.spec r
  | _, _, _, _, .rule x => ok.continuation x
  | _, _, _, _, .symm h => (Continuation.Derivation.spec ok h).symm
  | _, _, _, _, .trans h j =>
      (Continuation.Derivation.spec ok h).trans (Continuation.Derivation.spec ok j)
  | _, _, _, _, .copair cases =>
      ⟨Continuation.copairCartesian r fun c => (Diagram.Derivation.spec ok (cases c)).1,
        Continuation.copairCartesian r fun c => (Diagram.Derivation.spec ok (cases c)).2⟩
  | _, _, _, _, .frame _ _ body tail =>
      ⟨Continuation.frameCartesian r (fun _ => .refl) (fun _ => .refl)
          (Diagram.Derivation.spec ok body).1 (Continuation.Derivation.spec ok tail).1,
        Continuation.frameCartesian r (fun _ => .refl) (fun _ => .refl)
          (Diagram.Derivation.spec ok body).2 (Continuation.Derivation.spec ok tail).2⟩
  | _, _, _, _, .loop same =>
      ⟨Continuation.loopCartesian r (Continuation.Derivation.spec ok same).1,
        Continuation.loopCartesian r (Continuation.Derivation.spec ok same).2⟩

end

/-- A verified diagram moves along a derivation. -/
def Diagram.Derivation.verified (ok : T.SpecSound r) {Γ : List Ty} {Qs : Exits Ty}
    {d e : Diagram S Γ Qs} (h : Diagram.Derivation T d e)
    {q : DepPoly.{0, 0, 0, 0} ((Diagram.interface X Γ Qs).runtime R E)} (v : d.Verified r q) :
    e.Verified r q :=
  fun a pre =>
    ⟨((h.spec ok).1 a (v a pre).1).1,
      fun o run => (v a pre).2 o ((((h.spec ok).1 a (v a pre).1).2 o).to run)⟩

end Draft

#print axioms Draft.Diagram.Derivation.spec
#print axioms Draft.Diagram.Derivation.verified

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
      .inr (value (s + a), s + 1), .refl, .refl⟩,
    .refl⟩

set_option smartUnfolding false in
/-- One iteration over the moved witness that exits. -/
def endsM (a s : Nat) : StepM ⟨(entry 0 a, s), PUnit.unit⟩ (.inl (.inr (out a, s))) :=
  ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s), .refl, .refl⟩

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
      .inr (value (s + a), s + 1), .refl, .refl⟩,
    .refl⟩

set_option smartUnfolding false in
/-- One iteration over that witness that exits. -/
def endsOne (a s : Nat) : StepOne ⟨(entry 0 a, s), PUnit.unit⟩ (.inl (.inr (out a, s))) :=
  ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s), .refl, .refl⟩

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
def wholeRun (a s : Nat) : (countdown.spec G).Post (inputs 2 a, s) (movedWhole a s).1
    (.inr (runsOne 2 a s).1) :=
  ⟨.inr (Exits.At.here (entry 2 a), s), .refl, (runsOne 2 a s).2⟩

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

#print axioms Draft.Checks.Specification.movedRun
#print axioms Draft.Checks.Specification.movedBack
#print axioms Draft.Checks.Specification.movedRound
#print axioms Draft.Checks.Specification.roundOne
#print axioms Draft.Checks.Specification.wholeBack
#print axioms Draft.Checks.Specification.wholeRound
#print axioms Draft.Checks.Specification.wholeRoundBack

/-! ### The second exit equation as a rule -/

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  (r : DepPoly.{0, 0, 0, 0} ((S.interface X).runtime R E))
  {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty}

/-- A witness of the composite of an exit past a continuation and that continuation. No run
reaches the continuation, so the witness has no witness of the continuation. -/
def Diagram.exitPastPre (out : Qs.At (Port Γ)) (next : Continuation S K Qs) (a : All X Γ × R) :
    ((Diagram.seq (.exit (out.there K)) next).spec r).Pre a :=
  ⟨PUnit.unit, fun m e =>
    Identity.transport
      (fun m => Spec.resumePre (fun (y : Exits.At (K :: Qs) X × R) =>
        Spec.exitPre (fun k => (next.spec r).Pre (k, y.2)) y.1) m) e PUnit.unit⟩

/-- The rule set with the second exit equation. -/
def Rules.exitPast (S : Signature Ty) : Rules S :=
  ⟨fun d e => Diagram.ExitPast d e, fun _ _ => Empty⟩

/-- The second exit equation has a cartesian map in each direction, for each specification of
the calls. -/
def Rules.exitPastSound : (Rules.exitPast S).SpecSound r where
  diagram x :=
    match x with
    | .exit out next =>
        ⟨fun a pre => ⟨PUnit.unit, fun o => (Diagram.exitPastSpecRuns r out next a pre o).symm⟩,
          fun a _ =>
            ⟨Diagram.exitPastPre r out next a,
              fun o => Diagram.exitPastSpecRuns r out next a (Diagram.exitPastPre r out next a) o⟩⟩
  continuation x := nomatch x

end Draft

#print axioms Draft.Rules.exitPastSound

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
      .inr (value (s + a), s + 1), .refl, .refl⟩,
    .refl⟩

set_option smartUnfolding false in
def endsN (a s : Nat) : StepN ⟨(entry 0 a, s), PUnit.unit⟩ (.inl (.inr (out a, s))) :=
  ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s), .refl, .refl⟩

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
      .inr (value (s + a), s + 1), .refl, .refl⟩,
    .refl⟩

set_option smartUnfolding false in
/-- The iteration that exits has the run of the exit past the continuation. -/
def endsP (a s : Nat) : StepP ⟨(entry 0 a, s), PUnit.unit⟩ (.inl (.inr (out a, s))) :=
  ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s), .refl, _, .refl, .refl⟩

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

#print axioms Draft.Checks.Specification.pastRun
#print axioms Draft.Checks.Specification.pastBack
#print axioms Draft.Checks.Specification.pastRound
#print axioms Draft.Checks.Specification.pastRoundBack

/-! ### The unit runtime -/

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type}

/-- A verified diagram for specifications with no runtime: the verified diagram at the unit
runtime. It has the verified implementation of each approximant. -/
def Diagram.Verified.lift {Γ : List Ty} {Qs : Exits Ty}
    {r₀ : DepPoly.{0, 0, 0, 0} (S.interface X)}
    {q₀ : DepPoly.{0, 0, 0, 0} (Diagram.interface X Γ Qs)} {d : Diagram S Γ Qs}
    (v : d.Verified r₀.still q₀.still) {stop : Free (S.interface X) (Qs.At X)}
    (limit : (env : All X Γ) → (pre : q₀.Pre env) → FreeDep r₀ (q₀.Post env pre) stop)
    (n : Nat) : ImplDep q₀ r₀ (d.impl stop n) :=
  fun env pre =>
    FreeDep.ofStill _
      ((Diagram.Verified.stateLift _ v n).impl
        (fun env _ pre _ _ => FreeDep.toStill stop (limit env pre)) (env, .unit) pre)

end Draft

#print axioms Draft.Diagram.Verified.lift

/-! ### The form of the Prelude, and the constructors of the evidence -/

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  (r : DepPoly.{0, 0, 0, 0} ((S.interface X).runtime R E))

/-- The evidence of a diagram at an input, for a condition at each result of a run. -/
abbrev Diagram.Holds {Γ : List Ty} {Qs : Exits Ty} (P : E ⊕ (Qs.At X × R) → Type)
    (d : Diagram S Γ Qs) (a : All X Γ × R) : Type 1 :=
  FreeDep (d.spec r) P (Free.call (C := ⟨All X Γ × R, fun _ => E ⊕ (Qs.At X × R)⟩) a)

/-- The evidence of a continuation at an input, for a condition at each result of a run. -/
abbrev Continuation.Holds {K : Boundary Ty} {Qs : Exits Ty} (P : E ⊕ (Qs.At X × R) → Type)
    (k : Continuation S K Qs) (a : K.At X × R) : Type 1 :=
  FreeDep (k.spec r) P (Free.call (C := ⟨K.At X × R, fun _ => E ⊕ (Qs.At X × R)⟩) a)

/-- A verified diagram: the verified implementation with one call, to the specification of the
diagram. -/
abbrev Diagram.VerifiedImpl {Γ : List Ty} {Qs : Exits Ty}
    (q : DepPoly.{0, 0, 0, 0} ((Diagram.interface X Γ Qs).runtime R E)) (d : Diagram S Γ Qs) :
    Type 1 :=
  ImplDep q (d.spec r) (Impl.id ⟨All X Γ × R, fun _ => E ⊕ (Qs.At X × R)⟩)

/-- The two forms of a verified diagram give each other. -/
def Diagram.VerifiedImpl.toVerified {Γ : List Ty} {Qs : Exits Ty}
    {q : DepPoly.{0, 0, 0, 0} ((Diagram.interface X Γ Qs).runtime R E)} {d : Diagram S Γ Qs}
    (v : d.VerifiedImpl r q) : d.Verified r q :=
  fun a pre => ⟨(v a pre).parts.1, fun o run => ((v a pre).parts.2 o run).result⟩

/-- The converse. -/
def Diagram.Verified.toVerifiedImpl {Γ : List Ty} {Qs : Exits Ty}
    {q : DepPoly.{0, 0, 0, 0} ((Diagram.interface X Γ Qs).runtime R E)} {d : Diagram S Γ Qs}
    (v : d.Verified r q) : d.VerifiedImpl r q :=
  fun a pre => .request (v a pre).1 fun o run => .pure ((v a pre).2 o run)

section Constructors

variable {r} {Γ : List Ty} {Qs : Exits Ty} {P : E ⊕ (Qs.At X × R) → Type} {env : All X Γ} {s : R}

/-- The evidence of an exit: its condition at the runtime. -/
def Diagram.Holds.exit (out : Qs.At (Port Γ)) (h : P (.inr (out.select env, s))) :
    (Diagram.exit (S := S) out).Holds r P (env, s) :=
  .request PUnit.unit fun _ run => .pure (Identity.transport P run h)

section Step

variable (call : (S.interface (Port Γ)).Shape)
  (rest : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs)
  (admit : r.Pre (⟨call.1, env.select call.2⟩, s))
  (stopped : (e : E) → r.Post (⟨call.1, env.select call.2⟩, s) admit (.inl e) → P (.inl e))
  (next : (y : (S.output call.1).At X × R) →
    r.Post (⟨call.1, env.select call.2⟩, s) admit (.inr y) →
    (rest y.1.1).Holds r P (y.1.2.append env, y.2))

/-- The witness after each response of the call of a step. -/
def Diagram.Holds.stepWitness :
    (x : E ⊕ ((S.output call.1).At X × R)) →
    r.Post (⟨call.1, env.select call.2⟩, s) admit x →
    Spec.resumePre (fun (y : (S.output call.1).At X × R) =>
      ((rest y.1.1).spec r).Pre (y.1.2.append env, y.2)) x
  | .inl _, _ => PUnit.unit
  | .inr y, post => (next y post).parts.1

/-- The condition at the result of each run after a response of the call of a step. -/
def Diagram.Holds.stepResult :
    (x : E ⊕ ((S.output call.1).At X × R)) →
    (post : r.Post (⟨call.1, env.select call.2⟩, s) admit x) → (o : E ⊕ (Qs.At X × R)) →
    Spec.resumePost
      (fun (y : (S.output call.1).At X × R) p o =>
        ((rest y.1.1).spec r).Post (y.1.2.append env, y.2) p o)
      x (Diagram.Holds.stepWitness call rest admit next x post) o → P o
  | .inl e, post, _, run => Identity.transport P run (stopped e post)
  | .inr y, post, o, run => ((next y post).parts.2 o run).result

/-- The evidence of a step: a witness of the precondition of the call at the runtime, the
condition at each stop, and the evidence of the diagram of each response from the next
runtime, which receives the postcondition. -/
def Diagram.Holds.step : (Diagram.step call rest).Holds r P (env, s) :=
  .request ⟨admit, Diagram.Holds.stepWitness call rest admit next⟩ fun o run =>
    .pure (Diagram.Holds.stepResult call rest admit stopped next run.1 run.2.1 o run.2.2)

end Step

/-- The evidence of a step for the graph of a machine, at a call where the machine gives a
response: the evidence of the diagram of that response from its next runtime. -/
def Diagram.Holds.stepResponse (m : Machine (S.interface X) R E)
    (call : (S.interface (Port Γ)).Shape)
    (rest : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs)
    {b : (S.output call.1).At X × R} (known : m (⟨call.1, env.select call.2⟩, s) ≡ .inr b)
    (next : (rest b.1.1).Holds m.graph P (b.1.2.append env, b.2)) :
    (Diagram.step call rest).Holds m.graph P (env, s) :=
  Diagram.Holds.step (r := m.graph) (env := env) (s := s) call rest PUnit.unit
    (fun _ post => (Identity.inrNotInl (known.symm.trans post)).elim)
    (fun _ post =>
      Identity.transport
        (fun (c : (S.output call.1).At X × R) =>
          (rest c.1.1).Holds m.graph P (c.1.2.append env, c.2))
        (Identity.inrInject (known.symm.trans post)) next)

end Constructors

section Constructors

variable {r} {K : Boundary Ty} {Qs : Exits Ty} {P : E ⊕ (Qs.At X × R) → Type}

/-- The evidence of a copairing: the evidence of the diagram of the case. -/
def Continuation.Holds.copair {a : K.At X × R} (each : (c : K.Case) → Diagram S c.1 Qs)
    (h : (each a.1.1).Holds r P (a.1.2, a.2)) : (Continuation.copair each).Holds r P a :=
  .request h.parts.1 fun o run => .pure (h.parts.2 o run).result

/-- The condition at a result of the body of a loop: the condition of the loop at a stop and at
an exit of the loop, and the invariant at the next entrance. -/
def Continuation.Holds.loopCondition (Inv : K.At X × R → Type) (P : E ⊕ (Qs.At X × R) → Type) :
    E ⊕ (Exits.At (K :: Qs) X × R) → Type
  | .inl e => P (.inl e)
  | .inr y => Exits.At.elim (fun k => Inv (k, y.2)) (fun q => P (.inr (q, y.2))) y.1

section Loop

variable (Inv : K.At X × R → Type) (body : Continuation S K (K :: Qs))
  (bodyH : (a : K.At X × R) → Inv a →
    body.Holds r (Continuation.Holds.loopCondition Inv P) a)

/-- The body keeps the invariant. -/
def Continuation.Holds.loopKeeps : (iterSpec r body).Keeps Inv :=
  fun a i => ⟨(bodyH a i).parts.1, fun a' post =>
    ((bodyH a i).parts.2 (.inr (Exits.At.here a'.1, a'.2)) post).result⟩

/-- The condition of the loop at the result of an iteration that ends the loop. -/
def Continuation.Holds.loopExit (x : (a : K.At X × R) × Inv a) :
    (o : E ⊕ (Qs.At X × R)) →
    (iterSpec r body).iterate (Continuation.Holds.loopKeeps Inv body bodyH) x (.inl o) → P o
  | .inl e, post => ((bodyH x.1 x.2).parts.2 (.inl e) post).result
  | .inr y, post => ((bodyH x.1 x.2).parts.2 (.inr (Exits.At.there K y.1, y.2)) post).result

/-- The evidence of a loop, for an invariant at the entrance: the evidence of the body at each
entrance with the invariant, with the invariant at each exit to the entrance. -/
def Continuation.Holds.loop {a : K.At X × R} (start : Inv a) :
    (Continuation.loop body).Holds r P a :=
  .request ⟨Inv, start, Continuation.Holds.loopKeeps Inv body bodyH⟩ fun o run =>
    .pure
      (Loop.elim (R := fun (_ : (a : K.At X × R) × Inv a) (o : E ⊕ (Qs.At X × R)) => P o)
        (fun x _ post => Continuation.Holds.loopExit Inv body bodyH x _ post)
        (fun _ _ _ _ rest => rest) run)

end Loop

end Constructors

end Draft

#print axioms Draft.Diagram.Holds.step
#print axioms Draft.Continuation.Holds.loop

/-! The check on the countdown loop: the runtime at the exit is the runtime at the entrance plus
the counter. The invariant has the sum of the runtime and the counter. -/

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

/-- The evidence of the body at each entrance with the invariant, by the constructors. -/
def bodyHolds : (x : Entry.At Value × Nat) → Inv s₀ c₀ x →
    body.Holds G (Continuation.Holds.loopCondition (Inv s₀ c₀) (Final s₀ c₀)) x
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

/-- The evidence of the loop from each entrance: the runtime at the exit is the runtime at the
entrance plus the counter. -/
def holds (c a s : Nat) : loop.Holds G (Final s c) (entry c a, s) :=
  Continuation.Holds.loop (Inv s c) body (bodyHolds s c) (a := (entry c a, s)) .refl

end Draft.Checks.Specification.Invariant

#print axioms Draft.Checks.Specification.Invariant.holds

namespace Draft.Checks.Specification.Invariant

open Draft Draft.Checks.Countdown Draft.Checks.Specification

variable (a s : Nat)

/-- The witness of the precondition of the loop that the evidence has. -/
def witness : (loop.spec G).Pre (entry 2 a, s) := (holds 2 a s).parts.1

/-- One iteration over that witness. -/
abbrev StepH := (iterSpec G body).iterate (witness a s).2.2

set_option smartUnfolding false in
/-- The first iteration, with the invariant witness at the next entrance. -/
def first : (i : Inv s 2 (entry 1 (s + a), s + 1)) ×
    StepH a s ⟨(entry 2 a, s), (witness a s).2.1⟩ (.inr ⟨(entry 1 (s + a), s + 1), i⟩) :=
  ⟨_, ⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s), .refl, .inr (value 1, s), .refl,
      .inr (value (s + a), s + 1), .refl, .refl⟩, .refl⟩

set_option smartUnfolding false in
/-- The second iteration. -/
def second : (i : Inv s 2 (entry 0 ((s + 1) + (s + a)), s + 2)) ×
    StepH a s ⟨(entry 1 (s + a), s + 1), (first a s).1⟩
      (.inr ⟨(entry 0 ((s + 1) + (s + a)), s + 2), i⟩) :=
  ⟨_, ⟨.inr (⟨⟨_, .there .here⟩, .nil⟩, s + 1), .refl, .inr (value 0, s + 1), .refl,
      .inr (value ((s + 1) + (s + a)), s + 2), .refl, .refl⟩, .refl⟩

set_option smartUnfolding false in
/-- The last iteration: the exit. -/
def last : StepH a s ⟨(entry 0 ((s + 1) + (s + a)), s + 2), (second a s).1⟩
    (.inl (.inr (out ((s + 1) + (s + a)), s + 2))) :=
  ⟨.inr (⟨⟨_, .here⟩, .nil⟩, s + 2), .refl, .refl⟩

/-- The run of the loop over the witness, from the counter 2. -/
def run : (loop.spec G).Post (entry 2 a, s) (witness a s)
    (.inr (out ((s + 1) + (s + a)), s + 2)) :=
  .next (first a s).2 (.next (second a s).2 (.exit (last a s)))

set_option smartUnfolding false in
/-- The condition at the result of the run: the identity of the runtime at the exit with the
runtime at the entrance plus 2, for an arbitrary value and an arbitrary runtime. The evidence
goes through the invariant of each of the two iterations. -/
def runtimeAtExit :
    ((holds 2 a s).parts.2 (.inr (out ((s + 1) + (s + a)), s + 2)) (run a s)).result ≡
      (Identity.refl : s + 2 ≡ s + 2) := .refl

end Draft.Checks.Specification.Invariant

#print axioms Draft.Checks.Specification.Invariant.runtimeAtExit
