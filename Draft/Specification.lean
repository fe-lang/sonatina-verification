import Draft.Diagram

/-! The specification of a diagram, from a specification of its calls with a runtime.

A specification of a computation has a precondition at each input, and the runs to each result
over a witness of the precondition. A response of a call is a response with the next runtime,
or a stop, and a result of a run is an exit with a runtime, or a stop. A witness of the
precondition of a diagram has a witness of the precondition of each call that a run can make.

The precondition of a loop is an invariant: a family on the entrances that the body keeps, with
a witness of the precondition of the body at each entrance of the family. The runs of a loop
are the loop of `Prelude.Relation` on the entrances with the family. One iteration has the
runs of the body at the result that the next entrance, the exit, or the stop names. The
invariant has the universe level of the runs, so the specification of the calls gives the two
universe levels of the specification of a diagram.

The two exit equations hold for the specification. A witness for an exit to the boundary of a
continuation, and then the continuation, gives a witness for the continuation at the case of
the exit, and the converse. Over each witness, the runs of the composite are the runs of the
continuation, as an equivalence with its two round trips. The runs of an exit past a
continuation, and then the continuation, are the runs of that exit. The runs of a loop over a
witness are the loop of its iterations, by computation. -/

set_option autoImplicit false
set_option genInjectivity false

universe w z a b v w' z' c d

open Prelude Container

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}

/-- A specification of a computation from `A` to `B`: a precondition at each input, and the
runs to each result over a witness of the precondition. -/
abbrev Spec (A B : Type) : Type (max (a + 1) (b + 1)) := DepPoly.{0, 0, a, b} ⟨A, fun _ => B⟩

/-- The run that is the identity of a result and the result of the run. -/
abbrev Spec.Result {B : Type} (x o : B) : Type b := ULift.{b} (x ≡ o)

/-- The precondition after a result with a stop: no content at a stop. -/
def Spec.resumePre {M : Type} (P : M → Type a) : E ⊕ M → Type a
  | .inl _ => PUnit
  | .inr m => P m

/-- The runs after a result with a stop: at a stop, the stop is the result. -/
def Spec.resumePost {M B : Type} {P : M → Type a} (G : (m : M) → P m → E ⊕ B → Type b) :
    (x : E ⊕ M) → Spec.resumePre P x → E ⊕ B → Type b
  | .inl e, _, o => Spec.Result (Sum.inl e : E ⊕ B) o
  | .inr m, p, o => G m p o

/-- The case analysis of an exit of a list of boundaries with a first boundary. -/
def Exits.At.cases.{t} {K : Boundary Ty} {Qs : Exits Ty}
    {motive : Exits.At (K :: Qs) X → Type t}
    (head : (k : K.At X) → motive (Exits.At.here k))
    (tail : (q : Qs.At X) → motive (Exits.At.there K q)) (r : Exits.At (K :: Qs) X) : motive r :=
  Elem.consCases
    (motive := fun (Q : Boundary Ty) (i : Elem Q (K :: Qs)) => (q : Q.At X) → motive ⟨Q, i, q⟩)
    r.2.1 head (fun Q j q => tail ⟨Q, j, q⟩) r.2.2

/-- The precondition at an exit: the precondition of the continuation at an exit to its
boundary, and no content at each other exit. -/
abbrev Spec.exitPre {K : Boundary Ty} {Qs : Exits Ty} (headPre : K.At X → Type a) :
    Exits.At (K :: Qs) X → Type a :=
  Exits.At.elim headPre fun _ => PUnit

/-- The runs at an exit: the runs of the continuation at an exit to its boundary, and a given
family at each other exit. -/
def Spec.atExit {K : Boundary Ty} {Qs : Exits Ty} {B : Type} (headPre : K.At X → Type a)
    (headPost : (k : K.At X) → headPre k → B → Type b) (tailPost : Qs.At X → B → Type b) :
    (r : Exits.At (K :: Qs) X) → Spec.exitPre headPre r → B → Type b :=
  Exits.At.cases (motive := fun r => Spec.exitPre headPre r → B → Type b)
    headPost (fun q _ o => tailPost q o)

/-- The result of the body of a loop that a result of an iteration names: a stop, an exit of
the loop, or the next entrance. -/
def unresult {K : Boundary Ty} {Qs : Exits Ty} :
    (E ⊕ (Qs.At X × R)) ⊕ (K.At X × R) → E ⊕ (Exits.At (K :: Qs) X × R)
  | .inl (.inl e) => .inl e
  | .inl (.inr y) => .inr (Exits.At.there K y.1, y.2)
  | .inr y => .inr (Exits.At.here y.1, y.2)

/-- A body keeps a family on its entrances: at each entrance of the family, a witness of the
precondition of the body, and the family at the next entrance of each run. -/
abbrev Spec.Keeps {A B : Type} (F : Spec.{a, b} A (B ⊕ A)) (Inv : A → Type b) :
    Type (max a b) :=
  (x : A) → Inv x → (p : F.Pre x) × ((x' : A) → F.Post x p (.inr x') → Inv x')

/-- One iteration on the entrances with the family. -/
def Spec.iterate {A B : Type} (F : Spec.{a, b} A (B ⊕ A)) {Inv : A → Type b}
    (keeps : F.Keeps Inv) : Rel.{b, b, b} ((x : A) × Inv x) (B ⊕ ((x : A) × Inv x))
  | x, .inl o => F.Post x.1 (keeps x.1 x.2).1 (.inl o)
  | x, .inr y => (post : F.Post x.1 (keeps x.1 x.2).1 (.inr y.1)) × ((keeps x.1 x.2).2 y.1 post ≡ y.2)

/-- The specification of a loop from the specification of one iteration. A witness of the
precondition is an invariant: a family on the entrances that the body keeps, at the entrance.
The runs are the loop of the iterations on the entrances with the family. -/
def Spec.loopInv {A B : Type} (F : Spec.{a, b} A (B ⊕ A)) :
    Spec.{max a (b + 1), b} A B :=
  ⟨fun x => (Inv : A → Type b) × (Inv x × F.Keeps Inv),
    fun x w o => Loop (F.iterate w.2.2) ⟨x, w.2.1⟩ o⟩

variable (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E))

private def Spec.exit {Γ : List Ty} {Qs : Exits Ty} (out : Qs.At (Port Γ)) :
    Spec.{a, b} (All X Γ × R) (E ⊕ (Qs.At X × R)) :=
  ⟨fun _ => PUnit,
    fun x _ o => Spec.Result (Sum.inr (out.select x.1, x.2) : E ⊕ (Qs.At X × R)) o⟩

/-- The specification after a call returns, at its output case with its values in the environment. -/
private def Spec.afterResponse {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty}
    (next : (c : K.Case) → Spec.{a, b} (All X (c.1 ++ Γ) × R) (E ⊕ (Qs.At X × R)))
    (env : All X Γ) : Spec.{a, b} (K.At X × R) (E ⊕ (Qs.At X × R)) :=
  ⟨fun ⟨⟨c, vals⟩, runtime⟩ => (next c).Pre (vals.append env, runtime),
    fun ⟨⟨c, vals⟩, runtime⟩ p o => (next c).Post (vals.append env, runtime) p o⟩

private def Spec.step {Γ : List Ty} {Qs : Exits Ty} (call : (S.interface (Port Γ)).Shape)
    (next : (c : (S.output call.1).Case) →
      Spec.{max w (z + 1), z} (All X (c.1 ++ Γ) × R) (E ⊕ (Qs.At X × R))) :
    Spec.{max w (z + 1), z} (All X Γ × R) (E ⊕ (Qs.At X × R)) :=
  ⟨fun x =>
    (p : r.Pre (⟨call.1, x.1.select call.2⟩, x.2)) ×
      ((i : E ⊕ ((S.output call.1).At X × R)) → r.Post (⟨call.1, x.1.select call.2⟩, x.2) p i →
        Spec.resumePre (Spec.afterResponse next x.1).Pre i),
    fun x pre o =>
      (i : E ⊕ ((S.output call.1).At X × R)) ×
        (post : r.Post (⟨call.1, x.1.select call.2⟩, x.2) pre.1 i) ×
          Spec.resumePost
            (Spec.afterResponse next x.1).Post i (pre.2 i post) o⟩

private def Spec.seq {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty}
    (first : Spec.{a, b} (All X Γ × R) (E ⊕ (Exits.At (K :: Qs) X × R)))
    (next : Spec.{a, b} (K.At X × R) (E ⊕ (Qs.At X × R))) :
    Spec.{max a b, b} (All X Γ × R) (E ⊕ (Qs.At X × R)) :=
  ⟨fun x =>
    (p : first.Pre x) ×
      ((m : E ⊕ (Exits.At (K :: Qs) X × R)) → first.Post x p m →
        Spec.resumePre (fun (y : Exits.At (K :: Qs) X × R) =>
          Spec.exitPre (fun k => next.Pre (k, y.2)) y.1) m),
    fun x pre o =>
      (m : E ⊕ (Exits.At (K :: Qs) X × R)) × (post : first.Post x pre.1 m) ×
        Spec.resumePost
          (fun (y : Exits.At (K :: Qs) X × R) p o =>
            Spec.atExit (fun k => next.Pre (k, y.2))
              (fun k p o => next.Post (k, y.2) p o)
              (fun q o => Spec.Result (Sum.inr (q, y.2) : E ⊕ (Qs.At X × R)) o) y.1 p o)
          m (pre.2 m post) o⟩

private def Spec.copair {P : Boundary Ty} {Qs : Exits Ty}
    (each : (c : P.Case) → Spec.{a, b} (All X c.1 × R) (E ⊕ (Qs.At X × R))) :
    Spec.{a, b} (P.At X × R) (E ⊕ (Qs.At X × R)) :=
  ⟨fun x => (each x.1.1).Pre (x.1.2, x.2),
    fun x p o => (each x.1.1).Post (x.1.2, x.2) p o⟩

private def Spec.frame {P M K : Boundary Ty} {Δ : List Ty} {Qs : Exits Ty}
    (kept : (c : P.Case) → M.At (Port c.1)) (args : (c : P.Case) → PortMap c.1 Δ)
    (shared : Spec.{a, b} (All X Δ × R) (E ⊕ (Exits.At [K] X × R)))
    (next : Spec.{a, b} ((M.product K).At X × R) (E ⊕ (Qs.At X × R))) :
    Spec.{max a b, b} (P.At X × R) (E ⊕ (Qs.At X × R)) :=
  ⟨fun x =>
    (p : shared.Pre (x.1.2.select (args x.1.1), x.2)) ×
      ((m : E ⊕ (Exits.At [K] X × R)) →
        shared.Post (x.1.2.select (args x.1.1), x.2) p m →
        Spec.resumePre (fun (y : Exits.At [K] X × R) =>
          Spec.exitPre (fun out =>
            next.Pre
              (⟨Boundary.pair (kept x.1.1).1 out.1,
                out.2.append (x.1.2.select (kept x.1.1).2)⟩, y.2)) y.1) m),
    fun x pre o =>
      (m : E ⊕ (Exits.At [K] X × R)) ×
        (post : shared.Post (x.1.2.select (args x.1.1), x.2) pre.1 m) ×
          Spec.resumePost
            (fun (y : Exits.At [K] X × R) p o =>
              Spec.atExit
                (fun out =>
                  next.Pre
                    (⟨Boundary.pair (kept x.1.1).1 out.1,
                      out.2.append (x.1.2.select (kept x.1.1).2)⟩, y.2))
                (fun out p o =>
                  next.Post
                    (⟨Boundary.pair (kept x.1.1).1 out.1,
                      out.2.append (x.1.2.select (kept x.1.1).2)⟩, y.2) p o)
                (fun q _ => Exits.At.ofNil q) y.1 p o)
            m (pre.2 m post) o⟩

private def Spec.iteration {K : Boundary Ty} {Qs : Exits Ty}
    (body : Spec.{a, b} (K.At X × R) (E ⊕ (Exits.At (K :: Qs) X × R))) :
    Spec.{a, b} (K.At X × R) ((E ⊕ (Qs.At X × R)) ⊕ (K.At X × R)) :=
  ⟨body.Pre, fun x p t => body.Post x p (unresult t)⟩

mutual

/-- The specification of a diagram, from a specification of its calls with a runtime. -/
def Diagram.spec {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs) :
    Spec.{max w (z + 1), z} (All X Γ × R) (E ⊕ (Qs.At X × R)) :=
  Diagram.casesOn
    (motive_1 := fun Γ Qs _ => Spec.{max w (z + 1), z} (All X Γ × R) (E ⊕ (Qs.At X × R))) d
    (fun out => Spec.exit out)
    (fun call next => Spec.step r call fun c => (next c).spec)
    (fun first next => Spec.seq first.spec next.spec)

/-- The specification of a continuation. -/
def Continuation.spec : {P : Boundary Ty} → {Qs : Exits Ty} → Continuation S P Qs →
    Spec.{max w (z + 1), z} (P.At X × R) (E ⊕ (Qs.At X × R))
  | _, _, .copair each => Spec.copair fun c => (each c).spec
  | _, _, .frame kept args shared next => Spec.frame kept args shared.spec next.spec
  | _, _, .loop body => Spec.loopInv (Spec.iteration body.spec)

end

/-- The specification of one iteration of a loop. -/
abbrev iterSpec {K : Boundary Ty} {Qs : Exits Ty} (body : Continuation S K (K :: Qs)) :
    Spec.{max w (z + 1), z} (K.At X × R) ((E ⊕ (Qs.At X × R)) ⊕ (K.At X × R)) :=
  Spec.iteration (Continuation.spec r body)

end Draft

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E))
  {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty}

/-- The first exit equation, for the witnesses: a witness of the composite of an exit to the
boundary of a continuation and that continuation gives a witness of the continuation at the
case of the exit. -/
def Diagram.exitSeqPre (out : K.At (Port Γ)) (next : Continuation S K Qs) (a : All X Γ × R)
    (pre : (Diagram.spec r (Diagram.seq (.exit (Exits.At.here out)) next)).Pre a) :
    (Continuation.spec r next).Pre (⟨out.1, a.1.select out.2⟩, a.2) :=
  pre.2 (.inr ((Exits.At.here out).select a.1, a.2)) ⟨.refl⟩

/-- A witness of the continuation at the case of the exit gives a witness of the composite. -/
def Diagram.exitSeqPreInv (out : K.At (Port Γ)) (next : Continuation S K Qs) (a : All X Γ × R)
    (w : (Continuation.spec r next).Pre (⟨out.1, a.1.select out.2⟩, a.2)) :
    (Diagram.spec r (Diagram.seq (.exit (Exits.At.here out)) next)).Pre a :=
  ⟨PUnit.unit, fun _ e =>
    Identity.transport
      (fun m => Spec.resumePre (fun (y : Exits.At (K :: Qs) X × R) =>
        Spec.exitPre (fun k => (Continuation.spec r next).Pre (k, y.2)) y.1) m) e.down w⟩

/-- A witness of the continuation, as a witness of the composite and then as a witness of the
continuation, is the first witness. The identity holds by computation. -/
def Diagram.exitSeqPreRound (out : K.At (Port Γ)) (next : Continuation S K Qs)
    (a : All X Γ × R) (w : (Continuation.spec r next).Pre (⟨out.1, a.1.select out.2⟩, a.2)) :
    Diagram.exitSeqPre r out next a (Diagram.exitSeqPreInv r out next a w) ≡ w := .refl

/-- The first exit equation, for the runs over a witness: the runs of the composite are the
runs of the continuation at the case of the exit, with the two round trips. -/
def Diagram.exitSeqSpecRuns (out : K.At (Port Γ)) (next : Continuation S K Qs) (a : All X Γ × R)
    (pre : (Diagram.spec r (Diagram.seq (.exit (Exits.At.here out)) next)).Pre a)
    (o : E ⊕ (Qs.At X × R)) :
    Iso ((Diagram.spec r (Diagram.seq (.exit (Exits.At.here out)) next)).Post a pre o)
      ((Continuation.spec r next).Post (⟨out.1, a.1.select out.2⟩, a.2) (Diagram.exitSeqPre r out next a pre)
        o) :=
  Identity.contract
    (x₀ := (Sum.inr ((Exits.At.here out).select a.1, a.2) : E ⊕ (Exits.At (K :: Qs) X × R)))
    (fun m e =>
      Spec.resumePost
        (fun (y : Exits.At (K :: Qs) X × R) p o =>
          Spec.atExit (fun k => (Continuation.spec r next).Pre (k, y.2))
            (fun k p o => (Continuation.spec r next).Post (k, y.2) p o)
            (fun q o => Spec.Result (Sum.inr (q, y.2) : E ⊕ (Qs.At X × R)) o) y.1 p o)
        m (pre.2 m e) o)

/-- The second exit equation, for the runs over a witness: the runs of the composite of an exit
past a continuation and that continuation are the runs of that exit, with the two round
trips. -/
def Diagram.exitPastSpecRuns (out : Qs.At (Port Γ)) (next : Continuation S K Qs) (a : All X Γ × R)
    (pre : (Diagram.spec r (Diagram.seq (.exit (out.there K)) next)).Pre a) (o : E ⊕ (Qs.At X × R)) :
    Iso ((Diagram.spec r (Diagram.seq (.exit (out.there K)) next)).Post a pre o)
      ((Diagram.spec r (Diagram.exit (S := S) out)).Post a PUnit.unit o) :=
  Identity.contract
    (x₀ := (Sum.inr ((out.there K).select a.1, a.2) : E ⊕ (Exits.At (K :: Qs) X × R)))
    (fun m e =>
      Spec.resumePost
        (fun (y : Exits.At (K :: Qs) X × R) p o =>
          Spec.atExit (fun k => (Continuation.spec r next).Pre (k, y.2))
            (fun k p o => (Continuation.spec r next).Post (k, y.2) p o)
            (fun q o => Spec.Result (Sum.inr (q, y.2) : E ⊕ (Qs.At X × R)) o) y.1 p o)
        m (pre.2 m e) o)

/-- The runs of a loop over a witness are the runs of the loop of its iterations on the
entrances with the invariant. The identity holds by computation. -/
def Continuation.loopSpecRuns (body : Continuation S K (K :: Qs)) (a : K.At X × R)
    (w : (Continuation.spec r (Continuation.loop body)).Pre a) (o : E ⊕ (Qs.At X × R)) :
    (Continuation.spec r (Continuation.loop body)).Post a w o ≡
      Loop ((iterSpec r body).iterate w.2.2) ⟨a, w.2.1⟩ o :=
  .refl

end Draft
