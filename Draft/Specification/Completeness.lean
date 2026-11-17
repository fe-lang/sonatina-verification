import Draft.Specification.Soundness

/-! The runs of a diagram are runs of its approximants.

A run of the diagram over a witness, and then a run of the rest along its evidence, is a run of
the computation of the diagram along its evidence, from a threshold of the number of
unrollings. The witness of a diagram that has a witness of each of its parts gives that
threshold with the run. -/

set_option autoImplicit false
set_option genInjectivity false

universe w z a b v w' z' c d

open Prelude Container

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E))
  {α : Type} {F : E ⊕ (α × R) → Type v} {stop : Free (S.interface X) α}
  (limit : (s₀ : R) → FreeDep r F (stop.thread s₀))

abbrev Diagram.Along {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs) (env : All X Γ) (s : R)
    (pre : (Diagram.spec r d).Pre (env, s)) (m : E ⊕ (Qs.At X × R))
    (run : (Diagram.spec r d).Post (env, s) pre m) : Type (max w z v) :=
  (N : Nat) × ((n : Nat) → N ≤ n → (cont : Qs.At X → Free (S.interface X) α) →
    (rest : (m : E ⊕ (Qs.At X × R)) → (Diagram.spec r d).Post (env, s) pre m →
      FreeDep r F (Free.resume cont m)) →
    (o : E ⊕ (α × R)) → FreeDep.Runs (Free.resume cont m) (rest m run) o →
    FreeDep.Runs ((d.run stop n env cont).thread s)
      (Diagram.evidence r limit n d env s pre cont rest) o)

abbrev Continuation.Along {P : Boundary Ty} {Qs : Exits Ty} (k : Continuation S P Qs)
    (a : P.At X) (s : R) (pre : (Continuation.spec r k).Pre (a, s)) (m : E ⊕ (Qs.At X × R))
    (run : (Continuation.spec r k).Post (a, s) pre m) : Type (max w z v) :=
  (N : Nat) × ((n : Nat) → N ≤ n → (cont : Qs.At X → Free (S.interface X) α) →
    (rest : (m : E ⊕ (Qs.At X × R)) → (Continuation.spec r k).Post (a, s) pre m →
      FreeDep r F (Free.resume cont m)) →
    (o : E ⊕ (α × R)) → FreeDep.Runs (Free.resume cont m) (rest m run) o →
    FreeDep.Runs ((k.run stop n a cont).thread s)
      (Continuation.evidence r limit n k a s pre cont rest) o)

/-- Completeness after the result of the first diagram of a composite. -/
def seqAlong {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (first : Diagram S Γ (K :: Qs))
    (next : Continuation S K Qs) (env : All X Γ) (s : R)
    (pre : (Diagram.spec r (Diagram.seq first next)).Pre (env, s))
    (nextAlong : (k : K.At X) → (s₁ : R) → (p : (Continuation.spec r next).Pre (k, s₁)) →
      (m : E ⊕ (Qs.At X × R)) → (run : (Continuation.spec r next).Post (k, s₁) p m) →
      next.Along r limit k s₁ p m run)
    (m : E ⊕ (Qs.At X × R)) :
    (m₁ : E ⊕ (Exits.At (K :: Qs) X × R)) → (run₁ : (Diagram.spec r first).Post (env, s) pre.1 m₁) →
    (tail : Spec.resumePost
      (fun (y : Exits.At (K :: Qs) X × R) p o =>
        Spec.atExit (fun k => (Continuation.spec r next).Pre (k, y.2))
          (fun k p o => (Continuation.spec r next).Post (k, y.2) p o)
          (fun q o => Spec.Result (Sum.inr (q, y.2) : E ⊕ (Qs.At X × R)) o) y.1 p o)
      m₁ (pre.2 m₁ run₁) m) →
    (N : Nat) × ((n : Nat) → N ≤ n → (cont : Qs.At X → Free (S.interface X) α) →
      (rest : (m : E ⊕ (Qs.At X × R)) →
        (Diagram.spec r (Diagram.seq first next)).Post (env, s) pre m →
        FreeDep r F (Free.resume cont m)) →
      (o : E ⊕ (α × R)) → FreeDep.Runs (Free.resume cont m) (rest m ⟨m₁, run₁, tail⟩) o →
      FreeDep.Runs (Free.resume (Exits.At.elim (fun k => next.run stop n k cont) cont) m₁)
        (seqRest r n first next env s pre
          (fun k s₁ p => Continuation.evidence r limit n next k s₁ p) cont rest m₁ run₁) o)
  | .inl e, run₁, tail =>
      ⟨0, fun _ _ cont rest o t =>
        Identity.ind
          (fun (m : E ⊕ (Qs.At X × R)) (tail : (Sum.inl e : E ⊕ (Qs.At X × R)) ≡ m) =>
            FreeDep.Runs (Free.resume cont m) (rest m ⟨.inl e, run₁, ⟨tail⟩⟩) o →
              FreeDep.Runs (Free.resume cont (.inl e)) (rest (.inl e) ⟨.inl e, run₁, ⟨.refl⟩⟩) o)
          (fun t => t) tail.down t⟩
  | .inr y, run₁, tail =>
      Exits.At.cases
        (motive := fun x =>
          (run₁ : (Diagram.spec r first).Post (env, s) pre.1 (.inr (x, y.2))) →
          (tail : Spec.atExit (fun k => (Continuation.spec r next).Pre (k, y.2))
            (fun k p o => (Continuation.spec r next).Post (k, y.2) p o)
            (fun q o => Spec.Result (Sum.inr (q, y.2) : E ⊕ (Qs.At X × R)) o) x
            (pre.2 (.inr (x, y.2)) run₁) m) →
          (N : Nat) × ((n : Nat) → N ≤ n → (cont : Qs.At X → Free (S.interface X) α) →
            (rest : (m : E ⊕ (Qs.At X × R)) →
              (Diagram.spec r (Diagram.seq first next)).Post (env, s) pre m →
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
                    (rest m ⟨.inr (Exits.At.there K q, y.2), run₁, ⟨tail⟩⟩) o →
                  FreeDep.Runs (Free.resume cont (.inr (q, y.2)))
                    (rest (.inr (q, y.2)) ⟨.inr (Exits.At.there K q, y.2), run₁, ⟨.refl⟩⟩) o)
              (fun t => t) tail.down t⟩)
        y.1 run₁ tail

/-- Completeness after the result of the diagram of a frame. -/
def frameAlong {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
    (kept : (c : P.Case) → M.At (Port c.1)) (args : (c : P.Case) → PortMap c.1 Δ)
    (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs) (a : P.At X) (s : R)
    (pre : (Continuation.spec r (Continuation.frame kept args shared next)).Pre (a, s))
    (nextAlong : (k : (M.product K).At X) → (s₁ : R) → (p : (Continuation.spec r next).Pre (k, s₁)) →
      (m : E ⊕ (Qs.At X × R)) → (run : (Continuation.spec r next).Post (k, s₁) p m) →
      next.Along r limit k s₁ p m run)
    (m : E ⊕ (Qs.At X × R)) :
    (m₁ : E ⊕ (Exits.At [K] X × R)) →
    (run₁ : (Diagram.spec r shared).Post (a.2.select (args a.1), s) pre.1 m₁) →
    (tail : Spec.resumePost
      (fun (y : Exits.At [K] X × R) p o =>
        Spec.atExit
          (fun out =>
            (Continuation.spec r next).Pre
              (⟨Boundary.pair (kept a.1).1 out.1,
                out.2.append (a.2.select (kept a.1).2)⟩, y.2))
          (fun out p o =>
            (Continuation.spec r next).Post
              (⟨Boundary.pair (kept a.1).1 out.1,
                out.2.append (a.2.select (kept a.1).2)⟩, y.2) p o)
          (fun q _ => Exits.At.ofNil q) y.1 p o)
      m₁ (pre.2 m₁ run₁) m) →
    (N : Nat) × ((n : Nat) → N ≤ n → (cont : Qs.At X → Free (S.interface X) α) →
      (rest : (m : E ⊕ (Qs.At X × R)) →
        (Continuation.spec r (Continuation.frame kept args shared next)).Post (a, s) pre m →
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
            FreeDep.Runs (Free.resume cont m) (rest m ⟨.inl e, run₁, ⟨tail⟩⟩) o →
              FreeDep.Runs (Free.resume cont (.inl e)) (rest (.inl e) ⟨.inl e, run₁, ⟨.refl⟩⟩) o)
          (fun t => t) tail.down t⟩
  | .inr y, run₁, tail =>
      Exits.At.cases
        (motive := fun x =>
          (run₁ : (Diagram.spec r shared).Post (a.2.select (args a.1), s) pre.1 (.inr (x, y.2))) →
          (tail : Spec.atExit
            (fun out =>
              (Continuation.spec r next).Pre
                (⟨Boundary.pair (kept a.1).1 out.1,
                  out.2.append (a.2.select (kept a.1).2)⟩, y.2))
            (fun out p o =>
              (Continuation.spec r next).Post
                (⟨Boundary.pair (kept a.1).1 out.1,
                  out.2.append (a.2.select (kept a.1).2)⟩, y.2) p o)
            (fun q _ => Exits.At.ofNil q) x (pre.2 (.inr (x, y.2)) run₁) m) →
          (N : Nat) × ((n : Nat) → N ≤ n → (cont : Qs.At X → Free (S.interface X) α) →
            (rest : (m : E ⊕ (Qs.At X × R)) →
              (Continuation.spec r (Continuation.frame kept args shared next)).Post (a, s) pre m →
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
  (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E))
  {α : Type} {F : E ⊕ (α × R) → Type v} {stop : Free (S.interface X) α}
  (limit : (s₀ : R) → FreeDep r F (stop.thread s₀))

section LoopAlong

variable {K : Boundary Ty} {Qs : Exits Ty} (body : Continuation S K (K :: Qs))
  {Inv : K.At X × R → Type z} (keeps : (iterSpec r body).Keeps Inv)

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
  fun _ e₂ =>
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
    (bodyAlong : (a : K.At X) → (s₁ : R) → (p : (Continuation.spec r body).Pre (a, s₁)) →
      (m' : E ⊕ (Exits.At (K :: Qs) X × R)) → (run : (Continuation.spec r body).Post (a, s₁) p m') →
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
    (s : R) → (pre : (Diagram.spec r d).Pre (env, s)) → (m : E ⊕ (Qs.At X × R)) →
    (run : (Diagram.spec r d).Post (env, s) pre m) → d.Along r limit env s pre m run
  | _, Qs, .exit out, env, s, _, _, run =>
      ⟨0, fun _ _ cont rest o t =>
        Identity.ind
          (fun (m : E ⊕ (Qs.At X × R))
              (run : (Sum.inr (out.select env, s) : E ⊕ (Qs.At X × R)) ≡ m) =>
            FreeDep.Runs (Free.resume cont m) (rest m ⟨run⟩) o →
              FreeDep.Runs (Free.resume cont (.inr (out.select env, s)))
                (rest (.inr (out.select env, s)) ⟨.refl⟩) o)
          (fun t => t) run.down t⟩
  | _, Qs, .step _ next, env, _, pre, m, run =>
      match run with
      | ⟨.inl e, post, tail⟩ =>
          ⟨0, fun _ _ cont rest o t =>
            ⟨.inl e, post,
              Identity.ind
                (fun (m : E ⊕ (Qs.At X × R)) (tail : (Sum.inl e : E ⊕ (Qs.At X × R)) ≡ m) =>
                  FreeDep.Runs (Free.resume cont m) (rest m ⟨.inl e, post, ⟨tail⟩⟩) o →
                    FreeDep.Runs (Free.resume cont (.inl e))
                      (rest (.inl e) ⟨.inl e, post, ⟨.refl⟩⟩) o)
                (fun t => t) tail.down t⟩⟩
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
    (a : P.At X) → (s : R) → (pre : (Continuation.spec r k).Pre (a, s)) → (m : E ⊕ (Qs.At X × R)) →
    (run : (Continuation.spec r k).Post (a, s) pre m) → k.Along r limit a s pre m run
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


namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E))
  (always : (a : ((S.interface X).runtime R E).Shape) → r.Pre a)

mutual

/-- A specification of the calls with a witness of each precondition gives a witness of the
precondition of each diagram. -/
def Diagram.witness : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    (a : All X Γ × R) → (Diagram.spec r d).Pre a
  | _, _, .exit _, _ => PUnit.unit
  | _, _, .step call next, a =>
      ⟨always _, fun x _ =>
        Sum.casesOn
          (motive := fun x =>
            Spec.resumePre (fun (y : (S.output call.1).At X × R) =>
              (Diagram.spec r (next y.1.1)).Pre (y.1.2.append a.1, y.2)) x)
          x (fun _ => PUnit.unit) (fun y => Diagram.witness (next y.1.1) (y.1.2.append a.1, y.2))⟩
  | _, Qs, .seq (K := K) first next, a =>
      ⟨Diagram.witness first a, fun m _ =>
        Sum.casesOn
          (motive := fun m =>
            Spec.resumePre (fun (y : Exits.At (K :: Qs) X × R) =>
              Spec.exitPre (fun k => (Continuation.spec r next).Pre (k, y.2)) y.1) m)
          m (fun _ => PUnit.unit)
          (fun y =>
            Exits.At.cases
              (motive := fun e => Spec.exitPre (fun k => (Continuation.spec r next).Pre (k, y.2)) e)
              (fun k => Continuation.witness next (k, y.2)) (fun _ => PUnit.unit) y.1)⟩

def Continuation.witness : {P : Boundary Ty} → {Qs : Exits Ty} → (k : Continuation S P Qs) →
    (a : P.At X × R) → (Continuation.spec r k).Pre a
  | _, _, .copair each, a => Diagram.witness (each a.1.1) (a.1.2, a.2)
  | _, _, .frame (K := K) kept args shared next, a =>
      ⟨Diagram.witness shared (a.1.2.select (args a.1.1), a.2), fun m _ =>
        Sum.casesOn
          (motive := fun m =>
            Spec.resumePre (fun (y : Exits.At [K] X × R) =>
              Spec.exitPre (fun out =>
                (Continuation.spec r next).Pre
                  (⟨Boundary.pair (kept a.1.1).1 out.1,
                    out.2.append (a.1.2.select (kept a.1.1).2)⟩, y.2)) y.1) m)
          m (fun _ => PUnit.unit)
          (fun y =>
            Exits.At.cases
              (motive := fun e =>
                Spec.exitPre (fun out =>
                  (Continuation.spec r next).Pre
                    (⟨Boundary.pair (kept a.1.1).1 out.1,
                      out.2.append (a.1.2.select (kept a.1.1).2)⟩, y.2)) e)
              (fun _ => Continuation.witness next _) (fun _ => PUnit.unit) y.1)⟩
  | _, _, .loop body, _ =>
      ⟨fun _ => PUnit, PUnit.unit, fun a' _ => ⟨Continuation.witness body a', fun _ _ => PUnit.unit⟩⟩

end

end Draft
