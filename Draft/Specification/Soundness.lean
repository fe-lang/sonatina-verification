import Draft.Specification

/-! The evidence of each approximant of a diagram, from a witness of its precondition.

A witness of the precondition of a diagram gives the evidence of the computation of the diagram
with each number of unrollings, for evidence of the rest at each result of a run over the
witness. The computation at the limit of a loop has evidence. The condition at the result of a
run of the computation along this evidence is a run of the diagram. -/

set_option autoImplicit false
set_option genInjectivity false

universe w z a b v w' z' c d

open Prelude Container

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}

variable (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E))

section Evidence

variable {α : Type} {F : E ⊕ (α × R) → Type v} {stop : Free (S.interface X) α}
  (limit : (s₀ : R) → FreeDep r F (stop.thread s₀)) (n : Nat)

/-- For a witness of the precondition: the computation of the diagram with a number of
unrollings has evidence, when the rest has evidence at each result of a run over the
witness. -/
abbrev Diagram.Evidence (F : E ⊕ (α × R) → Type v) (stop : Free (S.interface X) α)
    {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs)
    (env : All X Γ) (s : R) (pre : (Diagram.spec r d).Pre (env, s)) :
    Type (max w z v) :=
  (cont : Qs.At X → Free (S.interface X) α) →
    ((m : E ⊕ (Qs.At X × R)) → (Diagram.spec r d).Post (env, s) pre m →
      FreeDep r F (Free.resume cont m)) →
    FreeDep r F ((d.run stop n env cont).thread s)

abbrev Continuation.Evidence (F : E ⊕ (α × R) → Type v) (stop : Free (S.interface X) α)
    {P : Boundary Ty} {Qs : Exits Ty}
    (k : Continuation S P Qs) (a : P.At X) (s : R)
    (pre : (Continuation.spec r k).Pre (a, s)) : Type (max w z v) :=
  (cont : Qs.At X → Free (S.interface X) α) →
    ((m : E ⊕ (Qs.At X × R)) → (Continuation.spec r k).Post (a, s) pre m →
      FreeDep r F (Free.resume cont m)) →
    FreeDep r F ((k.run stop n a cont).thread s)

/-- The evidence of the rest of the first diagram of a composite, at each of its results. -/
def seqRest {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (first : Diagram S Γ (K :: Qs))
    (next : Continuation S K Qs) (env : All X Γ) (s : R)
    (pre : (Diagram.spec r (Diagram.seq first next)).Pre (env, s))
    (nextEv : (k : K.At X) → (s₁ : R) → (p : (Continuation.spec r next).Pre (k, s₁)) →
      next.Evidence r n F stop k s₁ p)
    (cont : Qs.At X → Free (S.interface X) α)
    (rest : (m : E ⊕ (Qs.At X × R)) → (Diagram.spec r (Diagram.seq first next)).Post (env, s) pre m →
      FreeDep r F (Free.resume cont m)) :
    (m₁ : E ⊕ (Exits.At (K :: Qs) X × R)) → (Diagram.spec r first).Post (env, s) pre.1 m₁ →
    FreeDep r F (Free.resume (Exits.At.elim (fun k => next.run stop n k cont) cont) m₁)
  | .inl e, run₁ => rest (.inl e) ⟨.inl e, run₁, ⟨.refl⟩⟩
  | .inr y, run₁ =>
      Exits.At.cases
        (motive := fun x => (Diagram.spec r first).Post (env, s) pre.1 (.inr (x, y.2)) →
          FreeDep r F ((Exits.At.elim (fun k => next.run stop n k cont) cont x).thread y.2))
        (fun k run₁ =>
          nextEv k y.2 (pre.2 (.inr (Exits.At.here k, y.2)) run₁) cont
            (fun m tail => rest m ⟨.inr (Exits.At.here k, y.2), run₁, tail⟩))
        (fun q run₁ => rest (.inr (q, y.2)) ⟨.inr (Exits.At.there K q, y.2), run₁, ⟨.refl⟩⟩)
        y.1 run₁

/-- The evidence of the rest of the diagram of a frame, at each of its results. -/
def frameRest {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
    (kept : (c : P.Case) → M.At (Port c.1)) (args : (c : P.Case) → PortMap c.1 Δ)
    (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs) (a : P.At X) (s : R)
    (pre : (Continuation.spec r (Continuation.frame kept args shared next)).Pre (a, s))
    (nextEv : (k : (M.product K).At X) → (s₁ : R) → (p : (Continuation.spec r next).Pre (k, s₁)) →
      next.Evidence r n F stop k s₁ p)
    (cont : Qs.At X → Free (S.interface X) α)
    (rest : (m : E ⊕ (Qs.At X × R)) →
      (Continuation.spec r (Continuation.frame kept args shared next)).Post (a, s) pre m →
      FreeDep r F (Free.resume cont m)) :
    (m₁ : E ⊕ (Exits.At [K] X × R)) →
    (Diagram.spec r shared).Post (a.2.select (args a.1), s) pre.1 m₁ →
    FreeDep r F
      (Free.resume
        (Exits.At.only fun out =>
          next.run stop n
            ⟨Boundary.pair (kept a.1).1 out.1, out.2.append (a.2.select (kept a.1).2)⟩ cont)
        m₁)
  | .inl e, run₁ => rest (.inl e) ⟨.inl e, run₁, ⟨.refl⟩⟩
  | .inr y, run₁ =>
      Exits.At.cases
        (motive := fun x =>
          (Diagram.spec r shared).Post (a.2.select (args a.1), s) pre.1 (.inr (x, y.2)) →
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
  {Inv : K.At X × R → Type z} (keeps : (iterSpec r body).Keeps Inv)
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
    (m' : E ⊕ (Exits.At (K :: Qs) X × R)) → (Continuation.spec r body).Post y.1 (keeps y.1 y.2).1 m' →
    FreeDep r F
      (Free.resume
        (Exits.At.elim (fun k' => Continuation.unrolled stop (body.run stop n) j k' cont) cont)
        m')
  | .inl e, bodyRun => rest (.inl e) (.exit bodyRun)
  | .inr b, bodyRun =>
      Exits.At.cases
        (motive := fun x => (Continuation.spec r body).Post y.1 (keeps y.1 y.2).1 (.inr (x, b.2)) →
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
    (bodyEv : (a : K.At X) → (s₁ : R) → (p : (Continuation.spec r body).Pre (a, s₁)) →
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
    (env : All X Γ) → (s : R) → (pre : (Diagram.spec r d).Pre (env, s)) →
    d.Evidence r n F stop env s pre
  | _, _, .exit out, env, s, _ => fun _ rest => rest (.inr (out.select env, s)) ⟨.refl⟩
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
                (Diagram.spec r (next y.1.1)).Pre (y.1.2.append env, y.2)) x) →
              ((m : E ⊕ (Qs.At X × R)) →
                Spec.resumePost
                  (fun (y : (S.output call.1).At X × R) p o =>
                    (Diagram.spec r (next y.1.1)).Post (y.1.2.append env, y.2) p o) x p m →
                FreeDep r F (Free.resume cont m)) →
              FreeDep r F
                (Sum.elim (fun e => Free.pure (.inl e))
                  (fun (b : (S.output call.1).At X × R) =>
                    ((next b.1.1).run stop n (b.1.2.append env) cont).thread b.2) x))
            x (fun e _ k => k (.inl e) ⟨.refl⟩)
            (fun b p k => Diagram.evidence (next b.1.1) (b.1.2.append env) b.2 p cont k)
            (pre.2 x post) (fun m tail => rest m ⟨x, post, tail⟩)
  | _, _, .seq first next, env, s, pre => fun cont rest =>
      Diagram.evidence first env s pre.1 _
        (seqRest r n first next env s pre
          (fun k s₁ p => Continuation.evidence next k s₁ p) cont rest)

def Continuation.evidence : {P : Boundary Ty} → {Qs : Exits Ty} →
    (k : Continuation S P Qs) → (a : P.At X) → (s : R) → (pre : (Continuation.spec r k).Pre (a, s)) →
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
