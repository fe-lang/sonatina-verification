import Draft.Specification

/-! The evidence of each approximant of a diagram, from a witness of its precondition.

A witness of the precondition of a diagram gives the evidence of the computation of the diagram
with each number of unrollings, for evidence of the rest at each result of a run over the
witness. A bound records where a run can reach the loop cutoff. The evidence builder takes
evidence for the cutoff at those runtimes. When every runtime admits the cutoff, the same
builder applies to every witness and number of unrollings. -/

set_option autoImplicit false
set_option genInjectivity false

universe w z a b v w' z' c d

open Prelude Container

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}

variable (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E))

section Evidence

variable {α : Type} (n : Nat)

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

end Evidence

section Bound

/-! A bound on the runs, and the limit condition -/

/-- A condition after a result with a stop, over the witness after that result. -/
def Spec.resumeOn {M : Type} {P : M → Type a} (W : (m : M) → P m → Type c) :
    (x : E ⊕ M) → Spec.resumePre P x → Type c
  | .inl _, _ => PUnit
  | .inr m, p => W m p

/-- A condition at an exit, over the witness at that exit. -/
def Spec.exitOn {K : Boundary Ty} {Qs : Exits Ty} (headPre : K.At X → Type a)
    (W : (k : K.At X) → headPre k → Type c) :
    (e : Exits.At (K :: Qs) X) → Spec.exitPre headPre e → Type c :=
  Exits.At.cases (motive := fun e => Spec.exitPre headPre e → Type c) W (fun _ _ => PUnit)

/-- The bound of a loop, for a number of unrollings. With no unrolling, the entrance has the
condition of the limit. With one more unrolling, the body has its bound, and each next
entrance that a run of the body gives has the bound with one unrolling less. -/
def Spec.Bound {A B : Type} (F : Spec.{a, b} A (B ⊕ A)) {Inv : A → Type b}
    (keeps : F.Keeps Inv) (bodyOn : (a : A) → F.Pre a → Type c) (atLimit : A → Type d) :
    Nat → ((a : A) × Inv a) → Type (max b c d)
  | 0, y => ULift.{max b c} (atLimit y.1)
  | m + 1, y =>
      bodyOn y.1 (keeps y.1 y.2).1 ×
        ((a' : A) → (post : F.Post y.1 (keeps y.1 y.2).1 (.inr a')) →
          Spec.Bound F keeps bodyOn atLimit m ⟨a', (keeps y.1 y.2).2 a' post⟩)

variable (L : R → Type c)

mutual

/-- The bound of a diagram over a witness of its precondition, for a number of unrollings: each
run over the witness reaches the limit of a loop only at a runtime with the condition `L`. -/
def Diagram.Within (n : Nat) : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    (a : All X Γ × R) → (Diagram.spec r d).Pre a → Type (max z c)
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
          (post : (Diagram.spec r first).Post a pre.1 m) →
          Spec.resumeOn
            (fun (y : Exits.At (K :: Qs) X × R) p =>
              Spec.exitOn (fun k => (Continuation.spec r next).Pre (k, y.2))
                (fun k p => next.Within n (k, y.2) p) y.1 p) m (pre.2 m post))

def Continuation.Within (n : Nat) : {P : Boundary Ty} → {Qs : Exits Ty} →
    (k : Continuation S P Qs) → (a : P.At X × R) → (Continuation.spec r k).Pre a →
    Type (max z c)
  | _, _, .copair each, a, pre => (each a.1.1).Within n (a.1.2, a.2) pre
  | _, _, .frame (K := K) kept args shared next, a, pre =>
      shared.Within n (a.1.2.select (args a.1.1), a.2) pre.1 ×
        ((m : E ⊕ (Exits.At [K] X × R)) →
          (post : (Diagram.spec r shared).Post (a.1.2.select (args a.1.1), a.2) pre.1 m) →
          Spec.resumeOn
            (fun (y : Exits.At [K] X × R) p =>
              Spec.exitOn
                (fun out =>
                  (Continuation.spec r next).Pre
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

variable {α : Type} {F : E ⊕ (α × R) → Type v} {stop : Free (S.interface X) α}
  (limit : (s₀ : R) → L s₀ → FreeDep r F (stop.thread s₀)) (n : Nat)

/-- The evidence of the rest of the first diagram of a composite, with a bound. -/
def seqRestAt {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (first : Diagram S Γ (K :: Qs))
    (next : Continuation S K Qs) (env : All X Γ) (s : R)
    (pre : (Diagram.spec r (Diagram.seq first next)).Pre (env, s))
    (within : (Diagram.seq first next).Within r L n (env, s) pre)
    (nextEv : (k : K.At X) → (s₁ : R) → (p : (Continuation.spec r next).Pre (k, s₁)) →
      next.Within r L n (k, s₁) p → next.Evidence r n F stop k s₁ p)
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
          nextEv k y.2 (pre.2 (.inr (Exits.At.here k, y.2)) run₁)
            (within.2 (.inr (Exits.At.here k, y.2)) run₁) cont
            (fun m tail => rest m ⟨.inr (Exits.At.here k, y.2), run₁, tail⟩))
        (fun q run₁ => rest (.inr (q, y.2)) ⟨.inr (Exits.At.there K q, y.2), run₁, ⟨.refl⟩⟩)
        y.1 run₁

/-- The evidence of the rest of the diagram of a frame, with a bound. -/
def frameRestAt {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
    (kept : (c : P.Case) → M.At (Port c.1)) (args : (c : P.Case) → PortMap c.1 Δ)
    (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs) (a : P.At X) (s : R)
    (pre : (Continuation.spec r (Continuation.frame kept args shared next)).Pre (a, s))
    (within : (Continuation.frame kept args shared next).Within r L n (a, s) pre)
    (nextEv : (k : (M.product K).At X) → (s₁ : R) → (p : (Continuation.spec r next).Pre (k, s₁)) →
      next.Within r L n (k, s₁) p → next.Evidence r n F stop k s₁ p)
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
          nextEv _ y.2 (pre.2 (.inr (Exits.At.here out, y.2)) run₁)
            (within.2 (.inr (Exits.At.here out, y.2)) run₁) cont
            (fun m tail => rest m ⟨.inr (Exits.At.here out, y.2), run₁, tail⟩))
        (fun q _ => Exits.At.ofNil q) y.1 run₁

section LoopAt

variable {K : Boundary Ty} {Qs : Exits Ty} (body : Continuation S K (K :: Qs))
  {Inv : K.At X × R → Type z} (keeps : (iterSpec r body).Keeps Inv)
  (cont : Qs.At X → Free (S.interface X) α)

/-- The bound of a loop, for the body and the limit condition of a diagram. -/
abbrev LoopBound (j : Nat) (y : (a : K.At X × R) × Inv a) : Type (max z c) :=
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
    (bodyEv : (a : K.At X) → (s₁ : R) → (p : (Continuation.spec r body).Pre (a, s₁)) →
      body.Within r L n (a, s₁) p → body.Evidence r n F stop a s₁ p) :
    (j : Nat) → (y : (a : K.At X × R) × Inv a) → LoopBound r L n body keeps j y →
    ((m : E ⊕ (Qs.At X × R)) → Loop ((iterSpec r body).iterate keeps) y m →
      FreeDep r F (Free.resume cont m)) →
    FreeDep r F ((Continuation.unrolled stop (body.run stop n) j y.1.1 cont).thread y.1.2)
  | 0, y, bound, _ => limit y.1.2 bound.down
  | j + 1, y, bound, rest =>
      bodyEv y.1.1 y.1.2 (keeps y.1 y.2).1 bound.1 _
        (loopRestAt r L n body keeps cont j y bound.2
          (fun y' bound' rest' => loopEvidenceAt bodyEv j y' bound' rest') rest)

end LoopAt

mutual

/-- The evidence of an approximant of a diagram, from a witness of its precondition and a
bound: the limit of a loop is reached only at a runtime with the condition `L`. -/
def Diagram.evidenceAt : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    (env : All X Γ) → (s : R) → (pre : (Diagram.spec r d).Pre (env, s)) →
    d.Within r L n (env, s) pre → d.Evidence r n F stop env s pre
  | _, _, .exit out, env, s, _, _ => fun _ rest => rest (.inr (out.select env, s)) ⟨.refl⟩
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
                (Diagram.spec r (next y.1.1)).Pre (y.1.2.append env, y.2)) x) →
              Spec.resumeOn
                (fun (y : (S.output call.1).At X × R) p =>
                  (next y.1.1).Within r L n (y.1.2.append env, y.2) p) x p →
              ((m : E ⊕ (Qs.At X × R)) →
                Spec.resumePost
                  (fun (y : (S.output call.1).At X × R) p o =>
                    (Diagram.spec r (next y.1.1)).Post (y.1.2.append env, y.2) p o) x p m →
                FreeDep r F (Free.resume cont m)) →
              FreeDep r F
                (Sum.elim (fun e => Free.pure (.inl e))
                  (fun (b : (S.output call.1).At X × R) =>
                    ((next b.1.1).run stop n (b.1.2.append env) cont).thread b.2) x))
            x (fun e _ _ k => k (.inl e) ⟨.refl⟩)
            (fun b p w k =>
              Diagram.evidenceAt (next b.1.1) (b.1.2.append env) b.2 p w cont k)
            (pre.2 x post) (within x post) (fun m tail => rest m ⟨x, post, tail⟩)
  | _, _, .seq first next, env, s, pre, within => fun cont rest =>
      Diagram.evidenceAt first env s pre.1 within.1 _
        (seqRestAt r L n first next env s pre within
          (fun k s₁ p w => Continuation.evidenceAt next k s₁ p w) cont rest)

def Continuation.evidenceAt : {P : Boundary Ty} → {Qs : Exits Ty} →
    (k : Continuation S P Qs) → (a : P.At X) → (s : R) → (pre : (Continuation.spec r k).Pre (a, s)) →
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

end Bound

section Always

/-- A condition of the later part at each result of the first part, from the condition at each
witness of the later part. -/
def Spec.laterOn {K : Boundary Ty} {Qs : Exits Ty} {pre : K.At X × R → Type a}
    {on : (y : K.At X × R) → pre y → Type c} (all : (y : K.At X × R) → (p : pre y) → on y p) :
    (m : E ⊕ (Exits.At (K :: Qs) X × R)) →
    (q : Spec.resumePre
      (fun (y : Exits.At (K :: Qs) X × R) => Spec.exitPre (fun k => pre (k, y.2)) y.1) m) →
    Spec.resumeOn
      (fun (y : Exits.At (K :: Qs) X × R) p =>
        Spec.exitOn (fun k => pre (k, y.2)) (fun k p => on (k, y.2) p) y.1 p) m q
  | .inl _, _ => PUnit.unit
  | .inr y, q =>
      Exits.At.cases
        (motive := fun x => (q : Spec.exitPre (fun k => pre (k, y.2)) x) →
          Spec.exitOn (fun k => pre (k, y.2)) (fun k p => on (k, y.2) p) x q)
        (fun k p => all (k, y.2) p) (fun _ _ => PUnit.unit) y.1 q

/-- The bound of a loop for each number of unrollings, from a bound of the body over each
witness and the condition at the limit at each entrance. -/
def Spec.boundAlways {A B : Type} {F : Spec.{a, b} A (B ⊕ A)} {Inv : A → Type b}
    (keeps : F.Keeps Inv) {bodyOn : (x : A) → F.Pre x → Type c} {atLimit : A → Type d}
    (body : (x : A) → (p : F.Pre x) → bodyOn x p) (limit : (x : A) → atLimit x) :
    (m : Nat) → (y : (x : A) × Inv x) → Spec.Bound F keeps bodyOn atLimit m y
  | 0, y => ⟨limit y.1⟩
  | m + 1, y =>
      ⟨body y.1 (keeps y.1 y.2).1, fun x' post =>
        Spec.boundAlways keeps body limit m ⟨x', (keeps y.1 y.2).2 x' post⟩⟩

variable (L : R → Type c) (n : Nat) (always : (s : R) → L s)

mutual

/-- For a condition at the limit that each runtime has, each witness of the precondition of a
diagram has the bound, for each number of unrollings. -/
def Diagram.withinAlways : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    (x : All X Γ × R) → (p : (Diagram.spec r d).Pre x) → d.Within r L n x p
  | _, _, .exit _, _, _ => PUnit.unit
  | _, _, .step call rest, x, p => fun i post =>
      Sum.casesOn
        (motive := fun i =>
          (q : Spec.resumePre (fun (y : (S.output call.1).At X × R) =>
            (Diagram.spec r (rest y.1.1)).Pre (y.1.2.append x.1, y.2)) i) →
          Spec.resumeOn
            (fun (y : (S.output call.1).At X × R) p =>
              (rest y.1.1).Within r L n (y.1.2.append x.1, y.2) p) i q)
        i (fun _ _ => PUnit.unit)
        (fun y q => Diagram.withinAlways (rest y.1.1) (y.1.2.append x.1, y.2) q)
        (p.2 i post)
  | _, _, .seq first next, x, p =>
      ⟨Diagram.withinAlways first x p.1, fun m post =>
        Spec.laterOn (pre := fun y => (Continuation.spec r next).Pre y)
          (on := fun y p => next.Within r L n y p)
          (fun y q => Continuation.withinAlways next y q) m (p.2 m post)⟩

/-- The same for a continuation. -/
def Continuation.withinAlways : {K : Boundary Ty} → {Qs : Exits Ty} →
    (k : Continuation S K Qs) → (x : K.At X × R) → (p : (Continuation.spec r k).Pre x) →
    k.Within r L n x p
  | _, _, .copair each, x, p => Diagram.withinAlways (each x.1.1) (x.1.2, x.2) p
  | _, _, .frame kept args shared next, x, p =>
      ⟨Diagram.withinAlways shared (x.1.2.select (args x.1.1), x.2) p.1, fun m post =>
        Spec.laterOn (pre := fun y => (Continuation.spec r next).Pre (After kept x y))
          (on := fun y p => next.Within r L n (After kept x y) p)
          (fun y q => Continuation.withinAlways next (After kept x y) q) m (p.2 m post)⟩
  | _, _, .loop body, x, p =>
      Spec.boundAlways p.2.2 (fun y q => Continuation.withinAlways body y q)
        (fun y => always y.2) n ⟨x, p.2.1⟩

end

end Always

section Unconditional

variable {α : Type} {F : E ⊕ (α × R) → Type v} {stop : Free (S.interface X) α}
  (limit : (s : R) → FreeDep r F (stop.thread s)) (n : Nat)

/-- Evidence of an approximant when its cutoff computation satisfies the postcondition
at every runtime. -/
def Diagram.evidence {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs)
    (env : All X Γ) (s : R) (pre : (Diagram.spec r d).Pre (env, s)) :
    d.Evidence r n F stop env s pre :=
  d.evidenceAt r (fun _ => Unit) (fun s _ => limit s) n env s pre
    (d.withinAlways r (fun _ => Unit) n (fun _ => ()) (env, s) pre)

def Continuation.evidence {P : Boundary Ty} {Qs : Exits Ty} (k : Continuation S P Qs)
    (a : P.At X) (s : R) (pre : (Continuation.spec r k).Pre (a, s)) :
    k.Evidence r n F stop a s pre :=
  k.evidenceAt r (fun _ => Unit) (fun s _ => limit s) n a s pre
    (k.withinAlways r (fun _ => Unit) n (fun _ => ()) (a, s) pre)

end Unconditional

end Draft
