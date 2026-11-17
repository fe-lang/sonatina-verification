import Draft.Specification.Verified

/-! A derivation gives a cartesian map of specifications.

A cartesian map of specifications gives a witness of the second precondition from a witness of
the first, and an equivalence of the runs over the second witness and the runs over the first,
with its two round trips. A rule set holds for a specification of the calls when each rule has
a cartesian map between the specifications of its two sides, in each direction. A derivation in
such a rule set has these maps, by a recursion on the derivation, and a verified diagram moves
along them. In a composite and in a frame, the witness of the later part depends on the run of
the first part, and the equivalence of the runs is a sum over an equivalence of the runs of the
first part. The equivalence of the runs of a loop is the agreement of the loops of two bodies
that agree.

The second exit equation is a rule with a cartesian map in each direction, for each
specification of the calls. -/

set_option autoImplicit false
set_option genInjectivity false

universe w z a b v w' z' c d

open Prelude Container

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}

/-- A cartesian map of specifications of one interface: a witness of the first precondition
gives a witness of the second, and the runs over the second witness are the runs over the
first, as an equivalence with its two round trips. -/
abbrev Spec.Cartesian {A B : Type} (P Q : Spec.{a, b} A B) : Type (max a b) :=
  (a : A) → (pre : P.Pre a) → (w : Q.Pre a) × ((o : B) → Iso (Q.Post a w o) (P.Post a pre o))

/-- The identity map of a specification is cartesian. -/
def Spec.Cartesian.id {A B : Type} (P : Spec.{a, b} A B) : Spec.Cartesian P P :=
  fun _ pre => ⟨pre, fun _ => Iso.refl _⟩

/-- The composite of two cartesian maps. -/
def Spec.Cartesian.comp {A B : Type} {P Q T : Spec.{a, b} A B} (f : Spec.Cartesian P Q)
    (g : Spec.Cartesian Q T) : Spec.Cartesian P T :=
  fun a pre => ⟨(g a (f a pre).1).1, fun o => ((g a (f a pre).1).2 o).trans ((f a pre).2 o)⟩

/-- A cartesian map in each direction. -/
abbrev Spec.Equiv {A B : Type} (P Q : Spec.{a, b} A B) : Type (max a b) :=
  Spec.Cartesian P Q × Spec.Cartesian Q P

/-- The identity maps. -/
def Spec.Equiv.refl {A B : Type} (P : Spec.{a, b} A B) : Spec.Equiv P P := ⟨.id P, .id P⟩

/-- The two maps in the other order. -/
def Spec.Equiv.symm {A B : Type} {P Q : Spec.{a, b} A B} (f : Spec.Equiv P Q) : Spec.Equiv Q P :=
  ⟨f.2, f.1⟩

/-- The composites of the maps of two pairs. -/
def Spec.Equiv.trans {A B : Type} {P Q T : Spec.{a, b} A B} (f : Spec.Equiv P Q) (g : Spec.Equiv Q T) :
    Spec.Equiv P T :=
  ⟨f.1.comp g.1, g.2.comp f.2⟩

section Resume

variable {M B : Type} {P P' : M → Type a}

/-- A map of the witnesses after a response gives a map of the witnesses after a result with a
stop. -/
def Spec.resumeMapPre (f : (m : M) → P m → P' m) :
    (x : E ⊕ M) → Spec.resumePre (E := E) P x → Spec.resumePre (E := E) P' x
  | .inl _, p => p
  | .inr m, p => f m p

/-- An equivalence of the runs after a response, over the map of the witnesses, gives an
equivalence of the runs after a result with a stop. -/
def Spec.resumeIso {G : (m : M) → P m → E ⊕ B → Type b}
    {G' : (m : M) → P' m → E ⊕ B → Type b}
    (f : (m : M) → P m → P' m)
    (g : (m : M) → (p : P m) → (o : E ⊕ B) → Iso (G' m (f m p) o) (G m p o)) :
    (x : E ⊕ M) → (p : Spec.resumePre (E := E) P x) → (o : E ⊕ B) →
    Iso (Spec.resumePost G' x (Spec.resumeMapPre f x p) o) (Spec.resumePost G x p o)
  | .inl _, _, _ => Iso.refl _
  | .inr m, p, o => g m p o

end Resume

section Exit

variable {K : Boundary Ty} {Qs : Exits Ty} {B : Type} {H H' : K.At X → Type a}

/-- A map of the witnesses at the first boundary gives a map of the witnesses at an exit. -/
def Spec.exitMapPre (f : (k : K.At X) → H k → H' k) :
    (x : Exits.At (K :: Qs) X) → Spec.exitPre H x → Spec.exitPre H' x :=
  Exits.At.cases (motive := fun x => Spec.exitPre H x → Spec.exitPre H' x) f (fun _ p => p)

/-- An equivalence of the runs at the first boundary, over the map of the witnesses, gives an
equivalence of the runs at an exit. -/
def Spec.exitIso {G : (k : K.At X) → H k → B → Type b} {G' : (k : K.At X) → H' k → B → Type b}
    {T : Qs.At X → B → Type b} (f : (k : K.At X) → H k → H' k)
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
def Spec.loopCartesian {A B : Type} {F F' : Spec.{a, b} A (B ⊕ A)}
    (f : Spec.Cartesian F F') :
    Spec.Cartesian (Spec.loopInv F) (Spec.loopInv F') :=
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

variable (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E))

section Forms

variable {Γ : List Ty} {Qs : Exits Ty}

/-- A cartesian map for the diagram of each response gives a cartesian map of the steps. -/
def Diagram.stepCartesian (call : (S.interface (Port Γ)).Shape)
    {rest rest' : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs}
    (each : (c : (S.output call.1).Case) → Spec.Cartesian (Diagram.spec r (rest c)) (Diagram.spec r (rest' c))) :
    Spec.Cartesian (Diagram.spec r (Diagram.step call rest)) (Diagram.spec r (Diagram.step call rest')) :=
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
    {next next' : Continuation S K Qs} (head : Spec.Cartesian (Diagram.spec r first) (Diagram.spec r first'))
    (tail : Spec.Cartesian (Continuation.spec r next) (Continuation.spec r next')) :
    Spec.Cartesian (Diagram.spec r (Diagram.seq first next)) (Diagram.spec r (Diagram.seq first' next')) :=
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
                Spec.exitIso (T := fun q o => Spec.Result (Sum.inr (q, y.2) : E ⊕ (Qs.At X × R)) o)
                  (fun k p => (tail (k, y.2) p).1)
                  (fun k p o => (tail (k, y.2) p).2 o) y.1 p o)
              m (pre.2 m (((head a pre.1).2 m).to post)) o⟩

end Forms

section Forms

variable {P : Boundary Ty} {Qs : Exits Ty}

/-- A cartesian map for the diagram of each case gives a cartesian map of the copairings. -/
def Continuation.copairCartesian {each each' : (c : P.Case) → Diagram S c.1 Qs}
    (cases : (c : P.Case) → Spec.Cartesian (Diagram.spec r (each c)) (Diagram.spec r (each' c))) :
    Spec.Cartesian (Continuation.spec r (Continuation.copair each)) (Continuation.spec r (Continuation.copair each')) :=
  fun a pre => cases a.1.1 (a.1.2, a.2) pre

/-- A cartesian map for the body gives a cartesian map of the loops. -/
def Continuation.loopCartesian {body body' : Continuation S P (P :: Qs)}
    (same : Spec.Cartesian (Continuation.spec r body) (Continuation.spec r body')) :
    Spec.Cartesian (Continuation.spec r (Continuation.loop body)) (Continuation.spec r (Continuation.loop body')) :=
  Spec.loopCartesian (F := iterSpec r body) (F' := iterSpec r body')
    fun a pre => ⟨(same a pre).1, fun t => (same a pre).2 (unresult t)⟩

end Forms

section Frame

variable {M K : Boundary Ty} {Qs : Exits Ty} {Δ c : List Ty}

/-- The precondition of a frame at the values of a case, with the kept ports and the port map
of that case as arguments. -/
abbrev FramePre (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs)
    (vals : All X c) (s : R) (kp : M.At (Port c)) (ag : PortMap c Δ) :
    Type (max w (z + 1)) :=
  (p : (Diagram.spec r shared).Pre (vals.select ag, s)) ×
    ((m : E ⊕ (Exits.At [K] X × R)) → (Diagram.spec r shared).Post (vals.select ag, s) p m →
      Spec.resumePre (fun (y : Exits.At [K] X × R) =>
        Spec.exitPre (fun out =>
          (Continuation.spec r next).Pre
            (⟨Boundary.pair kp.1 out.1, out.2.append (vals.select kp.2)⟩, y.2)) y.1) m)

/-- The runs of a frame at the values of a case, over a witness. -/
abbrev FramePost (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs)
    (vals : All X c) (s : R) (kp : M.At (Port c)) (ag : PortMap c Δ)
    (pre : FramePre r shared next vals s kp ag) (o : E ⊕ (Qs.At X × R)) :
    Type z :=
  (m : E ⊕ (Exits.At [K] X × R)) × (post : (Diagram.spec r shared).Post (vals.select ag, s) pre.1 m) ×
    Spec.resumePost
      (fun (y : Exits.At [K] X × R) p o =>
        Spec.atExit
          (fun out =>
            (Continuation.spec r next).Pre
              (⟨Boundary.pair kp.1 out.1, out.2.append (vals.select kp.2)⟩, y.2))
          (fun out p o =>
            (Continuation.spec r next).Post
              (⟨Boundary.pair kp.1 out.1, out.2.append (vals.select kp.2)⟩, y.2) p o)
          (fun q _ => Exits.At.ofNil q) y.1 p o)
      m (pre.2 m post) o

variable {shared shared' : Diagram S Δ [K]} {next next' : Continuation S (M.product K) Qs}

/-- A cartesian map for the diagram of a frame and a cartesian map for its continuation give a
cartesian map at the values of a case, for one choice of the kept ports and of the port map. -/
def frameCartesianAt (body : Spec.Cartesian (Diagram.spec r shared) (Diagram.spec r shared'))
    (tail : Spec.Cartesian (Continuation.spec r next) (Continuation.spec r next')) (vals : All X c) (s : R)
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
    (body : Spec.Cartesian (Diagram.spec r shared) (Diagram.spec r shared'))
    (tail : Spec.Cartesian (Continuation.spec r next) (Continuation.spec r next')) :
    Spec.Cartesian (Continuation.spec r (Continuation.frame kept args shared next))
      (Continuation.spec r (Continuation.frame kept' args' shared' next')) :=
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
    Diagram.Agreement d e → Spec.Equiv (Diagram.spec r d) (Diagram.spec r e)
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
    Spec.Equiv (Continuation.spec r k) (Continuation.spec r k')
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
structure Rules.SpecSound (T : Rules S) : Type (max w (z + 1)) where
  diagram : {Γ : List Ty} → {Qs : Exits Ty} → {d e : Diagram S Γ Qs} → T.diagram d e →
    Spec.Equiv (Diagram.spec r d) (Diagram.spec r e)
  continuation : {P : Boundary Ty} → {Qs : Exits Ty} → {k k' : Continuation S P Qs} →
    T.continuation k k' → Spec.Equiv (Continuation.spec r k) (Continuation.spec r k')

variable {r} {T : Rules S}

mutual

/-- A derivation gives a cartesian map of the specifications of its two diagrams, in each
direction. -/
def Diagram.Derivation.spec (ok : Rules.SpecSound r T) : {Γ : List Ty} → {Qs : Exits Ty} →
    {d e : Diagram S Γ Qs} → Diagram.Derivation T d e → Spec.Equiv (Diagram.spec r d) (Diagram.spec r e)
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

def Continuation.Derivation.spec (ok : Rules.SpecSound r T) : {P : Boundary Ty} → {Qs : Exits Ty} →
    {k k' : Continuation S P Qs} → Continuation.Derivation T k k' →
    Spec.Equiv (Continuation.spec r k) (Continuation.spec r k')
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
def Diagram.Derivation.verified (ok : Rules.SpecSound r T) {Γ : List Ty} {Qs : Exits Ty}
    {d e : Diagram S Γ Qs} (h : Diagram.Derivation T d e)
    {q : DepPoly.{0, 0, w', z'} ((Diagram.interface X Γ Qs).runtime R E)} (v : d.Verified r q) :
    e.Verified r q :=
  fun a pre =>
    ⟨((h.spec ok).1 a (v a pre).1).1,
      fun o run => (v a pre).2 o ((((h.spec ok).1 a (v a pre).1).2 o).to run)⟩

end Draft

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R E : Type}
  (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E))
  {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty}

/-- A witness of the composite of an exit past a continuation and that continuation. No run
reaches the continuation, so the witness has no witness of the continuation. -/
def Diagram.exitPastPre (out : Qs.At (Port Γ)) (next : Continuation S K Qs) (a : All X Γ × R) :
    (Diagram.spec r (Diagram.seq (.exit (out.there K)) next)).Pre a :=
  ⟨PUnit.unit, fun _ e =>
    Identity.transport
      (fun m => Spec.resumePre (fun (y : Exits.At (K :: Qs) X × R) =>
        Spec.exitPre (fun k => (Continuation.spec r next).Pre (k, y.2)) y.1) m) e.down PUnit.unit⟩

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
