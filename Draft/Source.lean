import Draft.Diagram

/-! Source diagrams of the fragment with fixed occurrences.

A diagram of the fragment is one sequence of steps and one exit. The output boundary of each
step has one case: the type of its cases has a center, and each case is identical to the
center. The evidence is a function of the diagram, by a recursion on it. The action of a port
map keeps the fragment. The operations of a diagram of the fragment are a list, in the order of
its steps.

The dependency graph of a diagram of the fragment is the list of the occurrences of its steps.
An occurrence has the name of the step, its call of the request interface at the producers of
its operands, and the effectful step before it. The producer of an operand is the name of a
step, or no name for an input of the diagram. The occurrences are the calls of the diagram at
the names: each step gives its name to its output ports. The container of the graph has a shape
for each occurrence and a position for each operand.

The graph is a specification of the runs of its steps, with the list of the done steps as the
runtime. A step is admitted when it is not done, the producer of each operand is done, and the
effectful step before it is done. The response has the list with the step. A word of steps is
an admissible order when it has evidence of this specification, with each step done at its
end. The precondition has a decision, so a word has its evidence by computation. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude Container

namespace Draft

variable {Ty : Type} {S : Signature Ty}

/-- The evidence that a diagram is one sequence of steps and one exit. A step has the center
of the cases of its output boundary, the identity of each case with the center, and the
evidence of its rest at the center. -/
def Diagram.Straight : {Γ : List Ty} → {Qs : Exits Ty} → Diagram S Γ Qs → Type
  | _, _, .exit _ => Unit
  | _, _, .step call rest =>
      (center : (S.output call.1).Case) ×
        (((c : (S.output call.1).Case) → center ≡ c) × Diagram.Straight (rest center))
  | _, _, .seq _ _ => Empty

/-- The action of a port map keeps the fragment. -/
def Diagram.Straight.rename : {Γ Δ : List Ty} → {Qs : Exits Ty} → (ρ : PortMap Γ Δ) →
    (d : Diagram S Δ Qs) → d.Straight → (d.rename ρ).Straight
  | _, _, _, _, .exit _, _ => ()
  | _, _, _, ρ, .step _ rest, h => ⟨h.1, h.2.1, rename (ρ.lift h.1.1) (rest h.1) h.2.2⟩
  | _, _, _, _, .seq _ _, h => nomatch h

/-- The operations of a diagram of the fragment, in the order of its steps. -/
def Diagram.ops : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) → d.Straight →
    List S.Op
  | _, _, .exit _, _ => []
  | _, _, .step call rest, h => call.1 :: Diagram.ops (rest h.1) h.2.2
  | _, _, .seq _ _, _ => []

/-! The dependency graph. -/

/-- An occurrence of a step in a dependency graph with names of the type `N`: the name of the
step, its call of the request interface at the producers of its operands, and the effectful
step before it. -/
abbrev Signature.Occurrence (S : Signature Ty) (N : Type) : Type :=
  N × ((S.interface (fun _ => Option N)).Shape × Option N)

/-- The effectful step before a step of a kind. A pure step has none. -/
def Kind.before {N : Type} : Kind → Option N → Option N
  | .pure, _ => none
  | .effectful, last => last

/-- The last effectful step after a step of a kind with a name. -/
def Kind.last {N : Type} : Kind → Option N → N → Option N
  | .pure, last, _ => last
  | .effectful, _, n => some n

/-- The occurrences of the steps of a diagram of the fragment, for the producer of each port of
its context, the last effectful step before it, and a name for each step. Each step gives its
name to its output ports. -/
def Diagram.occurrences {N : Type} : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    d.Straight → All (fun _ => Option N) Γ → Option N → List N → List (S.Occurrence N)
  | _, _, .exit _, _, _, _, _ => []
  | _, _, .step _ _, _, _, _, [] => []
  | _, _, .step call rest, h, env, last, n :: names =>
      (n, ⟨call.1, env.select call.2⟩, Kind.before (S.kind call.1) last) ::
        Diagram.occurrences (rest h.1) h.2.2
          ((All.tabulate h.1.1 fun _ _ => some n).append env)
          (Kind.last (S.kind call.1) last n) names
  | _, _, .seq _ _, _, _, _, _ => []

/-- The numbers of the steps of a diagram of the fragment, from a first number. -/
def Diagram.numbers : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) → d.Straight →
    Nat → List Nat
  | _, _, .exit _, _, _ => []
  | _, _, .step _ rest, h, k => k :: Diagram.numbers (rest h.1) h.2.2 (k + 1)
  | _, _, .seq _ _, _, _ => []

/-- The dependency graph of a diagram of the fragment: the occurrences of its steps, with the
number of each step as its name. Each port of the context is an input. -/
def Diagram.graph {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs) (h : d.Straight) :
    List (S.Occurrence Nat) :=
  d.occurrences h (All.tabulate Γ fun _ _ => none) none (d.numbers h 0)

section Graph

variable {N : Type} (G : List (S.Occurrence N))

/-- The container of a dependency graph: a shape for each occurrence, and a position for each
operand. -/
def Signature.incidence : Container where
  Shape := (a : S.Occurrence N) × Elem a G
  Pos s := (t : Ty) × Port (S.input s.1.2.1.1) t

/-- The producer of each operand: the name of a step, or no name for an input. -/
def Signature.producer (s : (Signature.incidence G).Shape) (p : (Signature.incidence G).Pos s) :
    Option N :=
  s.1.2.1.2.lookup p.2

/-- A producer is in the list of the done steps, or the operand is an input. -/
def Signature.Produced (done : List N) : Option N → Type
  | none => Unit
  | some m => Elem m done

/-- The interface of the runs of a dependency graph: one call for each occurrence. -/
def Signature.runs : Container := ⟨(a : S.Occurrence N) × Elem a G, fun _ => Unit⟩

/-- The dependency graph as a specification of the runs of its steps, with the list of the done
steps as the runtime. A step is admitted when it is not done, the producer of each operand is
done, and the effectful step before it is done. The response has the list with the step. -/
def Signature.admissible : DepPoly.{0, 0, 0, 0} ((Signature.runs G).runtime (List N) Empty) where
  Pre a :=
    (Elem a.1.1.1 a.2 → Empty) ×
      (((p : (Signature.incidence G).Pos a.1) →
          Signature.Produced a.2 (Signature.producer G a.1 p)) ×
        Signature.Produced a.2 a.1.1.2.2)
  Post a _ := fun
    | .inl _ => Empty
    | .inr next => next.2 ≡ a.1.1.1 :: a.2

/-- The condition at the end of a word: each step of the graph is done. -/
def Signature.Finished : Empty ⊕ (Unit × List N) → Type
  | .inl _ => Empty
  | .inr out => (a : S.Occurrence N) → Elem a G → Elem a.1 out.2

/-- The word of a list of steps: one run for each step. -/
def Signature.word : List (Signature.runs G).Shape → Free (Signature.runs G) Unit
  | [] => .pure ()
  | s :: rest => .request s fun _ => Signature.word rest

variable {G}

/-- The evidence of one run and then the rest: a witness of the precondition, and the evidence
of the rest from the list with the step. -/
def Signature.ran {Q : Empty ⊕ (Unit × List N) → Type} (s : (Signature.runs G).Shape)
    (done : List N) {rest : Free (Signature.runs G) Unit}
    (pre : (Signature.admissible G).Pre (s, done))
    (next : FreeDep (Signature.admissible G) Q (rest.thread (E := Empty) (s.1.1 :: done))) :
    FreeDep (Signature.admissible G) Q
      ((Free.request (C := Signature.runs G) s fun _ => rest).thread done) :=
  FreeDep.request (r := Signature.admissible G) (shape := (s, done))
    (next := Sum.elim (fun stopped => .pure (.inl stopped))
      (fun (b : Unit × List N) => rest.thread b.2))
    pre
    fun b =>
      Sum.casesOn
        (motive := fun b => (Signature.admissible G).Post (s, done) pre b →
          FreeDep (Signature.admissible G) Q
            (Sum.elim (fun stopped => Free.pure (.inl stopped))
              (fun (b : Unit × List N) => rest.thread b.2) b))
        b (fun _ post => post.elim)
        (fun _ post =>
          Identity.transport (fun l => FreeDep (Signature.admissible G) Q (rest.thread l))
            post.symm next)

variable [DecEq N]

/-- The decision that one producer is done. -/
def Signature.produced? (done : List N) : (x : Option N) → Option (Signature.Produced done x)
  | none => some ()
  | some m =>
      match Elem.find m done with
      | .yes i => some i
      | .no _ => none

/-- The decision that the producer of each operand is done. -/
def Signature.producedAll? (done : List N) : {Δ : List Ty} →
    (args : All (fun _ => Option N) Δ) →
    Option ((t : Ty) → (p : Port Δ t) → Signature.Produced done (args.lookup p))
  | _, .nil => some (fun _ p => Elem.ofNil p)
  | _, .cons x xs =>
      match Signature.produced? done x with
      | none => none
      | some first =>
          match Signature.producedAll? done xs with
          | none => none
          | some others =>
              some (fun _ p =>
                Elem.consCases
                  (motive := fun _ i =>
                    Signature.Produced done
                      ((All.cons (P := fun _ => Option N) x xs).lookup i))
                  p first others)

/-- The decision of the precondition of a run. -/
def Signature.admit? (s : (Signature.runs G).Shape) (done : List N) :
    Option ((Signature.admissible G).Pre (s, done)) :=
  match Elem.find s.1.1 done with
  | .yes _ => none
  | .no fresh =>
      match Signature.producedAll? done s.1.2.1.2 with
      | none => none
      | some operands =>
          match Signature.produced? done s.1.2.2 with
          | none => none
          | some before => some (fresh, fun p => operands p.1 p.2, before)

/-- The decision that each step of a list of occurrences is done. -/
def Signature.finished? (done : List N) : (H : List (S.Occurrence N)) →
    Option ((a : S.Occurrence N) → Elem a H → Elem a.1 done)
  | [] => some (fun _ i => Elem.ofNil i)
  | b :: H =>
      match Elem.find b.1 done with
      | .no _ => none
      | .yes first =>
          match Signature.finished? done H with
          | none => none
          | some others =>
              some (fun _ i =>
                Elem.consCases (motive := fun c _ => Elem c.1 done) i first others)

/-- The occurrence with a name in a list of occurrences, when the list has one. -/
def Signature.named? (n : N) : (H : List (S.Occurrence N)) →
    Option ((a : S.Occurrence N) × Elem a H)
  | [] => none
  | b :: H =>
      match decideEq n b.1 with
      | .yes _ => some ⟨b, .here⟩
      | .no _ =>
          match Signature.named? n H with
          | none => none
          | some found => some ⟨found.1, .there found.2⟩

/-- The evidence that a word of steps is an admissible order from a list of done steps, when it
is one. -/
def Signature.accept : (w : List (Signature.runs G).Shape) → (done : List N) →
    Option (FreeDep (Signature.admissible G) (Signature.Finished G)
      ((Signature.word G w).thread (E := Empty) done))
  | [], done =>
      match Signature.finished? done G with
      | none => none
      | some all => some (.pure all)
  | s :: rest, done =>
      match Signature.admit? s done with
      | none => none
      | some pre =>
          match Signature.accept rest (s.1.1 :: done) with
          | none => none
          | some next => some (Signature.ran s done pre next)

end Graph

end Draft
