import Draft.Diagram

/-! Source diagrams of the fragment with fixed occurrences.

A diagram of the fragment is one sequence of steps and one exit. The output boundary of each
step has one case: the type of its cases has a center, and each case is identical to the
center. The evidence is a function of the diagram, by a recursion on it. The action of a port
map keeps the fragment. The operations of a diagram of the fragment are a list, in the order of
its steps.

The dependency graph of a diagram of the fragment has no names. A value is its history: an
input of the diagram, or an output port of the call that made it. A call has the histories of
its operands and the effectful call before it, which is the state edge of the graph. The graph
is the list of the occurrences of the steps of the diagram: each step is a call at the
histories of its context, and its output ports have that call as their history. The container
of the graph has a shape for each occurrence and a position for each operand. The occurrences
of a diagram with renamed ports are the occurrences of the diagram at the selected histories.

The graph is a specification of the runs of its steps. The runtime has the list of the
remaining occurrences and the list of the done occurrences. A run has the number of an
occurrence in the list of the remaining occurrences. It is admitted when the call of each
operand is done, and the effectful call before it is done. The response has the remaining list
without the occurrence and the done list with it. A word of runs is an admissible order when it
has evidence of this specification, with no remaining occurrence at its end. Each occurrence
thus has one run. The element of a take and each other element are elements of the list. For a
list with no element at two positions, the other elements have no element at two positions, and
the element of the take is not one of them.

Two calls of a pure operation at the same ports are one call in the merged diagram. The merge
goes through the steps one time, from the first step. It has the list of the available calls:
the calls of pure operations in the steps before, each with its ports and its output ports in
the context of the merged diagram, and a port map from the context of the source diagram to
that context. A step whose operation and ports are those of an available call is not a step of
the merged diagram: the rest has the output ports of the available call. Each other step is a
step of the merged diagram, and its call is available to the rest when its operation is pure.
The decision uses the identity of two operations and the identity of two ports.

The merged diagram has a derivation from the source diagram, in each rule set that has the
interchange rule and the copy rule. The proof is one recursion on the diagram, for a context of
diagrams that absorbs each available call: in the context, a step at the ports of the call is
the rest with the output ports of the call. The context under a step absorbs the call of that
step by the copy rule. It absorbs each earlier call by one interchange and the absorption of
the context before.

The merged diagram is a diagram of the fragment, and its occurrences have no element at two
positions. The proof has a state of the merge at each point: the calls of the steps before, the
histories of the context, and the last effectful call. Each call of a history of the context is
one of those calls, each of those calls with a pure operation is an available call, each of
those calls with an effectful operation has less effectful calls before it than the last
effectful call has, and no history is at two ports. The call of a step that the search does not
find is thus not one of those calls. The search finds an available call for its own operation
and ports, because the type of the operations has one identity proof for each two
operations.

The graph of the merged diagram has a link to the graph of the source diagram. A position of an
occurrence in the graph of the source diagram gives a position of that occurrence in the graph
of the merged diagram, and a position in the graph of the merged diagram gives a position in
the graph of the source diagram. The proof has a link for each available call: its call is a
call of a step before, and its output ports have the histories of the output ports of that
call. A step of the merged diagram has the occurrence of the step of the source diagram. A step
that the search finds has the occurrence of the available call, and the rest has the histories
of the source diagram at the output ports of that call. -/

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

mutual

/-- The history of a value: an input of the source diagram, or an output port of a call at an
output case. -/
inductive History (S : Signature Ty) (Γ₀ : List Ty) : Ty → Type where
  | input {t : Ty} (p : Port Γ₀ t) : History S Γ₀ t
  | output {t : Ty} {o : S.Op} (call : Call S Γ₀ o) (c : (S.output o).Case) (q : Port c.1 t) :
      History S Γ₀ t

/-- A call of an operation: the histories of its operands, and the effectful call before it. A
pure call has no effectful call before it. -/
inductive Call (S : Signature Ty) (Γ₀ : List Ty) : S.Op → Type where
  | mk {o : S.Op} (args : All (History S Γ₀) (S.input o)) (before : Option (Effect S Γ₀)) :
      Call S Γ₀ o

/-- An effectful call. -/
inductive Effect (S : Signature Ty) (Γ₀ : List Ty) : Type where
  | after {o : S.Op} (call : Call S Γ₀ o) : Effect S Γ₀

end

variable {Γ₀ : List Ty}

/-- An occurrence of a step: its operation with its call. -/
abbrev Signature.Occurrence (S : Signature Ty) (Γ₀ : List Ty) : Type :=
  (o : S.Op) × Call S Γ₀ o

/-- The histories of the operands of a call. -/
def Call.args {o : S.Op} : Call S Γ₀ o → All (History S Γ₀) (S.input o)
  | .mk args _ => args

/-- The effectful call before a call. -/
def Call.before {o : S.Op} : Call S Γ₀ o → Option (Effect S Γ₀)
  | .mk _ before => before

/-- The effectful call before a step of a kind. A pure step has none. -/
def Kind.before {N : Type} : Kind → Option N → Option N
  | .pure, _ => none
  | .effectful, last => last

/-- The last effectful call after a step of a kind. -/
def Kind.last {N : Type} : Kind → Option N → N → Option N
  | .pure, last, _ => last
  | .effectful, _, n => some n

/-- The effectful call before the second of two steps does not change when the first step moves
past it: one of the two kinds is the pure kind. -/
def Kind.beforeSecond {N : Type} : (k l : Kind) → ((k ≡ .pure) ⊕ (l ≡ .pure)) →
    (last : Option N) → (x : N) → Kind.before l (Kind.last k last x) ≡ Kind.before l last
  | .pure, .pure, _, _, _ => .refl
  | .pure, .effectful, _, _, _ => .refl
  | .effectful, .pure, _, _, _ => .refl
  | .effectful, .effectful, .inl e, _, _ => nomatch e
  | .effectful, .effectful, .inr e, _, _ => nomatch e

/-- The same for the first of the two steps. -/
def Kind.beforeFirst {N : Type} : (k l : Kind) → ((k ≡ .pure) ⊕ (l ≡ .pure)) →
    (last : Option N) → (y : N) → Kind.before k (Kind.last l last y) ≡ Kind.before k last
  | .pure, .pure, _, _, _ => .refl
  | .pure, .effectful, _, _, _ => .refl
  | .effectful, .pure, _, _, _ => .refl
  | .effectful, .effectful, .inl e, _, _ => nomatch e
  | .effectful, .effectful, .inr e, _, _ => nomatch e

/-- The last effectful call after two steps does not change with their order, when one of the
two kinds is the pure kind. -/
def Kind.lastSwap {N : Type} : (k l : Kind) → ((k ≡ .pure) ⊕ (l ≡ .pure)) →
    (last : Option N) → (x y : N) →
    Kind.last l (Kind.last k last x) y ≡ Kind.last k (Kind.last l last y) x
  | .pure, .pure, _, _, _, _ => .refl
  | .pure, .effectful, _, _, _, _ => .refl
  | .effectful, .pure, _, _, _, _ => .refl
  | .effectful, .effectful, .inl e, _, _, _ => nomatch e
  | .effectful, .effectful, .inr e, _, _, _ => nomatch e

/-- The histories of a context after a call at an output case: the output ports of the call,
and then the histories of the context before it. -/
def Call.outputs {o : S.Op} (call : Call S Γ₀ o) (c : (S.output o).Case) {Γ : List Ty}
    (env : All (History S Γ₀) Γ) : All (History S Γ₀) (c.1 ++ Γ) :=
  (All.tabulate c.1 fun _ q => History.output call c q).append env

/-- The call of a step at the histories of its context, after the last effectful call. -/
def Call.at (o : S.Op) {Γ : List Ty} (args : PortMap Γ (S.input o)) (env : All (History S Γ₀) Γ)
    (last : Option (Effect S Γ₀)) : Call S Γ₀ o :=
  .mk (env.select args) (Kind.before (S.kind o) last)

/-- The last effectful call after a call. -/
def Call.next {o : S.Op} (call : Call S Γ₀ o) (last : Option (Effect S Γ₀)) :
    Option (Effect S Γ₀) :=
  Kind.last (S.kind o) last (.after call)

/-- The occurrences of the steps of a diagram of the fragment at the histories of its context,
after the last effectful call. Each step is a call at the histories of its context, and its
output ports have that call as their history. -/
def Diagram.occurrences : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    d.Straight → All (History S Γ₀) Γ → Option (Effect S Γ₀) → List (S.Occurrence Γ₀)
  | _, _, .exit _, _, _, _ => []
  | _, _, .step call rest, h, env, last =>
      ⟨call.1, Call.at call.1 call.2 env last⟩ ::
        Diagram.occurrences (rest h.1) h.2.2
          ((Call.at call.1 call.2 env last).outputs h.1 env)
          ((Call.at call.1 call.2 env last).next last)
  | _, _, .seq _ _, _, _, _ => []

/-- The histories of the inputs of a source diagram. -/
def Signature.inputs (S : Signature Ty) (Γ₀ : List Ty) : All (History S Γ₀) Γ₀ :=
  All.tabulate Γ₀ fun _ p => .input p

/-- The dependency graph of a diagram of the fragment: the occurrences of its steps at the
histories of its inputs. -/
def Diagram.graph {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs) (h : d.Straight) :
    List (S.Occurrence Γ) :=
  d.occurrences h (S.inputs Γ) none

/-- The occurrences of a diagram with renamed ports are the occurrences of the diagram at the
selected histories. -/
def Diagram.occurrencesRename : {Γ Δ : List Ty} → {Qs : Exits Ty} → (ρ : PortMap Γ Δ) →
    (d : Diagram S Δ Qs) → (h : d.Straight) → (env : All (History S Γ₀) Γ) →
    (last : Option (Effect S Γ₀)) →
    (d.rename ρ).occurrences (Diagram.Straight.rename ρ d h) env last ≡
      d.occurrences h (env.select ρ) last
  | _, _, _, _, .exit _, _, _, _ => .refl
  | _, _, _, ρ, .step call rest, h, env, last =>
      (Identity.cong
          (fun tail =>
            (⟨call.1, Call.at call.1 (ρ.select call.2) env last⟩ : S.Occurrence Γ₀) :: tail)
          ((Diagram.occurrencesRename (ρ.lift h.1.1) (rest h.1) h.2.2
              ((Call.at call.1 (ρ.select call.2) env last).outputs h.1 env)
              ((Call.at call.1 (ρ.select call.2) env last).next last)).trans
            (Identity.cong
              (fun vals =>
                Diagram.occurrences (rest h.1) h.2.2 vals
                  ((Call.at call.1 (ρ.select call.2) env last).next last))
              (PortMap.selectLift _ env ρ)))).trans
        (Identity.cong
          (fun (args : All (History S Γ₀) (S.input call.1)) =>
            ((⟨call.1, .mk args (Kind.before (S.kind call.1) last)⟩ : S.Occurrence Γ₀) ::
              Diagram.occurrences (rest h.1) h.2.2
                ((Call.mk args (Kind.before (S.kind call.1) last)).outputs h.1
                  (env.select ρ))
                ((Call.mk args (Kind.before (S.kind call.1) last)).next last)))
          (All.selectSelect env ρ call.2))
  | _, _, _, _, .seq _ _, h, _, _ => nomatch h

/-- The occurrences of the rest of a step at a case are the occurrences at the center of the
cases. -/
def Diagram.occurrencesCase {o : S.Op} {Γ : List Ty} {Qs : Exits Ty}
    (rest : (c : (S.output o).Case) → Diagram S (c.1 ++ Γ) Qs) {center c : (S.output o).Case}
    (p : center ≡ c) (tail : (rest center).Straight) (call : Call S Γ₀ o)
    (env : All (History S Γ₀) Γ) (last : Option (Effect S Γ₀)) :
    (rest center).occurrences tail (call.outputs center env) last ≡
      (rest c).occurrences (Identity.transport (fun c => (rest c).Straight) p tail)
        (call.outputs c env) last :=
  Identity.ind
    (fun c p =>
      (rest center).occurrences tail (call.outputs center env) last ≡
        (rest c).occurrences (Identity.transport (fun c => (rest c).Straight) p tail)
          (call.outputs c env) last)
    .refl p

/-- The container of a dependency graph: a shape for each occurrence, and a position for each
operand. -/
def Signature.incidence (G : List (S.Occurrence Γ₀)) : Container where
  Shape := (a : S.Occurrence Γ₀) × Elem a G
  Pos s := (t : Ty) × Port (S.input s.1.1) t

/-- The producer of each operand: its history. -/
def Signature.producer (G : List (S.Occurrence Γ₀)) (s : (Signature.incidence G).Shape)
    (p : (Signature.incidence G).Pos s) : History S Γ₀ p.1 :=
  s.1.2.args.lookup p.2

/-! The specification of the runs. -/

/-- The element at a number in a list, with the other elements in their order. -/
def takeAt {α : Type} : Nat → List α → Option (α × List α)
  | _, [] => none
  | 0, a :: rest => some (a, rest)
  | k + 1, a :: rest => (takeAt k rest).map fun found => (found.1, a :: found.2)

section Take

variable {α : Type}

/-- The element of a take is an element of the list, and each other element of the take is an
element of the list. -/
def takeAt.elems : (k : Nat) → (xs : List α) → {y : α} → {ys : List α} →
    takeAt k xs ≡ some (y, ys) → Elem y xs × ((x : α) → Elem x ys → Elem x xs)
  | 0, [], _, _, p => (Identity.noneNotSome p).elim
  | _ + 1, [], _, _, p => (Identity.noneNotSome p).elim
  | 0, z :: rest, _, _, p =>
      Identity.ind (a := (z, rest))
        (fun (r : α × List α) _ =>
          Elem r.1 (z :: rest) × ((x : α) → Elem x r.2 → Elem x (z :: rest)))
        (.here, fun _ i => .there i) (Identity.someInject p)
  | k + 1, z :: rest, _, _, p =>
      let m := Identity.ofMapSome (takeAt k rest) p
      let ih := takeAt.elems k rest (y := m.1.1) (ys := m.1.2) m.2.1
      Identity.ind (a := (m.1.1, z :: m.1.2))
        (fun (r : α × List α) _ =>
          Elem r.1 (z :: rest) × ((x : α) → Elem x r.2 → Elem x (z :: rest)))
        (.there ih.1, fun x i =>
          match Elem.uncons i with
          | .inl same => Identity.transport (fun w => Elem w (z :: rest)) same.symm .here
          | .inr j => .there (ih.2 x j))
        m.2.2

/-- The other elements of a take of a list with no element at two positions have no element at
two positions, and the element of the take is not one of them. -/
def takeAt.distinct : (k : Nat) → (xs : List α) → {y : α} → {ys : List α} →
    takeAt k xs ≡ some (y, ys) → Elem.Distinct xs → Elem.Distinct ys × (Elem y ys → Empty)
  | 0, [], _, _, p, _ => (Identity.noneNotSome p).elim
  | _ + 1, [], _, _, p, _ => (Identity.noneNotSome p).elim
  | 0, z :: rest, _, _, p, d =>
      Identity.ind (a := (z, rest))
        (fun (r : α × List α) _ => Elem.Distinct r.2 × (Elem r.1 r.2 → Empty))
        (d.tail, d.fresh) (Identity.someInject p)
  | k + 1, z :: rest, _, _, p, d =>
      let m := Identity.ofMapSome (takeAt k rest) p
      let e := takeAt.elems k rest (y := m.1.1) (ys := m.1.2) m.2.1
      let ih := takeAt.distinct k rest (y := m.1.1) (ys := m.1.2) m.2.1 d.tail
      Identity.ind (a := (m.1.1, z :: m.1.2))
        (fun (r : α × List α) _ => Elem.Distinct r.2 × (Elem r.1 r.2 → Empty))
        (Elem.Distinct.cons ih.1 (fun i => d.fresh (e.2 z i)), fun i =>
          match Elem.uncons i with
          | .inl same => d.fresh (Identity.transport (fun w => Elem w rest) same e.1)
          | .inr j => ih.2 j)
        m.2.2

/-- No element of the first list has two positions, and no element has a position in each of
the two lists. -/
def Separate (xs done : List α) : Type :=
  Elem.Distinct xs × ((x : α) → Elem x xs → Elem x done → Empty)

/-- The lists after a take are separate: the other elements, and the done elements with the
element of the take. -/
def Separate.take {k : Nat} {xs done : List α} {y : α} {ys : List α}
    (p : takeAt k xs ≡ some (y, ys)) (s : Separate xs done) : Separate ys (y :: done) :=
  ((takeAt.distinct k xs p s.1).1, fun x i j =>
    match Elem.uncons j with
    | .inl same =>
        (takeAt.distinct k xs p s.1).2 (Identity.transport (fun z => Elem z ys) same i)
    | .inr j' => s.2 x ((takeAt.elems k xs p).2 x i) j')

end Take

/-- A history is produced for a list of done occurrences: it is an input, or its call is in the
list. -/
def History.Produced (done : List (S.Occurrence Γ₀)) : {t : Ty} → History S Γ₀ t → Type
  | _, .input _ => Unit
  | _, .output (o := o) call _ _ => Elem (⟨o, call⟩ : S.Occurrence Γ₀) done

/-- The effectful call before a call is done, or the call has none. -/
def Effect.Produced (done : List (S.Occurrence Γ₀)) : Option (Effect S Γ₀) → Type
  | none => Unit
  | some (.after (o := o) call) => Elem (⟨o, call⟩ : S.Occurrence Γ₀) done

/-- The interface of the runs: a call has the number of an occurrence in the list of the
remaining occurrences. -/
def runs : Container := ⟨Nat, fun _ => Unit⟩

/-- The runtime of the runs of a dependency graph: the remaining occurrences, and the done
occurrences. -/
abbrev Signature.Progress (S : Signature Ty) (Γ₀ : List Ty) : Type :=
  List (S.Occurrence Γ₀) × List (S.Occurrence Γ₀)

/-- The specification of the runs of a dependency graph. A run is admitted when its number has
an occurrence in the list of the remaining occurrences, the call of each operand of that
occurrence is done, and the effectful call before it is done. The response has the remaining
list without the occurrence and the done list with it. -/
def Signature.admissible (S : Signature Ty) (Γ₀ : List Ty) :
    DepPoly.{0, 0, 0, 0} (runs.runtime (S.Progress Γ₀) Empty) where
  Pre a :=
    (found : S.Occurrence Γ₀ × List (S.Occurrence Γ₀)) ×
      ((takeAt a.1 a.2.1 ≡ some found) ×
        (((t : Ty) → (p : Port (S.input found.1.1) t) →
            History.Produced a.2.2 (found.1.2.args.lookup p)) ×
          Effect.Produced a.2.2 found.1.2.before))
  Post a pre := fun
    | .inl _ => Empty
    | .inr next => next.2 ≡ (pre.1.2, pre.1.1 :: a.2.2)

/-- The condition at the end of a word: no occurrence remains. -/
def Signature.Finished (S : Signature Ty) (Γ₀ : List Ty) :
    Empty ⊕ (Unit × S.Progress Γ₀) → Type
  | .inl _ => Empty
  | .inr out => out.2.1 ≡ []

/-- The word of a list of numbers: one run for each number. -/
def word : List Nat → Free runs Unit
  | [] => .pure ()
  | k :: rest => .request k fun _ => word rest

/-- The evidence of one run and then the rest: a witness of the precondition, and the evidence
of the rest from the next runtime. -/
def Signature.ran {Q : Empty ⊕ (Unit × S.Progress Γ₀) → Type} (k : Nat)
    (state : S.Progress Γ₀) {rest : Free runs Unit}
    (pre : (S.admissible Γ₀).Pre (k, state))
    (next : FreeDep (S.admissible Γ₀) Q
      (rest.thread (E := Empty) (pre.1.2, pre.1.1 :: state.2))) :
    FreeDep (S.admissible Γ₀) Q ((Free.request (C := runs) k fun _ => rest).thread state) :=
  FreeDep.request (r := S.admissible Γ₀) (shape := (k, state))
    (next := Sum.elim (fun stopped => .pure (.inl stopped))
      (fun (b : Unit × S.Progress Γ₀) => rest.thread b.2))
    pre
    fun b =>
      Sum.casesOn
        (motive := fun b => (S.admissible Γ₀).Post (k, state) pre b →
          FreeDep (S.admissible Γ₀) Q
            (Sum.elim (fun stopped => Free.pure (.inl stopped))
              (fun (b : Unit × S.Progress Γ₀) => rest.thread b.2) b))
        b (fun _ post => post.elim)
        (fun _ post =>
          Identity.transport (fun st => FreeDep (S.admissible Γ₀) Q (rest.thread st))
            post.symm next)

/-! The merge of the equal calls. -/

/-- An available call: a call of a pure operation in the steps before a point, with its ports,
the one case of its output boundary, and its output ports. -/
structure Available (S : Signature Ty) (Γ : List Ty) where
  op : S.Op
  pure : S.kind op ≡ .pure
  args : PortMap Γ (S.input op)
  center : (S.output op).Case
  only : (c : (S.output op).Case) → center ≡ c
  outs : PortMap Γ center.1

/-- The data of a call that a later step can use: an operation, its ports, a case of its output
boundary, and the output ports of that case. -/
abbrev Used (S : Signature Ty) (Γ : List Ty) : Type :=
  (o : S.Op) × (PortMap Γ (S.input o) × ((c : (S.output o).Case) × PortMap Γ c.1))

namespace Available

variable {Γ : List Ty}

/-- The data of an available call. -/
def used (e : Available S Γ) : Used S Γ := ⟨e.op, e.args, e.center, e.outs⟩

/-- An available call in a context with more ports. -/
def weaken (Ξ : List Ty) (e : Available S Γ) : Available S (Ξ ++ Γ) :=
  ⟨e.op, e.pure, e.args.weaken Ξ, e.center, e.only, PortMap.weaken Ξ e.outs⟩

/-- The call of a step with a pure operation, in the context after the step. -/
def ofStep (f : S.Op) (pure : S.kind f ≡ .pure) (args : PortMap Γ (S.input f))
    (center : (S.output f).Case) (only : (c : (S.output f).Case) → center ≡ c) :
    Available S (center.1 ++ Γ) :=
  ⟨f, pure, args.weaken center.1, center, only,
    All.tabulate (P := Port (center.1 ++ Γ)) center.1 fun _ i => i.left⟩

/-- The available calls after a step: the call of the step when its operation is pure, and
then the calls before the step. -/
def after (table : List (Available S Γ)) (f : S.Op) (args : PortMap Γ (S.input f))
    (center : (S.output f).Case) (only : (c : (S.output f).Case) → center ≡ c) :
    List (Available S (center.1 ++ Γ)) :=
  Sum.casesOn (motive := fun _ => List (Available S (center.1 ++ Γ)))
    (Kind.cases (S.kind f))
    (fun pure => ofStep f pure args center only :: table.map (weaken center.1))
    (fun _ => table.map (weaken center.1))

/-- The case and the output ports of an available call, as a call of an operation at given
ports. -/
abbrev Use (e : Available S Γ) (f : S.Op) (args : PortMap Γ (S.input f)) : Type :=
  (c : (S.output f).Case) × ((outs : PortMap Γ c.1) × (e.used ≡ ⟨f, args, c, outs⟩))

/-- The use of an available call at given ports, for a decision that its ports are those
ports. -/
def usePorts (e : Available S Γ) (args : PortMap Γ (S.input e.op)) :
    Dec (e.args ≡ args) → Option (e.Use e.op args)
  | .no _ => none
  | .yes samePorts =>
      Identity.ind (fun (args : PortMap Γ (S.input e.op)) _ => Option (e.Use e.op args))
        (some ⟨e.center, e.outs, .refl⟩) samePorts

/-- The use of an available call for an operation, for a decision that its operation is that
operation, and then the decision of the identity of the ports. -/
def useOp (e : Available S Γ) (f : S.Op) :
    Dec (e.op ≡ f) → (args : PortMap Γ (S.input f)) → Option (e.Use f args)
  | .no _ => fun _ => none
  | .yes sameOp =>
      Identity.ind (fun (f : S.Op) _ => (args : PortMap Γ (S.input f)) → Option (e.Use f args))
        (fun args => e.usePorts args (All.decide (fun _ => Elem.decide) e.args args)) sameOp

/-- The use of an available call, when it is a call of the operation at the ports. -/
def use [DecEq S.Op] (e : Available S Γ) (f : S.Op) (args : PortMap Γ (S.input f)) :
    Option (e.Use f args) :=
  e.useOp f (decideEq e.op f) args

/-- An available call of a list that is a call of an operation at given ports, with its case
and its output ports. -/
structure Found (table : List (Available S Γ)) (f : S.Op) (args : PortMap Γ (S.input f)) where
  entry : Available S Γ
  mem : Elem entry table
  center : (S.output f).Case
  outs : PortMap Γ center.1
  same : entry.used ≡ ⟨f, args, center, outs⟩

/-- A found call of a list, in the list with one more first call. -/
def Found.there {table : List (Available S Γ)} {f : S.Op} {args : PortMap Γ (S.input f)}
    (e : Available S Γ) (found : Found table f args) : Found (e :: table) f args :=
  ⟨found.entry, .there found.mem, found.center, found.outs, found.same⟩

/-- The first call of a list as the found call, from its use. -/
def Found.here {table : List (Available S Γ)} {f : S.Op} {args : PortMap Γ (S.input f)}
    (e : Available S Γ) (m : e.Use f args) : Found (e :: table) f args :=
  ⟨e, .here, m.1, m.2.1, m.2.2⟩

/-- The first available call of a list that is a call of the operation at the ports. -/
def find [DecEq S.Op] (f : S.Op) (args : PortMap Γ (S.input f)) :
    (table : List (Available S Γ)) → Option (Found table f args)
  | [] => none
  | e :: rest =>
      Option.casesOn (motive := fun _ => Option (Found (e :: rest) f args)) (e.use f args)
        ((find f args rest).map (Found.there e))
        (fun m => some (Found.here e m))

end Available

/-- The step with one output case, with a diagram at the center of the cases as its rest. -/
def Diagram.under {Γ : List Ty} {Qs : Exits Ty} (f : S.Op) (args : PortMap Γ (S.input f))
    (center : (S.output f).Case) (only : (c : (S.output f).Case) → center ≡ c)
    (D : Diagram S (center.1 ++ Γ) Qs) : Diagram S Γ Qs :=
  .step ⟨f, args⟩ fun c =>
    Identity.transport (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) (only c) D

/-- The merge of a diagram of the fragment at a list of available calls and a port map to the
context of the merged diagram. -/
def Diagram.mergeWith [DecEq S.Op] : {Γ Δ : List Ty} → {Qs : Exits Ty} →
    List (Available S Γ) → PortMap Γ Δ → (d : Diagram S Δ Qs) → d.Straight → Diagram S Γ Qs
  | _, _, _, _, ρ, .exit out, _ => .exit (out.select ρ)
  | Γ, _, Qs, table, ρ, .step call rest, h =>
      Option.casesOn (motive := fun _ => Diagram S Γ Qs)
        (Available.find call.1 (ρ.select call.2) table)
        (Diagram.under call.1 (ρ.select call.2) h.1 h.2.1
          (Diagram.mergeWith (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
            (ρ.lift h.1.1) (rest h.1) h.2.2))
        (fun found =>
          Diagram.mergeWith table (found.outs.append ρ) (rest found.center)
            (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center) h.2.2))
  | _, _, _, _, _, .seq _ _, h => nomatch h

/-- The merge of the equal calls of a diagram of the fragment. -/
def Diagram.merge [DecEq S.Op] {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs)
    (h : d.Straight) : Diagram S Γ Qs :=
  Diagram.mergeWith [] (PortMap.id Γ) d h

/-! The derivation of the merged diagram. -/

variable {R : Rules S}

/-- A context of diagrams absorbs the data of a call: in the context, a step of the operation
at the ports is the rest at the case, with the output ports in the place of the output ports
of the step. -/
def Absorbed (R : Rules S) {Γ Γ₀ : List Ty} {Qs : Exits Ty}
    (K : Diagram S Γ Qs → Diagram S Γ₀ Qs) (k : Used S Γ) : Type :=
  (D : (c : (S.output k.1).Case) → Diagram S (c.1 ++ Γ) Qs) →
    Diagram.Derivation R (K (.step ⟨k.1, k.2.1⟩ D))
      (K (Diagram.rename (k.2.2.2.append (PortMap.id Γ)) (D k.2.2.1)))

/-- The derivations are a congruence for the step with one output case. -/
def Diagram.Derivation.under {Γ : List Ty} {Qs : Exits Ty} (f : S.Op)
    (args : PortMap Γ (S.input f)) (center : (S.output f).Case)
    (only : (c : (S.output f).Case) → center ≡ c) {D D' : Diagram S (center.1 ++ Γ) Qs}
    (der : Diagram.Derivation R D D') :
    Diagram.Derivation R (Diagram.under f args center only D)
      (Diagram.under f args center only D') :=
  .step ⟨f, args⟩ fun c =>
    Identity.ind
      (fun (c : (S.output f).Case) (p : center ≡ c) =>
        Diagram.Derivation R
          (Identity.transport (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) p D)
          (Identity.transport (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) p D'))
      der (only c)

/-- A step with one output case agrees with the step that has the diagram of the center as its
rest. -/
def Diagram.Agreement.under {Γ : List Ty} {Qs : Exits Ty} (f : S.Op)
    (args : PortMap Γ (S.input f)) (center : (S.output f).Case)
    (only : (c : (S.output f).Case) → center ≡ c)
    (rest : (c : (S.output f).Case) → Diagram S (c.1 ++ Γ) Qs) :
    Diagram.Agreement (.step ⟨f, args⟩ rest) (Diagram.under f args center only (rest center)) :=
  .step ⟨f, args⟩ fun c =>
    Identity.ind
      (fun (c : (S.output f).Case) (p : center ≡ c) =>
        Diagram.Agreement (rest c)
          (Identity.transport (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) p
            (rest center)))
      (Diagram.Agreement.refl _) (only c)

section

variable {Γ Γ₀ : List Ty} {Qs : Exits Ty} {K : Diagram S Γ Qs → Diagram S Γ₀ Qs}
  (cong : {D D' : Diagram S Γ Qs} → Diagram.Derivation R D D' →
    Diagram.Derivation R (K D) (K D'))
  (f : S.Op) (args : PortMap Γ (S.input f)) (center : (S.output f).Case)
  (only : (c : (S.output f).Case) → center ≡ c)

/-- The context under a step absorbs the call of the step, by the copy rule. -/
def Absorbed.ofStep (copy : Rules.Map (Rules.copy S) R) (pure : S.kind f ≡ .pure) :
    Absorbed R (fun D => K (Diagram.under f args center only D))
      (Available.ofStep f pure args center only).used :=
  fun D =>
    (cong (.agree (.step ⟨f, args⟩ fun ca =>
        Identity.ind
          (fun (ca : (S.output f).Case) (p : center ≡ ca) =>
            Diagram.Agreement
              (Identity.transport (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) p
                (.step ⟨f, args.weaken center.1⟩ D))
              (.step ⟨f, args.weaken ca.1⟩ fun c' =>
                Identity.transport
                  (fun (c : (S.output f).Case) => Diagram S (c'.1 ++ (c.1 ++ Γ)) Qs) p (D c')))
          (Diagram.Agreement.refl _) (only ca)))).trans
      ((cong (.rule (copy.diagram (.copy f pure args fun ca c' =>
          Identity.transport
            (fun (c : (S.output f).Case) => Diagram S (c'.1 ++ (c.1 ++ Γ)) Qs) (only ca)
            (D c'))))).trans
        (cong (.agree (.step ⟨f, args⟩ fun ca =>
          Identity.ind
            (fun (ca : (S.output f).Case) (p : center ≡ ca) =>
              Diagram.Agreement
                (Diagram.rename (PortMap.copy ca.1 Γ)
                  (Identity.transport
                    (fun (c : (S.output f).Case) => Diagram S (ca.1 ++ (c.1 ++ Γ)) Qs) p
                    (D ca)))
                (Identity.transport (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) p
                  (Diagram.rename (PortMap.copy center.1 Γ) (D center))))
            (Diagram.Agreement.refl _) (only ca)))))

/-- The ports of an available call under more ports, after the exchange with those ports. -/
def Available.underPorts (Ξ : List Ty) (e : Available S Γ) :
    (PortMap.lift Ξ (e.outs.append (PortMap.id Γ))).select (PortMap.exchange Ξ e.center.1 Γ) ≡
      (PortMap.weaken Ξ e.outs).append (PortMap.id (Ξ ++ Γ)) :=
  (Identity.cong
      (fun (m : PortMap (Ξ ++ Γ) (e.center.1 ++ Γ)) =>
        All.select
          ((All.tabulate (P := Port (Ξ ++ Γ)) Ξ (fun _ i => i.left)).append m)
          (PortMap.exchange Ξ e.center.1 Γ))
      (All.mapAppend (fun (t : Ty) (i : Port Γ t) => (i.right Ξ : Port (Ξ ++ Γ) t)) e.outs
        (PortMap.id Γ))).trans
    ((PortMap.selectExchange (All.tabulate (P := Port (Ξ ++ Γ)) Ξ (fun _ i => i.left))
        (PortMap.weaken Ξ e.outs) (PortMap.weaken Ξ (PortMap.id Γ))).trans
      (Identity.cong (All.append (PortMap.weaken Ξ e.outs)) (PortMap.liftId Ξ Γ)))

/-- The context under a step absorbs each call that the context before absorbs: the step of the
call moves before the step of the context by one interchange. -/
def Absorbed.under (inter : Rules.Map (Rules.interchange S) R) (e : Available S Γ)
    (absorbed : Absorbed R K e.used) :
    Absorbed R (fun D => K (Diagram.under f args center only D)) (e.weaken center.1).used :=
  fun D =>
    (cong (.agree (.step ⟨f, args⟩ fun ca =>
        Identity.ind
          (fun (ca : (S.output f).Case) (p : center ≡ ca) =>
            Diagram.Agreement
              (Identity.transport (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) p
                (.step ⟨e.op, e.args.weaken center.1⟩ D))
              (.step ⟨e.op, e.args.weaken ca.1⟩ fun cb =>
                Identity.transport
                  (fun (c : (S.output f).Case) => Diagram S (cb.1 ++ (c.1 ++ Γ)) Qs) p (D cb)))
          (Diagram.Agreement.refl _) (only ca)))).trans
      ((cong (.rule (inter.diagram (.swap f e.op (.inr e.pure) args e.args fun ca cb =>
          Identity.transport
            (fun (c : (S.output f).Case) => Diagram S (cb.1 ++ (c.1 ++ Γ)) Qs) (only ca)
            (D cb))))).trans
        ((absorbed fun cb => .step ⟨f, args.weaken cb.1⟩ fun ca =>
            Diagram.rename (PortMap.exchange ca.1 cb.1 Γ)
              (Identity.transport
                (fun (c : (S.output f).Case) => Diagram S (cb.1 ++ (c.1 ++ Γ)) Qs) (only ca)
                (D cb))).trans
          (cong (.agree (.stepPorts f
            ((PortMap.selectWeaken e.outs (PortMap.id Γ) args).trans (PortMap.idSelect args))
            fun ca =>
              Identity.ind
                (fun (ca : (S.output f).Case) (p : center ≡ ca) =>
                  Diagram.Agreement
                    (Diagram.rename (PortMap.lift ca.1 (e.outs.append (PortMap.id Γ)))
                      (Diagram.rename (PortMap.exchange ca.1 e.center.1 Γ)
                        (Identity.transport
                          (fun (c : (S.output f).Case) =>
                            Diagram S (e.center.1 ++ (c.1 ++ Γ)) Qs) p (D e.center))))
                    (Identity.transport
                      (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) p
                      (Diagram.rename
                        ((PortMap.weaken center.1 e.outs).append (PortMap.id (center.1 ++ Γ)))
                        (D e.center))))
                (Diagram.renameCompose (D e.center) _ _ _ (e.underPorts center.1))
                (only ca))))))

/-- The context under a step absorbs each available call after the step. -/
def Absorbed.after (inter : Rules.Map (Rules.interchange S) R)
    (copy : Rules.Map (Rules.copy S) R) (table : List (Available S Γ))
    (absorbed : All (fun e => Absorbed R K e.used) table) :
    All (fun e => Absorbed R (fun D => K (Diagram.under f args center only D)) e.used)
      (Available.after table f args center only) :=
  Sum.casesOn
    (motive := fun kind =>
      All (fun e => Absorbed R (fun D => K (Diagram.under f args center only D)) e.used)
        (Sum.casesOn (motive := fun _ => List (Available S (center.1 ++ Γ))) kind
          (fun pure =>
            Available.ofStep f pure args center only :: table.map (Available.weaken center.1))
          (fun _ => table.map (Available.weaken center.1))))
    (Kind.cases (S.kind f))
    (fun pure =>
      .cons (Absorbed.ofStep cong f args center only copy pure)
        (All.image (Available.weaken center.1)
          (fun e a => Absorbed.under cong f args center only inter e a) absorbed))
    (fun _ =>
      All.image (Available.weaken center.1)
        (fun e a => Absorbed.under cong f args center only inter e a) absorbed)

end

/-- The merged diagram has a derivation from the diagram with the ports of the map, in each
context that absorbs each available call. -/
def Diagram.mergeWithDerivation [DecEq S.Op] (inter : Rules.Map (Rules.interchange S) R)
    (copy : Rules.Map (Rules.copy S) R) {Γ₀ : List Ty} :
    {Γ Δ : List Ty} → {Qs : Exits Ty} → (K : Diagram S Γ Qs → Diagram S Γ₀ Qs) →
    (cong : {D D' : Diagram S Γ Qs} → Diagram.Derivation R D D' →
      Diagram.Derivation R (K D) (K D')) →
    (table : List (Available S Γ)) → All (fun e => Absorbed R K e.used) table →
    (ρ : PortMap Γ Δ) → (d : Diagram S Δ Qs) → (h : d.Straight) →
    Diagram.Derivation R (K (Diagram.rename ρ d)) (K (Diagram.mergeWith table ρ d h))
  | _, _, _, _, _, _, _, _, .exit _, _ => .agree (Diagram.Agreement.refl _)
  | Γ, _, Qs, K, cong, table, absorbed, ρ, .step call rest, h =>
      Option.casesOn
        (motive := fun found =>
          Diagram.Derivation R
            (K (.step ⟨call.1, ρ.select call.2⟩ fun c => Diagram.rename (ρ.lift c.1) (rest c)))
            (K (Option.casesOn (motive := fun _ => Diagram S Γ Qs) found
              (Diagram.under call.1 (ρ.select call.2) h.1 h.2.1
                (Diagram.mergeWith (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
                  (ρ.lift h.1.1) (rest h.1) h.2.2))
              (fun found =>
                Diagram.mergeWith table (found.outs.append ρ) (rest found.center)
                  (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center)
                    h.2.2)))))
        (Available.find call.1 (ρ.select call.2) table)
        ((cong (.agree (Diagram.Agreement.under call.1 (ρ.select call.2) h.1 h.2.1
            fun c => Diagram.rename (ρ.lift c.1) (rest c)))).trans
          (Diagram.mergeWithDerivation inter copy
            (fun D => K (Diagram.under call.1 (ρ.select call.2) h.1 h.2.1 D))
            (fun der => cong (der.under call.1 (ρ.select call.2) h.1 h.2.1))
            (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
            (Absorbed.after cong call.1 (ρ.select call.2) h.1 h.2.1 inter copy table absorbed)
            (ρ.lift h.1.1) (rest h.1) h.2.2))
        (fun found =>
          ((Identity.transport (Absorbed R K) found.same (absorbed.lookup found.mem))
              fun c => Diagram.rename (ρ.lift c.1) (rest c)).trans
            ((cong (.agree (Diagram.renameCompose (rest found.center) _ _ _
                ((PortMap.selectLift found.outs (PortMap.id Γ) ρ).trans
                  (Identity.cong (All.append found.outs) (PortMap.idSelect ρ)))))).trans
              (Diagram.mergeWithDerivation inter copy K cong table absorbed
                (found.outs.append ρ) (rest found.center)
                (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center) h.2.2))))
  | _, _, _, _, _, _, _, _, .seq _ _, h => nomatch h

/-- The merged diagram of a diagram of the fragment has a derivation from the diagram, in each
rule set that has the interchange rule and the copy rule. -/
def Diagram.mergeDerivation [DecEq S.Op] (inter : Rules.Map (Rules.interchange S) R)
    (copy : Rules.Map (Rules.copy S) R) {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs)
    (h : d.Straight) : Diagram.Derivation R d (d.merge h) :=
  .trans (.symm (.agree d.renameId))
    (Diagram.mergeWithDerivation inter copy (fun D => D) (fun der => der) [] .nil
      (PortMap.id Γ) d h)

/-! The occurrences of the merged diagram. -/

section Merged

variable {Γ₀ : List Ty}

/-- The occurrence of the call of a history, for an output port of a call. -/
def History.source : {t : Ty} → History S Γ₀ t → Option (S.Occurrence Γ₀)
  | _, .input _ => none
  | _, .output (o := o) call _ _ => some ⟨o, call⟩

/-- The number of the port of a history: the input port, or the output port of the call. -/
def History.number : {t : Ty} → History S Γ₀ t → Nat
  | _, .input p => p.toFin.val
  | _, .output _ _ q => q.toFin.val

mutual

/-- The number of the effectful calls before a call. -/
def Call.rank : {o : S.Op} → Call S Γ₀ o → Nat
  | _, .mk _ before => Effect.rank before

/-- The number of the effectful calls of a state edge. -/
def Effect.rank : Option (Effect S Γ₀) → Nat
  | none => 0
  | some (.after call) => Call.rank call + 1

end

section

variable {Γ : List Ty}

/-- The occurrence of a call of a pure operation at ports, for the histories of a context. -/
def Signature.pureAt (env : All (History S Γ₀) Γ) (x : (S.interface (Port Γ)).Shape) :
    S.Occurrence Γ₀ :=
  ⟨x.1, Call.mk (env.select x.2) none⟩

/-- Two calls of pure operations with one occurrence have one operation and the same ports,
when no history of the context is at two ports. -/
def Signature.pureAtInjective (env : All (History S Γ₀) Γ)
    (apart : (t : Ty) → (p q : Port Γ t) → env.lookup p ≡ env.lookup q → p ≡ q)
    (x y : (S.interface (Port Γ)).Shape) (same : S.pureAt env x ≡ S.pureAt env y) : x ≡ y :=
  let code :
      (q : x.1 ≡ y.1) ×
        (Identity.transport (fun o => All (History S Γ₀) (S.input o)) q (env.select x.2) ≡
          env.select y.2) :=
    Identity.ind (a := S.pureAt env x)
      (fun (z : S.Occurrence Γ₀) _ =>
        (q : x.1 ≡ z.1) ×
          (Identity.transport (fun o => All (History S Γ₀) (S.input o)) q (env.select x.2) ≡
            z.2.args))
      ⟨.refl, .refl⟩ same
  Identity.ind (a := x.1)
    (fun (f : S.Op) (q : x.1 ≡ f) => (a : PortMap Γ (S.input f)) →
      Identity.transport (fun o => All (History S Γ₀) (S.input o)) q (env.select x.2) ≡
        env.select a → x ≡ (⟨f, a⟩ : (S.interface (Port Γ)).Shape))
    (fun a same =>
      Identity.cong (fun a => (⟨x.1, a⟩ : (S.interface (Port Γ)).Shape))
        (PortMap.selectInjective env apart x.2 a same))
    code.1 y.2 code.2

namespace Available

/-- An available call has a use at its own ports, for each decision. -/
def usePortsSelf (e : Available S Γ) :
    (d : Dec (e.args ≡ e.args)) → (m : e.Use e.op e.args) × (e.usePorts e.args d ≡ some m)
  | .no refute => (refute .refl).elim
  | .yes same =>
      Identity.ind (a := e.args)
        (fun (args : PortMap Γ (S.input e.op)) (q : e.args ≡ args) =>
          (m : e.Use e.op args) ×
            (Identity.ind (fun (args : PortMap Γ (S.input e.op)) _ => Option (e.Use e.op args))
              (some ⟨e.center, e.outs, .refl⟩) q ≡ some m))
        ⟨⟨e.center, e.outs, .refl⟩, .refl⟩ same

/-- An available call has a use at its own operation and ports, for each decision. The proof of
the decision is the reflexivity proof, because the type of the operations has one identity
proof for each two operations. -/
def useOpSelf [DecEq S.Op] (e : Available S Γ) :
    (d : Dec (e.op ≡ e.op)) → (m : e.Use e.op e.args) × (e.useOp e.op d e.args ≡ some m)
  | .no refute => (refute .refl).elim
  | .yes same =>
      Identity.transport
        (fun (q : e.op ≡ e.op) =>
          (m : e.Use e.op e.args) ×
            (Identity.ind
              (fun (f : S.Op) _ => (args : PortMap Γ (S.input f)) → Option (e.Use f args))
              (fun args => e.usePorts args (All.decide (fun _ => Elem.decide) e.args args))
              q e.args ≡ some m))
        (Dec.unique (fun (x y : S.Op) => decideEq x y) .refl same)
        (e.usePortsSelf (All.decide (fun _ => Elem.decide) e.args e.args))

/-- An available call has a use at each operation and ports that are its operation and its
ports. -/
def useSame [DecEq S.Op] (e : Available S Γ) (x : (S.interface (Port Γ)).Shape)
    (same : (⟨e.op, e.args⟩ : (S.interface (Port Γ)).Shape) ≡ x) :
    (m : e.Use x.1 x.2) × (e.use x.1 x.2 ≡ some m) :=
  Identity.ind (a := (⟨e.op, e.args⟩ : (S.interface (Port Γ)).Shape))
    (fun (x : (S.interface (Port Γ)).Shape) _ => (m : e.Use x.1 x.2) × (e.use x.1 x.2 ≡ some m))
    (e.useOpSelf (decideEq e.op e.op)) same

/-- The search finds an available call for the operation and the ports of each available call
of the list. -/
def findSame [DecEq S.Op] (x : (S.interface (Port Γ)).Shape) :
    (table : List (Available S Γ)) → (e : Available S Γ) → Elem e table →
    (⟨e.op, e.args⟩ : (S.interface (Port Γ)).Shape) ≡ x →
    (found : Found table x.1 x.2) × (find x.1 x.2 table ≡ some found)
  | [], _, i, _ => i.ofNil
  | e' :: rest, e, i, same =>
      Option.casesOn
        (motive := fun o => (e'.use x.1 x.2 ≡ o) →
          (found : Found (e' :: rest) x.1 x.2) ×
            (Option.casesOn (motive := fun _ => Option (Found (e' :: rest) x.1 x.2)) o
              ((find x.1 x.2 rest).map (Found.there e'))
              (fun m => some (Found.here e' m)) ≡ some found))
        (e'.use x.1 x.2)
        (fun none' =>
          match Elem.uncons i with
          | .inl isHead =>
              (Identity.noneNotSome
                (none'.symm.trans
                  (e'.useSame x
                    (Identity.transport
                      (fun (y : Available S Γ) =>
                        (⟨y.op, y.args⟩ : (S.interface (Port Γ)).Shape) ≡ x)
                      isHead same)).2)).elim
          | .inr j =>
              let inner := findSame x rest e j same
              ⟨Found.there e' inner.1, Identity.cong (Option.map (Found.there e')) inner.2⟩)
        (fun m _ => ⟨Found.here e' m, .refl⟩)
        .refl

end Available

/-- The state of the merge at a point of the merged diagram, for the histories of its context,
the last effectful call, and the calls of the steps before the point. Each call of a history of
the context is one of those calls. Each of those calls with a pure operation is an available
call of the list. Each of those calls with an effectful operation has less effectful calls
before it than the last effectful call has. No history is at two ports. -/
structure Merged (table : List (Available S Γ)) (env : All (History S Γ₀) Γ)
    (last : Option (Effect S Γ₀)) (prior : List (S.Occurrence Γ₀)) : Type where
  known : (t : Ty) → (p : Port Γ t) → (x : S.Occurrence Γ₀) →
    History.source (env.lookup p) ≡ some x → Elem x prior
  listed : (x : S.Occurrence Γ₀) → Elem x prior → S.kind x.1 ≡ .pure →
    (e : Available S Γ) × (Elem e table × (S.pureAt env ⟨e.op, e.args⟩ ≡ x))
  ranked : (x : S.Occurrence Γ₀) → Elem x prior → S.kind x.1 ≡ .effectful →
    Call.rank x.2 < Effect.rank last
  apart : (t : Ty) → (p q : Port Γ t) → env.lookup p ≡ env.lookup q → p ≡ q

/-- The state at the start: the histories of the inputs, and no call. -/
def Merged.start (Γ : List Ty) :
    Merged (S := S) ([] : List (Available S Γ)) (S.inputs Γ) none [] where
  known _ p _ src :=
    (Identity.noneNotSome
      ((Identity.cong History.source
          (All.lookupTabulate (fun _ q => (History.input q : History S Γ _)) p)).symm.trans
        src)).elim
  listed _ i _ := i.ofNil
  ranked _ i _ := (Elem.ofNil i : Empty).elim
  apart _ p q same :=
    Elem.sameNumber p q
      (Identity.cong History.number
        ((All.lookupTabulate (fun _ q => (History.input q : History S Γ _)) p).symm.trans
          (same.trans (All.lookupTabulate (fun _ q => (History.input q : History S Γ _)) q))))

variable {table : List (Available S Γ)} {env : All (History S Γ₀) Γ}
  {last : Option (Effect S Γ₀)} {prior : List (S.Occurrence Γ₀)}

/-- The call of a step that the search does not find is not a call of a step before. A pure
call of a step before is an available call with other ports or another operation. An effectful
call of a step before has less effectful calls before it. -/
def Merged.fresh [DecEq S.Op] (m : Merged table env last prior) (f : S.Op)
    (args : PortMap Γ (S.input f)) (missing : Available.find f args table ≡ none)
    (i : Elem (⟨f, Call.at f args env last⟩ : S.Occurrence Γ₀) prior) : Empty :=
  match Kind.cases (S.kind f) with
  | .inl pure =>
      let e := m.listed _ i pure
      Identity.noneNotSome
        (missing.symm.trans
          (Available.findSame ⟨f, args⟩ table e.1 e.2.1
            (S.pureAtInjective env m.apart ⟨e.1.op, e.1.args⟩ ⟨f, args⟩
              (e.2.2.trans
                (Identity.cong
                  (fun k =>
                    (⟨f, Call.mk (env.select args) (Kind.before k last)⟩ : S.Occurrence Γ₀))
                  pure)))).2)
  | .inr effectful =>
      (Nat.lt_irrefl _
        (Identity.transport
          (fun k => Effect.rank (Kind.before k last) < Effect.rank last) effectful
          (m.ranked _ i effectful))).elim

/-- The state after a step of the merged diagram whose call is not a call of a step before. -/
def Merged.after (m : Merged table env last prior) (f : S.Op) (args : PortMap Γ (S.input f))
    (center : (S.output f).Case) (only : (c : (S.output f).Case) → center ≡ c)
    (fresh : Elem (⟨f, Call.at f args env last⟩ : S.Occurrence Γ₀) prior → Empty) :
    Merged (Available.after table f args center only)
      ((Call.at f args env last).outputs center env) ((Call.at f args env last).next last)
      (⟨f, Call.at f args env last⟩ :: prior) :=
  let A : Call S Γ₀ f := Call.at f args env last
  let outs : All (History S Γ₀) center.1 :=
    All.tabulate center.1 fun _ q => History.output A center q
  let newAt {t : Ty} (p : Port (center.1 ++ Γ) t) (j : Elem t center.1) (e : p ≡ j.left) :
      All.lookup (outs.append env) p ≡ History.output A center j :=
    (Identity.cong (fun q => All.lookup (outs.append env) q) e).trans
      ((All.lookupLeft outs env j).trans
        (All.lookupTabulate (fun _ q => History.output A center q) j))
  let oldAt {t : Ty} (p : Port (center.1 ++ Γ) t) (j : Port Γ t) (e : p ≡ j.right center.1) :
      All.lookup (outs.append env) p ≡ env.lookup j :=
    (Identity.cong (fun q => All.lookup (outs.append env) q) e).trans
      (All.lookupRight outs env j)
  let known : (t : Ty) → (p : Port (center.1 ++ Γ) t) → (x : S.Occurrence Γ₀) →
      History.source (All.lookup (outs.append env) p) ≡ some x →
      Elem x ((⟨f, A⟩ : S.Occurrence Γ₀) :: prior) :=
    fun t p x src =>
      match Elem.split center.1 p with
      | .inl found =>
          Identity.transport (fun y => Elem y ((⟨f, A⟩ : S.Occurrence Γ₀) :: prior))
            (Identity.someInject
              ((Identity.cong History.source (newAt p found.1 found.2)).symm.trans src))
            .here
      | .inr found =>
          .there (m.known t found.1 x
            ((Identity.cong History.source (oldAt p found.1 found.2)).symm.trans src))
  let apart : (t : Ty) → (p q : Port (center.1 ++ Γ) t) →
      All.lookup (outs.append env) p ≡ All.lookup (outs.append env) q → p ≡ q :=
    fun t p q same =>
      match Elem.split center.1 p, Elem.split center.1 q with
      | .inl a, .inl b =>
          a.2.trans
            ((Identity.cong (fun (i : Elem t center.1) => (i.left : Elem t (center.1 ++ Γ)))
                (Elem.sameNumber a.1 b.1
                  (Identity.cong History.number
                    ((newAt p a.1 a.2).symm.trans (same.trans (newAt q b.1 b.2)))))).trans
              b.2.symm)
      | .inl a, .inr b =>
          (fresh (m.known t b.1 ⟨f, A⟩
            (Identity.cong History.source
              ((oldAt q b.1 b.2).symm.trans (same.symm.trans (newAt p a.1 a.2)))))).elim
      | .inr a, .inl b =>
          (fresh (m.known t a.1 ⟨f, A⟩
            (Identity.cong History.source
              ((oldAt p a.1 a.2).symm.trans (same.trans (newAt q b.1 b.2)))))).elim
      | .inr a, .inr b =>
          a.2.trans
            ((Identity.cong (Elem.right center.1)
                (m.apart t a.1 b.1
                  ((oldAt p a.1 a.2).symm.trans (same.trans (oldAt q b.1 b.2))))).trans
              b.2.symm)
  let weak (x : S.Occurrence Γ₀) (e : Available S Γ)
      (same : S.pureAt env ⟨e.op, e.args⟩ ≡ x) :
      S.pureAt (outs.append env) ⟨e.op, e.args.weaken center.1⟩ ≡ x :=
    (Identity.cong (fun a => (⟨e.op, Call.mk a none⟩ : S.Occurrence Γ₀))
      (PortMap.selectWeaken outs env e.args)).trans same
  Sum.casesOn
    (motive := fun kind =>
      Merged
        (Sum.casesOn (motive := fun _ => List (Available S (center.1 ++ Γ))) kind
          (fun pure =>
            Available.ofStep f pure args center only :: table.map (Available.weaken center.1))
          (fun _ => table.map (Available.weaken center.1)))
        (outs.append env) (A.next last) ((⟨f, A⟩ : S.Occurrence Γ₀) :: prior))
    (Kind.cases (S.kind f))
    (fun pure =>
      { known := known
        apart := apart
        listed := fun x i px =>
          match Elem.uncons i with
          | .inl isNew =>
              ⟨Available.ofStep f pure args center only, .here,
                (Identity.cong (fun a => (⟨f, Call.mk a none⟩ : S.Occurrence Γ₀))
                    (PortMap.selectWeaken outs env args)).trans
                  ((Identity.cong
                      (fun k =>
                        (⟨f, Call.mk (env.select args) (Kind.before k last)⟩ :
                          S.Occurrence Γ₀))
                      pure).symm.trans isNew.symm)⟩
          | .inr j =>
              let e := m.listed x j px
              ⟨e.1.weaken center.1, .there (Elem.map (Available.weaken center.1) e.2.1),
                weak x e.1 e.2.2⟩
        ranked := fun x i ex =>
          match Elem.uncons i with
          | .inl isNew =>
              (Kind.pureNotEffectful
                (pure.symm.trans
                  ((Identity.cong (fun (y : S.Occurrence Γ₀) => S.kind y.1) isNew).symm.trans
                    ex))).elim
          | .inr j =>
              Identity.transport
                (fun k => Call.rank x.2 < Effect.rank (Kind.last k last (.after A))) pure.symm
                (m.ranked x j ex) })
    (fun effectful =>
      { known := known
        apart := apart
        listed := fun x i px =>
          match Elem.uncons i with
          | .inl isNew =>
              (Kind.pureNotEffectful
                (px.symm.trans
                  ((Identity.cong (fun (y : S.Occurrence Γ₀) => S.kind y.1) isNew).trans
                    effectful))).elim
          | .inr j =>
              let e := m.listed x j px
              ⟨e.1.weaken center.1, Elem.map (Available.weaken center.1) e.2.1,
                weak x e.1 e.2.2⟩
        ranked := fun x i ex =>
          match Elem.uncons i with
          | .inl isNew =>
              Identity.transport
                (fun (y : S.Occurrence Γ₀) => Call.rank y.2 < Effect.rank (A.next last))
                isNew.symm
                (Identity.transport
                  (fun k =>
                    Call.rank (Call.mk (env.select args) (Kind.before k last) : Call S Γ₀ f) <
                      Effect.rank
                        (Kind.last k last
                          (.after (Call.mk (env.select args) (Kind.before k last)))))
                  effectful.symm (Nat.lt_succ_self _))
          | .inr j =>
              Identity.transport
                (fun k =>
                  Call.rank x.2 <
                    Effect.rank
                      (Kind.last k last
                        (.after (Call.mk (env.select args) (Kind.before k last) :
                          Call S Γ₀ f))))
                effectful.symm (Nat.lt_succ_of_lt (m.ranked x j ex)) })

end

/-- The merged diagram is a diagram of the fragment. -/
def Diagram.mergeWithStraight [DecEq S.Op] : {Γ Δ : List Ty} → {Qs : Exits Ty} →
    (table : List (Available S Γ)) → (ρ : PortMap Γ Δ) → (d : Diagram S Δ Qs) →
    (h : d.Straight) → (Diagram.mergeWith table ρ d h).Straight
  | _, _, _, _, _, .exit _, _ => ()
  | Γ, _, Qs, table, ρ, .step call rest, h =>
      Option.casesOn
        (motive := fun o =>
          (Option.casesOn (motive := fun _ => Diagram S Γ Qs) o
            (Diagram.under call.1 (ρ.select call.2) h.1 h.2.1
              (Diagram.mergeWith (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
                (ρ.lift h.1.1) (rest h.1) h.2.2))
            (fun found =>
              Diagram.mergeWith table (found.outs.append ρ) (rest found.center)
                (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center)
                  h.2.2))).Straight)
        (Available.find call.1 (ρ.select call.2) table)
        (Sigma.mk h.1
          (Prod.mk h.2.1
            (Identity.ind (a := h.1)
              (fun (c : (S.output call.1).Case) (p : h.1 ≡ c) =>
                (Identity.transport
                  (fun (c : (S.output call.1).Case) => Diagram S (c.1 ++ Γ) Qs) p
                  (Diagram.mergeWith
                    (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
                    (ρ.lift h.1.1) (rest h.1) h.2.2)).Straight)
              (Diagram.mergeWithStraight
                (Available.after table call.1 (ρ.select call.2) h.1 h.2.1) (ρ.lift h.1.1)
                (rest h.1) h.2.2)
              (h.2.1 h.1))))
        (fun found =>
          Diagram.mergeWithStraight table (found.outs.append ρ) (rest found.center)
            (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center) h.2.2))
  | _, _, _, _, _, .seq _ _, h => nomatch h

/-- The occurrences of the merged diagram have no element at two positions, and no occurrence
is a call of a step before, for each state of the merge. -/
def Diagram.mergeWithSeparate [DecEq S.Op] : {Γ Δ : List Ty} → {Qs : Exits Ty} →
    (table : List (Available S Γ)) → (ρ : PortMap Γ Δ) → (d : Diagram S Δ Qs) →
    (h : d.Straight) → (env : All (History S Γ₀) Γ) → (last : Option (Effect S Γ₀)) →
    (prior : List (S.Occurrence Γ₀)) → Merged table env last prior →
    (hM : (Diagram.mergeWith table ρ d h).Straight) →
    Separate ((Diagram.mergeWith table ρ d h).occurrences hM env last) prior
  | _, _, _, _, _, .exit _, _, _, _, _, _, _ => (fun _ i _ => i.ofNil, fun _ i _ => i.ofNil)
  | Γ, _, Qs, table, ρ, .step call rest, h, env, last, prior, m, hM =>
      Option.casesOn
        (motive := fun o => (Available.find call.1 (ρ.select call.2) table ≡ o) →
          (hM : (Option.casesOn (motive := fun _ => Diagram S Γ Qs) o
            (Diagram.under call.1 (ρ.select call.2) h.1 h.2.1
              (Diagram.mergeWith (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
                (ρ.lift h.1.1) (rest h.1) h.2.2))
            (fun found =>
              Diagram.mergeWith table (found.outs.append ρ) (rest found.center)
                (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center)
                  h.2.2))).Straight) →
          Separate
            ((Option.casesOn (motive := fun _ => Diagram S Γ Qs) o
              (Diagram.under call.1 (ρ.select call.2) h.1 h.2.1
                (Diagram.mergeWith (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
                  (ρ.lift h.1.1) (rest h.1) h.2.2))
              (fun found =>
                Diagram.mergeWith table (found.outs.append ρ) (rest found.center)
                  (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center)
                    h.2.2))).occurrences hM env last)
            prior)
        (Available.find call.1 (ρ.select call.2) table)
        (fun missing hM =>
          let A : Call S Γ₀ call.1 := Call.at call.1 (ρ.select call.2) env last
          let fresh := m.fresh call.1 (ρ.select call.2) missing
          let inner :=
            Identity.ind (a := h.1)
              (fun (c : (S.output call.1).Case) (p : h.1 ≡ c) =>
                (s : (Identity.transport
                  (fun (c : (S.output call.1).Case) => Diagram S (c.1 ++ Γ) Qs) p
                  (Diagram.mergeWith
                    (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
                    (ρ.lift h.1.1) (rest h.1) h.2.2)).Straight) →
                Separate
                  ((Identity.transport
                    (fun (c : (S.output call.1).Case) => Diagram S (c.1 ++ Γ) Qs) p
                    (Diagram.mergeWith
                      (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
                      (ρ.lift h.1.1) (rest h.1) h.2.2)).occurrences s (A.outputs c env)
                    (A.next last))
                  ((⟨call.1, A⟩ : S.Occurrence Γ₀) :: prior))
              (fun s =>
                Diagram.mergeWithSeparate
                  (Available.after table call.1 (ρ.select call.2) h.1 h.2.1) (ρ.lift h.1.1)
                  (rest h.1) h.2.2 (A.outputs h.1 env) (A.next last)
                  ((⟨call.1, A⟩ : S.Occurrence Γ₀) :: prior)
                  (m.after call.1 (ρ.select call.2) h.1 h.2.1 fresh) s)
              (h.2.1 hM.1) hM.2.2
          (Elem.Distinct.cons inner.1 (fun i => inner.2 _ i .here), fun x i j =>
            match Elem.uncons i with
            | .inl isNew => fresh (Identity.transport (fun y => Elem y prior) isNew j)
            | .inr i' => inner.2 x i' (.there j)))
        (fun found _ hM =>
          Diagram.mergeWithSeparate table (found.outs.append ρ) (rest found.center)
            (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center) h.2.2)
            env last prior m hM)
        .refl hM
  | _, _, _, _, _, .seq _ _, h, _, _, _, _, _ => nomatch h

/-- The merged diagram of a diagram of the fragment is a diagram of the fragment. -/
def Diagram.mergeStraight [DecEq S.Op] {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs)
    (h : d.Straight) : (d.merge h).Straight :=
  Diagram.mergeWithStraight [] (PortMap.id Γ) d h

/-- The dependency graph of the merged diagram has no element at two positions. -/
def Diagram.mergeDistinct [DecEq S.Op] {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs)
    (h : d.Straight) (hM : (d.merge h).Straight) : Elem.Distinct ((d.merge h).graph hM) :=
  (Diagram.mergeWithSeparate [] (PortMap.id Γ) d h (S.inputs Γ) none [] (Merged.start Γ) hM).1

/-- A link of two lists for a third list: each element of the first list is an element of the
second list or of the third list, and each element of the second list is an element of the
first list. -/
abbrev Link {α : Type} (source merged prior : List α) : Type :=
  ((x : α) → Elem x source → Elem x merged ⊕ Elem x prior) ×
    ((x : α) → Elem x merged → Elem x source)

/-- The link of two lists with one more first element each, when the two elements are one
element. -/
def Link.cons {α : Type} {source merged prior : List α} {y y' : α} (same : y ≡ y')
    (rest : Link source merged (y' :: prior)) : Link (y :: source) (y' :: merged) prior :=
  (fun x i =>
    match Elem.uncons i with
    | .inl e =>
        .inl (Identity.transport (fun z => Elem z (y' :: merged)) (e.trans same).symm .here)
    | .inr j =>
        match rest.1 x j with
        | .inl m => .inl (.there m)
        | .inr k =>
            match Elem.uncons k with
            | .inl e => .inl (Identity.transport (fun z => Elem z (y' :: merged)) e.symm .here)
            | .inr k' => .inr k',
    fun x i =>
      match Elem.uncons i with
      | .inl e =>
          Identity.transport (fun z => Elem z (y :: source)) (e.trans same.symm).symm .here
      | .inr j => .there (rest.2 x j))

/-- The link of a list with one more first element, when that element is an element of the
third list. -/
def Link.skip {α : Type} {source merged prior : List α} {y : α} (known : Elem y prior)
    (rest : Link source merged prior) : Link (y :: source) merged prior :=
  (fun x i =>
    match Elem.uncons i with
    | .inl e => .inr (Identity.transport (fun z => Elem z prior) e.symm known)
    | .inr j => rest.1 x j,
    fun x i => .there (rest.2 x i))

section

variable {Γ : List Ty}

/-- The output ports of the data of a call have the histories of the output ports of the call
of the pure operation at the ports. -/
abbrev Used.Sound (env : All (History S Γ₀) Γ) (k : Used S Γ) : Type :=
  (t : Ty) → (q : Port k.2.2.1.1 t) →
    env.lookup (All.lookup (P := Port Γ) k.2.2.2 q) ≡
      History.output (Call.mk (env.select k.2.1) none : Call S Γ₀ k.1) k.2.2.1 q

/-- An available call with its link: its call is a call of a step before, and its output ports
have the histories of the output ports of that call. -/
abbrev Available.Linked (env : All (History S Γ₀) Γ) (prior : List (S.Occurrence Γ₀))
    (e : Available S Γ) : Type :=
  Elem (S.pureAt env ⟨e.op, e.args⟩) prior × Used.Sound env e.used

/-- An available call keeps its link in a context with more ports and with one more call. -/
def Available.Linked.weaken {env : All (History S Γ₀) Γ} {prior : List (S.Occurrence Γ₀)}
    {e : Available S Γ} (l : e.Linked env prior) {Ξ : List Ty} (outs : All (History S Γ₀) Ξ)
    (x : S.Occurrence Γ₀) : (e.weaken Ξ).Linked (outs.append env) (x :: prior) :=
  (.there
      (Identity.transport (fun y => Elem y prior)
        (Identity.cong (fun a => (⟨e.op, Call.mk a none⟩ : S.Occurrence Γ₀))
          (PortMap.selectWeaken outs env e.args)).symm
        l.1),
    fun t q =>
      (Identity.cong (fun p => All.lookup (outs.append env) p)
          (All.lookupMap (fun (t : Ty) (i : Port Γ t) => (i.right Ξ : Port (Ξ ++ Γ) t)) e.outs
            q)).trans
        ((All.lookupRight outs env (All.lookup (P := Port Γ) e.outs q)).trans
          ((l.2 t q).trans
            (Identity.cong
              (fun a => History.output (Call.mk a none : Call S Γ₀ e.op) e.center q)
              (PortMap.selectWeaken outs env e.args).symm))))

/-- The call of a step with a pure operation has its link after the step. -/
def Available.Linked.ofStep (f : S.Op) (pure : S.kind f ≡ .pure) (args : PortMap Γ (S.input f))
    (center : (S.output f).Case) (only : (c : (S.output f).Case) → center ≡ c)
    (env : All (History S Γ₀) Γ) (last : Option (Effect S Γ₀))
    (prior : List (S.Occurrence Γ₀)) :
    (Available.ofStep f pure args center only).Linked
      ((Call.at f args env last).outputs center env)
      (⟨f, Call.at f args env last⟩ :: prior) :=
  let A : Call S Γ₀ f := Call.at f args env last
  let outs : All (History S Γ₀) center.1 :=
    All.tabulate center.1 fun _ q => History.output A center q
  let pureEq :
      (Call.mk (All.select (outs.append env) (args.weaken center.1)) none : Call S Γ₀ f) ≡ A :=
    (Identity.cong (fun a => (Call.mk a none : Call S Γ₀ f))
        (PortMap.selectWeaken outs env args)).trans
      (Identity.cong (fun k => (Call.mk (env.select args) (Kind.before k last) : Call S Γ₀ f))
        pure).symm
  (Identity.transport (fun y => Elem y ((⟨f, A⟩ : S.Occurrence Γ₀) :: prior))
      (Identity.cong (fun a => (⟨f, a⟩ : S.Occurrence Γ₀)) pureEq).symm .here,
    fun _ q =>
      (Identity.cong (fun p => All.lookup (outs.append env) p)
          (All.lookupTabulate (fun (t : Ty) (i : Elem t center.1) =>
            (i.left : Port (center.1 ++ Γ) t)) q)).trans
        ((All.lookupLeft outs env q).trans
          ((All.lookupTabulate (fun _ q => History.output A center q) q).trans
            (Identity.cong (fun a => History.output a center q) pureEq.symm))))

/-- Each available call after a step has its link. -/
def Available.Linked.after {env : All (History S Γ₀) Γ} {prior : List (S.Occurrence Γ₀)}
    (table : List (Available S Γ)) (linked : All (fun e => e.Linked env prior) table)
    (f : S.Op) (args : PortMap Γ (S.input f)) (center : (S.output f).Case)
    (only : (c : (S.output f).Case) → center ≡ c) (last : Option (Effect S Γ₀)) :
    All
      (fun e =>
        e.Linked ((Call.at f args env last).outputs center env)
          (⟨f, Call.at f args env last⟩ :: prior))
      (Available.after table f args center only) :=
  Sum.casesOn
    (motive := fun kind =>
      All
        (fun e =>
          e.Linked ((Call.at f args env last).outputs center env)
            (⟨f, Call.at f args env last⟩ :: prior))
        (Sum.casesOn (motive := fun _ => List (Available S (center.1 ++ Γ))) kind
          (fun pure =>
            Available.ofStep f pure args center only :: table.map (Available.weaken center.1))
          (fun _ => table.map (Available.weaken center.1))))
    (Kind.cases (S.kind f))
    (fun pure =>
      .cons (Available.Linked.ofStep f pure args center only env last prior)
        (All.image (Available.weaken center.1) (fun _ l => l.weaken _ _) linked))
    (fun _ => All.image (Available.weaken center.1) (fun _ l => l.weaken _ _) linked)

end

/-- The link of the occurrences of a diagram of the fragment and of its merged diagram, for the
calls of the steps before. Each occurrence of the diagram is an occurrence of the merged
diagram or one of those calls, and each occurrence of the merged diagram is an occurrence of
the diagram. -/
def Diagram.mergeWithLink [DecEq S.Op] : {Γ Δ : List Ty} → {Qs : Exits Ty} →
    (table : List (Available S Γ)) → (ρ : PortMap Γ Δ) → (d : Diagram S Δ Qs) →
    (h : d.Straight) → (env : All (History S Γ₀) Γ) → (last : Option (Effect S Γ₀)) →
    (prior : List (S.Occurrence Γ₀)) → All (fun e => e.Linked env prior) table →
    (hM : (Diagram.mergeWith table ρ d h).Straight) →
    Link (d.occurrences h (env.select ρ) last)
      ((Diagram.mergeWith table ρ d h).occurrences hM env last) prior
  | _, _, _, _, _, .exit _, _, _, _, _, _, _ => (fun _ i => i.ofNil, fun _ i => i.ofNil)
  | Γ, _, Qs, table, ρ, .step call rest, h, env, last, prior, linked, hM =>
      let Ad : Call S Γ₀ call.1 := Call.at call.1 call.2 (env.select ρ) last
      let A' : Call S Γ₀ call.1 := Call.at call.1 (ρ.select call.2) env last
      let sameCall : A' ≡ Ad :=
        Identity.cong
          (fun a => (Call.mk a (Kind.before (S.kind call.1) last) : Call S Γ₀ call.1))
          (All.selectSelect env ρ call.2)
      Option.casesOn
        (motive := fun o =>
          (hM : (Option.casesOn (motive := fun _ => Diagram S Γ Qs) o
            (Diagram.under call.1 (ρ.select call.2) h.1 h.2.1
              (Diagram.mergeWith (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
                (ρ.lift h.1.1) (rest h.1) h.2.2))
            (fun found =>
              Diagram.mergeWith table (found.outs.append ρ) (rest found.center)
                (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center)
                  h.2.2))).Straight) →
          Link
            ((⟨call.1, Ad⟩ : S.Occurrence Γ₀) ::
              (rest h.1).occurrences h.2.2 (Ad.outputs h.1 (env.select ρ)) (Ad.next last))
            ((Option.casesOn (motive := fun _ => Diagram S Γ Qs) o
              (Diagram.under call.1 (ρ.select call.2) h.1 h.2.1
                (Diagram.mergeWith (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
                  (ρ.lift h.1.1) (rest h.1) h.2.2))
              (fun found =>
                Diagram.mergeWith table (found.outs.append ρ) (rest found.center)
                  (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center)
                    h.2.2))).occurrences hM env last)
            prior)
        (Available.find call.1 (ρ.select call.2) table)
        (fun hM =>
          let sourceSame :
              (rest h.1).occurrences h.2.2 ((A'.outputs h.1 env).select (ρ.lift h.1.1))
                  (A'.next last) ≡
                (rest h.1).occurrences h.2.2 (Ad.outputs h.1 (env.select ρ)) (Ad.next last) :=
            (Identity.cong (fun vals => (rest h.1).occurrences h.2.2 vals (A'.next last))
                (PortMap.selectLift (All.tabulate h.1.1 fun _ q => History.output A' h.1 q) env
                  ρ)).trans
              (Identity.cong
                (fun (a : Call S Γ₀ call.1) =>
                  (rest h.1).occurrences h.2.2 (a.outputs h.1 (env.select ρ)) (a.next last))
                sameCall)
          Link.cons
            (Identity.cong (fun a => (⟨call.1, a⟩ : S.Occurrence Γ₀)) sameCall.symm)
            (Identity.ind (a := h.1)
              (fun (c : (S.output call.1).Case) (p : h.1 ≡ c) =>
                (s : (Identity.transport
                  (fun (c : (S.output call.1).Case) => Diagram S (c.1 ++ Γ) Qs) p
                  (Diagram.mergeWith
                    (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
                    (ρ.lift h.1.1) (rest h.1) h.2.2)).Straight) →
                Link
                  ((rest h.1).occurrences h.2.2 (Ad.outputs h.1 (env.select ρ)) (Ad.next last))
                  ((Identity.transport
                    (fun (c : (S.output call.1).Case) => Diagram S (c.1 ++ Γ) Qs) p
                    (Diagram.mergeWith
                      (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
                      (ρ.lift h.1.1) (rest h.1) h.2.2)).occurrences s (A'.outputs c env)
                    (A'.next last))
                  ((⟨call.1, A'⟩ : S.Occurrence Γ₀) :: prior))
              (fun s =>
                Identity.transport
                  (fun (L : List (S.Occurrence Γ₀)) =>
                    Link L
                      ((Diagram.mergeWith
                        (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
                        (ρ.lift h.1.1) (rest h.1) h.2.2).occurrences s (A'.outputs h.1 env)
                        (A'.next last))
                      ((⟨call.1, A'⟩ : S.Occurrence Γ₀) :: prior))
                  sourceSame
                  (Diagram.mergeWithLink
                    (Available.after table call.1 (ρ.select call.2) h.1 h.2.1) (ρ.lift h.1.1)
                    (rest h.1) h.2.2 (A'.outputs h.1 env) (A'.next last)
                    ((⟨call.1, A'⟩ : S.Occurrence Γ₀) :: prior)
                    (Available.Linked.after table linked call.1 (ρ.select call.2) h.1 h.2.1 last)
                    s))
              (h.2.1 hM.1) hM.2.2))
        (fun found hM =>
          let l := All.lookup linked found.mem
          let pure : S.kind call.1 ≡ .pure :=
            Identity.transport (fun (k : Used S Γ) => S.kind k.1 ≡ .pure) found.same
              found.entry.pure
          let pureCall :
              (Call.mk (env.select (ρ.select call.2)) none : Call S Γ₀ call.1) ≡ Ad :=
            (Identity.cong
                (fun k =>
                  (Call.mk (env.select (ρ.select call.2)) (Kind.before k last) :
                    Call S Γ₀ call.1))
                pure).symm.trans sameCall
          let known : Elem (⟨call.1, Ad⟩ : S.Occurrence Γ₀) prior :=
            Identity.transport (fun (a : Call S Γ₀ call.1) => Elem (⟨call.1, a⟩ : S.Occurrence Γ₀) prior)
              pureCall
              (Identity.transport
                (fun (k : Used S Γ) => Elem (S.pureAt env ⟨k.1, k.2.1⟩) prior) found.same l.1)
          let sound : Used.Sound env ⟨call.1, ρ.select call.2, found.center, found.outs⟩ :=
            Identity.transport (Used.Sound env) found.same l.2
          let outsSame :
              Ad.outputs found.center (env.select ρ) ≡ env.select (found.outs.append ρ) :=
            (Identity.cong (fun o => All.append o (env.select ρ))
                (All.selectValues env found.outs
                  (fun _ q => History.output Ad found.center q)
                  (fun t q =>
                    (sound t q).trans
                      (Identity.cong (fun a => History.output a found.center q)
                        pureCall))).symm).trans
              (All.selectAppend env found.outs ρ).symm
          let lastSame : Ad.next last ≡ last :=
            Identity.cong (fun k => Kind.last k last (.after Ad)) pure
          let sourceSame :
              (rest h.1).occurrences h.2.2 (Ad.outputs h.1 (env.select ρ)) (Ad.next last) ≡
                (rest found.center).occurrences
                  (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center) h.2.2)
                  (env.select (found.outs.append ρ)) last :=
            (Diagram.occurrencesCase rest (h.2.1 found.center) h.2.2 Ad (env.select ρ)
                (Ad.next last)).trans
              (Identity.cong₂
                (fun vals l =>
                  (rest found.center).occurrences
                    (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center)
                      h.2.2)
                    vals l)
                outsSame lastSame)
          Link.skip known
            (Identity.transport
              (fun (L : List (S.Occurrence Γ₀)) =>
                Link L
                  ((Diagram.mergeWith table (found.outs.append ρ) (rest found.center)
                    (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center)
                      h.2.2)).occurrences hM env last)
                  prior)
              sourceSame.symm
              (Diagram.mergeWithLink table (found.outs.append ρ) (rest found.center)
                (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center) h.2.2)
                env last prior linked hM)))
        hM
  | _, _, _, _, _, .seq _ _, h, _, _, _, _, _ => nomatch h

/-- A position of an occurrence in the graph of a diagram of the fragment gives a position of
that occurrence in the graph of its merged diagram, and a position in the graph of the merged
diagram gives a position in the graph of the diagram. -/
def Diagram.mergeLink [DecEq S.Op] {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs)
    (h : d.Straight) (hM : (d.merge h).Straight) :
    ((x : S.Occurrence Γ) → Elem x (d.graph h) → Elem x ((d.merge h).graph hM)) ×
      ((x : S.Occurrence Γ) → Elem x ((d.merge h).graph hM) → Elem x (d.graph h)) :=
  let link :=
    Identity.transport
      (fun vals => Link (d.occurrences h vals none) ((d.merge h).graph hM) [])
      (PortMap.selectId (S.inputs Γ))
      (Diagram.mergeWithLink [] (PortMap.id Γ) d h (S.inputs Γ) none [] .nil hM)
  (fun x i =>
    match link.1 x i with
    | .inl m => m
    | .inr k => k.ofNil,
    link.2)

end Merged

end Draft
