import Prelude.Container.Verified

/-! Calls that commute in a congruence of computations.

Two calls commute in a congruence when the congruence relates the two orders of the calls, for
each continuation. A call is central when it commutes with each call. A call is copyable when
the congruence relates two calls of it to one call whose response goes to the two places.

A class of calls is a specification: a witness of the precondition is the evidence that a call
is of the class, and each response has the postcondition. The evidence of a computation for
this specification has the evidence of the class at each call of the computation. Two
computations commute when each call of the first commutes with each call of the second. A
computation is copyable when each of its calls is central and copyable.

Two calls commute in the congruence of the source of an implementation when the calls of their
two computations commute. A call is copyable in it when the calls of its computation are
central and copyable. -/

set_option autoImplicit false
set_option genInjectivity false

universe s p s' p' u v v' w z x y

namespace Prelude.Container

/-- The specification of a class of calls. A witness of the precondition is the evidence that
the call is of the class, and each response has the postcondition. -/
def DepPoly.admit {C : Container.{s, p}} (P : C.Shape → Type w) : DepPoly.{s, p, w, 0} C where
  Pre := P
  Post _ _ _ := PUnit

namespace FreeDep

variable {C : Container.{s, p}} {α : Type u} {Q : α → Type v}

/-- A computation that makes no call has evidence for each specification of the calls. -/
def ofNoCall {t : DepPoly.{s, p, x, y} C} {a : Free C α}
    (h : FreeDep (DepPoly.noCall.{s, p, w, z} C) Q a) : FreeDep t Q a :=
  FreeDep.casesOn (motive := fun a _ => FreeDep t Q a) h (fun q => .pure q)
    (fun pre _ => nomatch pre)

/-- Each computation has evidence for the class of all the calls. -/
def ofAll : (a : Free C α) →
    FreeDep (DepPoly.admit fun (_ : C.Shape) => PUnit.{1}) (fun _ => PUnit.{1}) a
  | .pure _ => .pure ⟨⟩
  | .request _ k => .request ⟨⟩ fun i _ => ofAll (k i)

end FreeDep

namespace Free.Congruence

variable {C : Container.{s, p}} {D : Container.{s', p'}} {α : Type u} {β : Type v}
  {γ : Type v'}

variable (eqv : Congruence.{s, p, u, w} C α)

/-- Two calls commute in a congruence: it relates the two orders of the calls, for each
continuation. -/
def Commute (a b : C.Shape) : Type (max s p u w) :=
  (k : C.Pos a → C.Pos b → Free C α) →
    eqv.Rel (.request a fun i => .request b fun j => k i j)
      (.request b fun j => .request a fun i => k i j)

/-- A call is central in a congruence: it commutes with each call. -/
def Central (a : C.Shape) : Type (max s p u w) := (b : C.Shape) → eqv.Commute a b

/-- A call is copyable in a congruence: two calls of it are one call whose response goes to the
two places. -/
def Copyable (a : C.Shape) : Type (max s p u w) :=
  (k : C.Pos a → C.Pos a → Free C α) →
    eqv.Rel (.request a fun i => .request a fun j => k i j) (.request a fun i => k i i)

variable {eqv}

/-- Two calls that commute, in the other order. -/
def Commute.symm {a b : C.Shape} (h : eqv.Commute a b) : eqv.Commute b a :=
  fun k => eqv.symm (h fun i j => k j i)

section Classes

variable {P : C.Shape → Type x} {Q : C.Shape → Type y}
  (commute : (a b : C.Shape) → P a → Q b → eqv.Commute a b)

/-- A call changes order with a computation, when it commutes with each call of the
computation. -/
def Commute.past {a : C.Shape} (pa : P a) {G : γ → Type z} : {c : Free C γ} →
    FreeDep (DepPoly.admit Q) G c → (k : C.Pos a → γ → Free C α) →
    eqv.Rel (.request a fun i => c.bind (k i)) (c.bind fun j => .request a fun i => k i j)
  | .pure j, _, k => eqv.refl (.request a fun i => k i j)
  | .request b f, h, k =>
      eqv.trans (commute a b pa h.parts.1 fun i j => (f j).bind (k i))
        (eqv.request b fun j => Commute.past pa (h.parts.2 j ⟨⟩) k)

/-- Two computations change order, when each call of the first commutes with each call of the
second. -/
def Commute.bind {F : β → Type z} {G : γ → Type z} : {a : Free C β} →
    FreeDep (DepPoly.admit P) F a → {c : Free C γ} → FreeDep (DepPoly.admit Q) G c →
    (k : β → γ → Free C α) →
    eqv.Rel (a.bind fun i => c.bind (k i)) (c.bind fun j => a.bind fun i => k i j)
  | .pure i, _, c, _, k => eqv.refl (c.bind (k i))
  | .request a f, h, _, hc, k =>
      eqv.trans (eqv.request a fun i => Commute.bind (h.parts.2 i ⟨⟩) hc k)
        (Commute.past commute h.parts.1 hc fun i j => (f i).bind fun i' => k i' j)

/-- Two calls commute in the congruence of the source of an implementation, when each call of
the computation of the first commutes with each call of the computation of the second. -/
def Commute.along {eqv : Congruence.{s', p', u, w} D α} {P : D.Shape → Type x}
    {Q : D.Shape → Type y} (commute : (a b : D.Shape) → P a → Q b → eqv.Commute a b)
    {g : Impl C D} {a b : C.Shape} {F : C.Pos a → Type z} {G : C.Pos b → Type z}
    (ha : FreeDep (DepPoly.admit P) F (g a)) (hb : FreeDep (DepPoly.admit Q) G (g b)) :
    (eqv.along g).Commute a b :=
  fun k => Commute.bind commute ha hb fun i j => (k i j).subst g

end Classes

section Values

variable {P : C.Shape → Type x}
  (value : (a : C.Shape) → P a → eqv.Central a × eqv.Copyable a)

/-- A computation is copyable when each of its calls is central and copyable: two runs of it
are one run whose value goes to the two places. -/
def Copyable.bind {F : β → Type z} : {a : Free C β} → FreeDep (DepPoly.admit P) F a →
    (k : β → β → Free C α) →
    eqv.Rel (a.bind fun i => a.bind fun j => k i j) (a.bind fun i => k i i)
  | .pure i, _, k => eqv.refl (k i i)
  | .request a f, h, k =>
      eqv.trans
        (eqv.request a fun i =>
          eqv.symm
            (Commute.past (P := P) (Q := P) (fun a b pa _ => (value a pa).1 b) h.parts.1
              (h.parts.2 i ⟨⟩) fun i' j => (f i').bind (k j)))
        (eqv.trans
          ((value a h.parts.1).2 fun i i' => (f i).bind fun j => (f i').bind (k j))
          (eqv.request a fun i => Copyable.bind (h.parts.2 i ⟨⟩) k))

/-- A call is copyable in the congruence of the source of an implementation, when each call of
its computation is central and copyable. -/
def Copyable.along {eqv : Congruence.{s', p', u, w} D α} {P : D.Shape → Type x}
    (value : (a : D.Shape) → P a → eqv.Central a × eqv.Copyable a) {g : Impl C D} {a : C.Shape}
    {F : C.Pos a → Type z} (ha : FreeDep (DepPoly.admit P) F (g a)) : (eqv.along g).Copyable a :=
  fun k => Copyable.bind value ha fun i j => (k i j).subst g

end Values

end Free.Congruence

end Prelude.Container
