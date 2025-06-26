(** * Prelude: some introductory stuff *)

Set Universe Polymorphism.

Inductive eq@{s s'|u|} {A : Type@{s|u}} (x : A) : A -> Type@{s'|u} :=
  refl : eq x x.

Lemma eq_f@{s s' s''|u v|+} {A : Type@{s|u}} {B : Type@{s'|v}} (f : A -> B) {x y : A} :
  eq@{s s''|u} x y -> eq@{s' s''|v} (f x) (f y).
Proof. intros []. constructor. Defined.

(** Usual notations / definitions on functions. *)
Notation "f ;; g" := (fun x => g (f x)) (at level 40).

Definition id@{s|u|} (A : Type@{s|u}) (x : A) := x.

Record Equiv@{s|u v|} (A : Type@{s|u}) (B : Type@{s|v}) := {
    f : A -> B;
    g : B -> A;
    retr : forall x, eq@{s s|u} ((f ;; g) x) x;
    sec : forall y, eq@{s s|v} ((g ;; f) y) y;
  }.
Arguments retr {_} {_} _.
Arguments sec {_} {_} _.

Notation "A ≃ B" := (Equiv A B) (at level 50).

