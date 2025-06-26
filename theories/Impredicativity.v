Require Import SupplementaryMaterial.Prelude.

Set Universe Polymorphism.

(** * Impredicativity: showing impredicativity from elimination constraints. *)

(** In this section, we assume a sort [s] such that [Prop ~> s] in every definition.
    We show that [s] is also impredicative, i.e., that it can be resized and that
    the resizing operation is an equivalence. *)
Module PropImpredicativity.
  Inductive Box@{s|u|} (A : Type@{s|u}) : Prop := box : A -> Box A.
  Inductive Unbox@{s|u|} (A : Prop) : Type@{s|u} := unbox : A -> Unbox A.

  Arguments box {_} _.
  Arguments unbox {_} _.

  Notation "[ x ]" := (unbox (box x)).

  Definition resize@{s|u v|} (A : Type@{s|u}) : Type@{s|v} :=
    Unbox@{s|v} (Box@{s|u} A).

  Definition r@{s|u v|} {A : Type@{s|u}} (x : A) : resize@{s|u v} A := [ x ].

  Definition s@{s|u v|Prop ~> s} {A : Type@{s|u}} (x : resize@{s|u v} A) : A :=
    match x with
    | [ x ] => x
    end.

  (** Then, we get the resizing property. *)
  Lemma resize_is_equiv@{s|u v|Prop ~> s} (A : Type@{s|u}) : Equiv@{s|u v} A (resize@{s|u v} A).
  Proof.
    unshelve econstructor.
    - exact r.
    - exact s.
    - intros x. reflexivity.
    - intros y. cbv. now destruct y, b.
  Qed.
End PropImpredicativity.

(** We can do the exact same thing with [SProp]. *)
Module SPropImpredicativity.
  Inductive Box@{s|u|} (A : Type@{s|u}) : SProp := box : A -> Box A.
  Inductive Unbox@{s|u|} (A : SProp) : Type@{s|u} := unbox : A -> Unbox A.

  Arguments box {_} _.
  Arguments unbox {_} _.

  Notation "[ x ]" := (unbox (box x)).

  Definition resize@{s|u v|} (A : Type@{s|u}) : Type@{s|v} :=
    Unbox@{s|v} (Box@{s|u} A).

  Definition r@{s|u v|} {A : Type@{s|u}} (x : A) : resize@{s|u v} A := [ x ].

  Definition s@{s|u v|SProp ~> s} {A : Type@{s|u}} (x : resize@{s|u v} A) : A :=
    match x with
    | [ x ] => x
    end.

  Lemma resize_is_equiv@{s|u v|SProp ~> s} (A : Type@{s|u}) : Equiv@{s|u v} A (resize@{s|u v} A).
  Proof.
    unshelve econstructor.
    - exact r.
    - exact s.
    - intros x. reflexivity.
    - intros y. cbv. now destruct y, b.
  Qed.

  Definition SProd@{sd s|ud u v|ud <= v, u <= v}
    (A : Type@{sd|ud}) (B : A -> Type@{s|u}) : Type@{s|u} :=
    resize@{s|v u} (forall (x : A), B x).

  Lemma SProd_equiv@{sd s|ud u v|ud <= v, u <= v, SProp ~> s}
    (A : Type@{sd|ud}) (B : A -> Type@{s|u}) :
    Equiv@{s|v u} (forall (x : A), B x) (SProd A B).
  Proof.
    unshelve econstructor.
    - intro. now repeat constructor.
    - intro. now destruct X, b.
    - intro f. now cbv.
    - intro f. cbv. now destruct f, b.
  Qed.
End SPropImpredicativity.
