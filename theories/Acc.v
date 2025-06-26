(** * Acc: general recursion using negative type *)

From Stdlib Require Import FunInd.
From Stdlib Require Import Arith.Compare.
From Stdlib Require Import Lia.

(** ** Well-foundedness

    Well-foundedness can be expressed using an [Acc]essibility predicate.
    This predicate turns a relation into a directed graph, and says that an element
    is accessible whenever all its predecessors are accessible.

    If this graph has no infinite branch, then it means that the relation is well-founded:
    every element can be accessed. *)
Inductive Acc {A : Type} (R : A -> A -> Prop) (x : A) : Prop :=
  { Acc_inv : forall (y : A), R y x -> Acc R y }.
Arguments Acc_inv {_} {_} {_} _ {_} _.

Definition wf {A : Type} (R : A -> A -> Prop) : Prop :=
  forall (x : A), Acc R x.

(** We will use the order [lt]. Let us show that it is well-founded. *)
Lemma wf_lt : wf lt.
Proof.
  intro n. induction n.
  - easy.
  - refine ({| Acc_inv := _ |}).
    intros. destruct (le_dec y n).
    * inversion l. assumption.
      assert (Hy : y < n).
      { rewrite <-H1. now apply le_n_S. }
      clear H l H0 H1. eapply Acc_inv in IHn; eauto.
    * assert (e : y = n) by lia.
      now rewrite e.
Qed.

Fixpoint div2 (n : nat) : nat :=
  match n with
  | O => O
  | 1 => O
  | S (S n) => S (div2 n)
  end.

Functional Scheme div2_ind := Induction for div2 Sort Prop.

Lemma eq_dec_nat : forall (n m : nat), { n = m } + { n <> m }.
Proof.
  intro n. induction n as [|n IHn].
  - destruct m. now left. now right.
  - destruct m. now right.
    destruct (IHn m).
    * left; now f_equal.
    * right; intro e; now injection e.
Qed.

(** The order [lt] is well-founded, and we can use [div2] with it. *)
Lemma div2_lt (n : nat) : n <> 0 -> div2 n < n.
Proof.
  intro hne. functional induction (div2 n) using div2_ind.
  - exfalso; now apply hne.
  - apply le_n.
  - destruct (eq_dec_nat n1 0).
    * rewrite e. cbn. apply le_n.
    * apply IHn0 in n. apply le_n_S, le_S, n.
Qed.

(** This definition is not accepted *)
Fail Fixpoint log2 (n : nat) : nat :=
  match n with
  | O => O
  | S _ => S (log2 (div2 n))
  end.

(** Hence, we can use the generic recursion to define it. *)
#[program] Definition log2 (n : nat) : nat :=
  (fix F (n : nat) (a : Acc lt n) {struct a} : nat :=
     match n with
     | O => O
     | S _ => S (F (div2 n) (Acc_inv a _))
     end)
    n (wf_lt n).
Next Obligation.
  apply div2_lt. intro. inversion H.
Defined.
