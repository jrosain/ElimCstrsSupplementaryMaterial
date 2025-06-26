Require Import SupplementaryMaterial.Prelude.
Require Import SupplementaryMaterial.Impredicativity.

Set Universe Polymorphism.

Module SPropProofIrrelevance.
  Import SPropImpredicativity.

  Lemma box_inj@{s|u|SProp ~> s} :
    forall (A : Type@{s|u}) (x y : A),
      eq@{SProp s|u} (box@{s|u} x) (box@{s|u} y) -> eq@{s s|u} x y.
  Proof.
    intros.
    refine (eq_f@{SProp s s|u u} (fun X => match X with box a => a end) X).
  Qed.

  Lemma irrelevance@{s|u|SProp ~> s} :
    forall (A : Type@{s|u}) (x y : A), eq@{s s|u} x y.
  Proof.
    intros ???.
    assert (H : eq@{SProp s|u} (box@{s|u} x) (box@{s|u} y)) by reflexivity.
    now apply box_inj@{s|u} in H.
  Qed.
End SPropProofIrrelevance.
