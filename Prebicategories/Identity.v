(*
 - Identity pseudofunctor
From 'UniMath/Bicategories/PseudoFunctors/Examples/Identity.v'
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.

Require Import Integers.Prebicategories.Invertible_2cells.
Require Import Integers.Prebicategories.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope cat.
(*Local Open Scope mor_disp_scope.*)
Local Open Scope bicategory_scope.

Section IdentityPseudofunctor.
  Variable (C : prebicat).

  Definition id_pseudofunctor_data : pseudofunctor_data C C.
  Proof.
    use make_pseudofunctor_data.
    - exact (λ a, a).
    - exact (λ a b f, f).
    - exact (λ a b f g θ, θ).
    - exact (λ a, id2 (identity a)).
    - exact (λ a b c f g, id2 (f · g)).
  Defined.

  Definition id_pseudofunctor_laws : pseudofunctor_laws id_pseudofunctor_data.
  Proof.
    repeat split.
    - intros a b c f g h θ. 
      exact (id2_left _ @ !id2_right _).
    - intros a b c f g h θ.
      exact (id2_left _ @ !id2_right _).
    - intros a b f. cbn.
      rewrite id2_rwhisker.
      rewrite !id2_left.
      reflexivity.
    - intros a b f ; cbn in *.
      rewrite lwhisker_id2.
      rewrite !id2_left.
      reflexivity.
    - intros a b c d f g h ; cbn in *.
      rewrite lwhisker_id2, id2_rwhisker.
      rewrite !id2_left, !id2_right.
      reflexivity.
  Qed.

  Definition id_pseudofunctor : pseudofunctor C C.
  Proof.
    use make_pseudofunctor.
    - exact id_pseudofunctor_data.
    - exact id_pseudofunctor_laws.
    - split ; cbn ; intros ; is_iso.
  Defined.
End IdentityPseudofunctor.
