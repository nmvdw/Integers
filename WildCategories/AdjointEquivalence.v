(*
 - Definition of adjoint equivalences
 - Projections
 - Proofs of inverse triangles
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.

Require Import Integers.WildCategories.WildCat.
Require Import Integers.WildCategories.DispWildCat.
Require Import Integers.WildCategories.Invertible_2cells.
Require Import Integers.WildCategories.WildFunctor.
Import WildFunctor.Notations.
Require Import Integers.WildCategories.WildNaturalTransformation.
Import WildNaturalTransformation.Notations.
Require Import Integers.WildCategories.WildNaturalIsomorphism.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(** Definition **)
Definition is_adjoint_equivalence
           {C D : wild_cat}
           (L : wild_functor C D)
           (R : wild_functor D C)
  : UU.
Proof.
  use total2.
  - exact (wild_nat_iso (R ✦ L) (id_wild_functor D) × wild_nat_iso (id_wild_functor C) (L ✦ R)).
  - intro units.
    destruct units as [ε η].
    exact ((∏ (a : D), invertible_2cell (η (R a) · #R (ε a)) (id₁ (R a)))
             ×
             ∏ (a : C), invertible_2cell (#L (η a) · ε (L a)) (id₁ (L a))).
Defined.

Definition adjoint_equivalence (C D : wild_cat) : UU
  := ∑ (L : wild_functor C D) (R : wild_functor D C), is_adjoint_equivalence L R.

Definition make_adjoint_equivalence
           {C D : wild_cat}
           (L : wild_functor C D)
           (R : wild_functor D C)
           (ε : wild_nat_iso (R ✦ L) (id_wild_functor D))
           (η : wild_nat_iso (id_wild_functor C) (L ✦ R))
           (tR : ∏ (a : D), invertible_2cell (η (R a) · #R (ε a)) (id₁ (R a)))
           (tL : ∏ (a : C), invertible_2cell (#L (η a) · ε (L a)) (id₁ (L a)))
  : adjoint_equivalence C D
  := L ,, R ,, (ε ,, η) ,, tR ,, tL.

(** Projections **)
Definition adj_left {C D : wild_cat} (A : adjoint_equivalence C D)
  : wild_functor C D
  := pr1 A.

(*Coercion adj_left : adjunction >-> wild_functor.*)

Definition adj_right {C D : wild_cat} (A : adjoint_equivalence C D)
  : wild_functor D C
  := pr12 A.

Definition adj_counit {C D : wild_cat} (A : adjoint_equivalence C D)
  : wild_nat_iso ((adj_right A) ✦ (adj_left A)) (id_wild_functor D)
  := pr1 (pr122 A).

Definition adj_unit {C D : wild_cat} (A : adjoint_equivalence C D)
  : wild_nat_iso (id_wild_functor C) ((adj_left A) ✦ (adj_right A))
  := pr2 (pr122 A).

Definition adj_tR {C D : wild_cat} (A : adjoint_equivalence C D)
  : ∏ (a : D), invertible_2cell
                 ((adj_unit A) (adj_right A a) · #(adj_right A) (adj_counit A a))
                 (id₁ (adj_right A a))
  := pr1 (pr222 A).

Definition adj_tL {C D : wild_cat} (A : adjoint_equivalence C D)
  : ∏ (a : C), invertible_2cell
                 (#(adj_left A) (adj_unit A a) · adj_counit A (adj_left A a))
                 (id₁ (adj_left A a))
  := pr2 (pr222 A).

(** Inverse triangles **)
Lemma adj_tL_inv {C D : wild_cat} (A : adjoint_equivalence C D)
  : ∏ (a : C), invertible_2cell
                 (wild_nat_iso_trans_inv (adj_counit A) (adj_left A a)
                   · #(adj_left A) (wild_nat_iso_trans_inv (adj_unit A) a))
                 (id₁ (adj_left A a)).
Proof.
  intro a.
  use tpair.
  - refine (_ • _ • _ • _ • _ • _ • _ • _ • _).
    + apply linvunitor.
    + apply ((adj_tL A a)^-1 ▹ _).
    + apply rassociator.
    + apply (_ ◃ lassociator _ _ _).
    + apply (_ ◃ (wild_nat_iso_r (adj_counit A) (adj_left A a) ▹ _)).
    + apply (_ ◃ lunitor _).
    + apply (wild_functor_comp (adj_left A)).
    + apply (##(adj_left A) (wild_nat_iso_r (adj_unit A) a)).
    + apply ((wild_functor_id (adj_left A) a)^-1).
  - refine (_ • _ • _ • _ • _ • _ • _ • _ • _).
    + apply ((wild_functor_id (adj_left A) a)).
    + apply (##(adj_left A) ((wild_nat_iso_r (adj_unit A) a)^-1)).
    + apply ((wild_functor_comp (adj_left A) _ _)^-1).
    + apply (_ ◃ linvunitor _).
    + apply (_ ◃ ((wild_nat_iso_r (adj_counit A) (adj_left A a)^-1) ▹ _)).
    + apply (_ ◃ rassociator _ _ _).
    + apply lassociator.
    + apply (adj_tL A a ▹ _).
    + apply lunitor.
Qed.

Lemma adj_tR_inv {C D : wild_cat} (A : adjoint_equivalence C D)
  : ∏ (b : D), invertible_2cell
                 (#(adj_right A) (wild_nat_iso_trans_inv (adj_counit A) b)
                   · wild_nat_iso_trans_inv (adj_unit A) (adj_right A b))
                 (id₁ (adj_right A b)).
Proof.
  intro b.
  use tpair.
  - refine (_ • _ • _ • _ • _ • _ • _ • _ • _).
    + apply linvunitor.
    + apply ((adj_tR A b)^-1 ▹ _).
    + apply rassociator.
    + apply (_ ◃ lassociator _ _ _).
    + apply (_ ◃ (wild_functor_comp (adj_right A) _ _ ▹ _)).
    + apply (_ ◃ ((##(adj_right A) (wild_nat_iso_r (adj_counit A) b) ) ▹ _)).
    + apply (_ ◃ (((wild_functor_id _ _)^-1) ▹ _)).
    + apply (_ ◃ lunitor _).
    + apply (wild_nat_iso_r (adj_unit A) (adj_right A b)).
  - refine (_ • _ • _ • _ • _ • _ • _ • _ • _).
    + apply ((wild_nat_iso_r (adj_unit A) (adj_right A b))^-1).
    + apply (_ ◃ linvunitor _).
    + apply (_ ◃ ((wild_functor_id (adj_right A) _ ) ▹ _)).
    + apply (_ ◃ ((##(adj_right A) ((wild_nat_iso_r (adj_counit A) b)^-1)) ▹ _)).
    + apply (_ ◃ ((wild_functor_comp (adj_right A) _ _)^-1 ▹ _)).
    + apply (_ ◃ rassociator _ _ _).
    + apply lassociator.
    + apply (adj_tR A b ▹ _).
    + apply lunitor.    
Qed.
