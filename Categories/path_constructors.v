Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.Type.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import Integers.Categories.disp_precat.
Require Import Integers.Categories.total_precat.
Require Import Integers.Categories.point_constructors.

Local Open Scope cat.
Local Open Scope mor_disp.


(** Adding endpoints using a precategory C **)
(* Conform 'Bicategories in Univalent Foundations', Definition 9.12 using precategories, or 'Constructing Higher ...', Example 2.11, using precategories and T=Id. *)

Definition add_path_endpoints_ob_mor {C : precategory} {D : disp_precat C} {S : functor C C} (l r : nat_trans (functor_composite (pr1_precat D) S) (pr1_precat D)) : disp_cat_ob_mor (total_precategory D).
Proof.
  use make_disp_cat_ob_mor.
    + intro Aa.
      exact (l Aa = r Aa).
    + intros Aa Bb α β f.
      exact (maponpaths (λ x, x · _) α @ !nat_trans_ax r Aa Bb f = !nat_trans_ax l Aa Bb f @ maponpaths (λ x, _ · x) β).
      (** alternative:
      pose (cancel_postcomposition (l Aa) (r Aa) (functor_on_morphisms (pr1_precat D) f) α) as αf.
      pose (cancel_precomposition _ _ _ _ (l Bb) (r Bb) (functor_on_morphisms (functor_composite (pr1_precat D) S) f) β) as Sfβ. 
      exact (αf @ !nat_trans_ax r Aa Bb f = !nat_trans_ax l Aa Bb f @ Sfβ). *)
Defined.


(* Attempt at adding identity and composition to this *)
Definition add_path_endpoints_id_comp {C : precategory} {D : disp_precat C} {S : functor C C} (l r : nat_trans (functor_composite (pr1_precat D) S) (pr1_precat D)) : disp_cat_id_comp (total_precategory D) (add_path_endpoints_ob_mor l r).
Proof.
  split.
    + intro Aa. simpl. intros α.
      refine (!_).
      pose (λ x : C ⟦ S (pr1 Aa), pr1 Aa ⟧, x · identity (pr1 Aa)) as f.
      pose (λ x : C ⟦ S (pr1 Aa), pr1 Aa ⟧, (# S)%Cat (identity (pr1 Aa)) · x) as g.
      assert (H : homotsec f g).
      {
        unfold homotsec.
        intro x.
        unfold f.
        unfold g.
        refine (_ @ !(_ @ _)).
        - apply id_right.
        - apply (maponpaths (λ y, y · x) (functor_id S (pr1 Aa))).
        - apply id_left.
      }

      unfold f in H.
      unfold g in H.

Abort.


(** Adding endpoints using type_precat as base precategory **)
Definition add_paths_endpoints_type_precat_data {D : disp_precat type_precat} {S : functor type_precat type_precat} (l r : nat_trans (functor_composite (pr1_precat D) S) (pr1_precat D)) : disp_cat_data (total_precategory D).
Proof.
  use tpair.
  - use make_disp_cat_ob_mor.
    + intro Aa.
      exact (∏ x, l Aa x = r Aa x).
    + intros Aa Bb α β f.
      exact (∏ x, eqtohomot (!nat_trans_ax l Aa Bb f) x @ β (functor_on_morphisms (functor_composite (pr1_precat D) S) f x) = maponpaths (functor_on_morphisms (pr1_precat D) f) (α x) @ eqtohomot (!nat_trans_ax r Aa Bb f) x).
  - split.
    + simpl. intros Aa α x.

      refine (_ @ _ @ _ @ _ @ _ @ _).
      * apply maponpaths.
Abort.

