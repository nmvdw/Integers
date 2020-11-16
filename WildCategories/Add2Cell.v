(* Adding 2 cells using a wild category C *)
(* Conform 'Bicategories in Univalent Foundations', Definition 9.12 using prebicategories, or 'Constructing Higher ...', Example 2.11, using prebicategories and T=Id. *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.WildCategories.WildCat.
Require Import Integers.WildCategories.DispWildCat.
Require Import Integers.WildCategories.Invertible_2cells.
Require Import Integers.WildCategories.WildFunctor.
Import WildFunctor.Notations.
Require Import Integers.WildCategories.WildNaturalTransformation.
Import WildNaturalTransformation.Notations.

Local Open Scope cat.
Local Open Scope mor_disp_scope.


Section AddEndpoints.
  Context {C : wild_cat}.
  Variable (D : disp_wild_cat C).

  Variable (S : wild_functor C C).
  Variable (l r : wild_nat_trans (pr1_wild_functor D ⋯ S) (pr1_wild_functor D)).

  Definition add_cell_disp_data : disp_wild_cat_1_id_comp_cells (total_wild_cat D).
  Proof.
    use tpair.
    - use tpair.
      + use tpair.
        * exact (λ Aa, l Aa ==> r Aa).
        * exact (λ Aa Bb α β ff, α ▹ #(pr1_wild_functor D) ff • $ r ff
                                 = $ l ff • (#S (#(pr1_wild_functor D) ff) ◃ β)).
          
      + split.
        * intros Aa α. simpl. cbn in α.
          
