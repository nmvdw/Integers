(* Adding 2 cells using a wild category C *)
(* Conform 'Bicategories in Univalent Foundations', Definition 9.12 using prebicategories, or 'Constructing Higher ...', Example 2.11, using prebicategories and T=Id. *)
(* But with `unit` as 1-cells *)
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


Section Add2CellUnit.
  Context {C : wild_cat}.
  Variable (D : disp_wild_cat C).

  Variable (S : wild_functor C C).
  Variable (l r : wild_nat_trans (pr1_wild_functor D ⋯ S) (pr1_wild_functor D)).

  Definition disp_add_cell_data : disp_wild_cat_1_id_comp_cells (total_wild_cat D).
  Proof.
    use tpair.
    - use tpair.
      + use tpair.
        * exact (λ Aa, l Aa ==> r Aa).
        * exact (λ Aa Bb α β ff, unit).
      + split.
        * exact (λ Aa α, tt).
        * exact (λ Aa Bb Cc f g α β γ Hf Hg, tt).
    - intros Aa Bb f g θ hAa hBb hf hg. cbn in hAa, hBb.
      exact unit.
  Defined.

  Definition disp_add_cell : disp_wild_cat (total_wild_cat D).
  Proof.
    use tpair.
    - exact disp_add_cell_data.
    - repeat split.
  Defined.
End Add2CellUnit.
