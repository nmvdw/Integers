(* Adding 2 cells using a wild category C *)
(* Conform 'Bicategories in Univalent Foundations', Definition 9.12 using prebicategories, or 'Constructing Higher ...', Example 2.11, using prebicategories and T=Id. *)
(* It needs some extra information as input *)
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

Section Add2Cell.
  Context {C : wild_cat}.
  Variable (D : disp_wild_cat C).

  Variable (S : wild_functor C C).
  Variable (l r : wild_nat_trans (pr1_wild_functor D ⋯ S) (pr1_wild_functor D)).

  Variable (p : ∏ {Aa : total_wild_cat D} (α : l Aa ==> r Aa),
                α ▹ id₁ (pr1 Aa) • $r (identity Aa)
                =
                $l (identity Aa) • (#S (id₁ (pr1 Aa)) ◃ α)).

  Variable (q : ∏ {Aa Bb Cc : total_wild_cat D} {f : Aa --> Bb} {g : Bb --> Cc}
                  {α : l Aa ==> r Aa} {β : l Bb ==> r Bb} {γ : l Cc ==> r Cc}
                  (ff : (α ▹ pr1 f) • $ r f = $ l f • (# S (pr1 f) ◃ β))
                  (gg : (β ▹ pr1 g) • $ r g = $ l g • (# S (pr1 g) ◃ γ)),
                (α ▹  pr1 f · pr1 g) • $ r (f · g)
                =
                $ l (f · g) • (# S (pr1 f · pr1 g) ◃ γ)).

  Definition disp_add_cell_data : disp_wild_cat_1_id_comp_cells (total_wild_cat D).
  Proof.
    use tpair.
    - use tpair.
      + use tpair.
        * exact (λ Aa, l Aa ==> r Aa).
        * exact (λ Aa Bb α β ff, α ▹ #(pr1_wild_functor D) ff • $ r ff
                                 = $ l ff • (#S (#(pr1_wild_functor D) ff) ◃ β)).
      + split.
        * intros Aa α. simpl. cbn. 
          exact (p α).          
        * intros Aa Bb Cc f g α β γ. cbn in α, β, γ. simpl. intros ff gg. cbn in ff, gg. cbn.
          exact (q ff gg).
    - cbn. intros Aa Bb. cbn. clear p. clear q. intros f g θ hAa hBb hf hg.
      exact unit.
  Defined.

  Definition disp_add_cell : disp_wild_cat (total_wild_cat D).
  Proof.
    use tpair.
    - exact disp_add_cell_data.
    - repeat split.
  Defined.
End Add2Cell.
