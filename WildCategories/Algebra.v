(* Given a prebicategory C and a pseudofunctor F : C -> C, define a prebicategory of F-algebras *)
(* conform  'Constructing Higher ...', Example 2.9 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.WildCategories.WildCat.
Require Import Integers.WildCategories.DispWildCat. Import DispWildCat.Notations.
Require Import Integers.WildCategories.Invertible_2cells.
Require Import Integers.WildCategories.WildFunctor.
Import WildFunctor.Notations.

Local Open Scope cat.

Section Algebra.
  Context {C : wild_cat}.
  Variable (F : wild_functor C C).

  Definition disp_alg_data : disp_wild_cat_1_id_comp_cells C.
  use tpair.
  - use tpair.
    + use tpair.
      * exact (λ a, F a --> a).
      * cbn. intros a b ha hb f.
         exact (invertible_2cell (ha · f) (#F f · hb)).
    + split.
      * cbn. intros a ha.
         use make_invertible_2cell.
         -- exact (runitor ha • linvunitor ha • (wild_functor_id F a ▹ ha)).
         -- is_iso.
            exact (wild_functor_id F a).
      * cbn. intros a b c f g ha hb hc hf hg.
         use make_invertible_2cell.
         -- exact ((lassociator ha f g)
                     • (hf ▹ g)
                     • rassociator (#F f) hb g
                     • (#F f ◃ hg)
                     • lassociator (#F f) (#F g) hc
                     • (wild_functor_comp F f g ▹ hc)).
         -- is_iso.
            ++ exact hf.
            ++ exact hg.
            ++ exact (wild_functor_comp F f g).
  - exact (λ a b f g θ ha hb hf hg, unit).
  Defined.

  Definition disp_alg : disp_wild_cat C.
  Proof.
    use tpair.
    - exact disp_alg_data.
    - repeat split.
  Defined.
  
  Definition wild_cat_alg := total_wild_cat disp_alg.
End Algebra.
