(* Given a wild category C, a type I, and for every i : I a displayed wild category, then we can make a displayed wild category with dependent functions as objects. *)
(* conform  'Constructing Higher ...', Example 2.10 *)
(* From UniMath/Bicategories/DisplayedBicats/Examples/DispDepProd.v *)

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
Local Open Scope mor_disp_scope.

Section DispDepProd.
  Context {C : wild_cat} (I : UU) (D : I → disp_wild_cat C).

  Definition disp_depprod_data : disp_wild_cat_1_id_comp_cells C.
  Proof.
    use tpair.
      + use tpair.
        * use tpair.
          -- exact (λ a, ∏ i : I, D i a).
          -- exact (λ a b ha hb f, ∏ i : I, ha i -->[ f ] hb i).
        * split.
          -- exact (λ a ha i, id_disp (ha i)).
          -- exact (λ a b c f g ha hb hc hf hg i, hf i ;; hg i).
      + exact (λ a b f g θ ha hb hf hg, ∏ i : I, hf i ==>[ θ ] hg i).
  Defined.

  Definition disp_depprod : disp_wild_cat C.
  Proof.
    use tpair.
    - exact disp_depprod_data.
    - repeat split.
      + exact (λ a b f ha hb hf i, disp_id2 (hf i)).
      + exact (λ a b f ha hb hf i, disp_lunitor (hf i)).
      + exact (λ a b f ha hb hf i, disp_runitor (hf i)).
      + exact (λ a b f ha hb hf i, disp_linvunitor (hf i)).
      + exact (λ a b f ha hb hf i, disp_rinvunitor (hf i)).
      + exact (λ a b c d f g h ha hb hc hd hf hg hh i,
               disp_rassociator (hf i) (hg i) (hh i)).
      + exact (λ a b c d f g h ha hb hc hd hf hg hh i,
               disp_lassociator (hf i) (hg i) (hh i)).
      + exact (λ a b f g h θ γ ha hb hf hg hh hθ hγ i, hθ i •• hγ i).
      + exact (λ a b c f g1 g2 θ ha hb hc hf hg1 hg2 hθ i, hf i ◃◃ hθ i).
      + exact (λ a b c f1 f2 g θ ha hb hc hf1 hf2 hg hθ i, hθ i ▹▹ hg i).
  Defined.

  Definition depprod_wild_cat := total_wild_cat disp_depprod.
End DispDepProd.
