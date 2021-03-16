(*
 - Direct product of two displayed wild categories over a wild category
From 'UniMath/Bicategories/DisplayedBicats/Examples/Prod.v'
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.WildCategories.WildCat.
Require Import Integers.WildCategories.DispWildCat. Import DispWildCat.Notations.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.

(** Direct product of displayed wild categories **)
Section disp_wild_cat_prod.
  Context {C : wild_cat}.
  Variable (D1 D2 : disp_wild_cat C).

  Definition disp_dirprod_wild_cat_1_id_comp_cells : disp_wild_cat_1_id_comp_cells C.
  Proof.
    exists (dirprod_disp_cat_data D1 D2).
    intros c c' f g x d d' f' g'.
    cbn in *.
    exact ( (pr1 f' ==>[ x ] pr1 g') × (pr2 f' ==>[ x ] pr2 g')).
  Defined.

  Definition disp_dirprod_wild_cat_ops : disp_wild_cat_ops disp_dirprod_wild_cat_1_id_comp_cells.
  Proof.
    repeat (use tpair).
    - cbn. intros.
      apply (make_dirprod (disp_id2 _ ) (disp_id2  _)).
    - cbn. intros.
      apply (make_dirprod (disp_lunitor _ ) (disp_lunitor  _)).
    - cbn. intros.
      apply (make_dirprod (disp_runitor _ ) (disp_runitor  _)).
    - cbn. intros.
      apply (make_dirprod (disp_linvunitor _ ) (disp_linvunitor  _)).
    - cbn. intros.
      apply (make_dirprod (disp_rinvunitor _ ) (disp_rinvunitor  _)).
    - cbn. intros.
      apply (make_dirprod (disp_rassociator _ _ _ ) (disp_rassociator _ _ _)).
    - cbn. intros.
      apply (make_dirprod (disp_lassociator _ _ _ ) (disp_lassociator _ _ _)).
    - cbn. intros.
      apply (make_dirprod (disp_vcomp2 (pr1 X) (pr1 X0)) (disp_vcomp2 (pr2 X) (pr2 X0))).
    - cbn. intros.
      apply (make_dirprod (disp_lwhisker (pr1 ff) (pr1 X)) (disp_lwhisker (pr2 ff) (pr2 X))).
    - cbn. intros.
      apply (make_dirprod (disp_rwhisker (pr1 gg) (pr1 X)) (disp_rwhisker (pr2 gg) (pr2 X))).
  Defined.

  Definition disp_dirprod_wild_cat : disp_wild_cat C := _ ,, disp_dirprod_wild_cat_ops.
End disp_wild_cat_prod.
