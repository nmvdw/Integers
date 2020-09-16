(** Direct product of two displayed precategories over a precategory **)
(* Copied from UniMath/Bicategories/DisplayedBicats/Examples/Prod.v *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.Prebicategories.DispPrebicat. Import DispPrebicat.Notations.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.


Section Disp_PreDirprod.
  Context {C : prebicat}. (* <- This is the main difference with the original file *)
  Variable (D1 D2 : disp_prebicat C).

  Definition disp_dirprod_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells C.
  Proof.
    exists (dirprod_disp_cat_data D1 D2).
    intros c c' f g x d d' f' g'.
    cbn in *.
    exact ( (pr1 f' ==>[ x ] pr1 g') × (pr2 f' ==>[ x ] pr2 g')).
  Defined.

  Definition disp_dirprod_prebicat_ops : disp_prebicat_ops' disp_dirprod_prebicat_1_id_comp_cells.
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

  Definition disp_dirprod_prebicat_data : disp_prebicat_data C := _ ,, disp_dirprod_prebicat_ops.

  Definition disp_dirprod_brebicat_laws : disp_prebicat_laws disp_dirprod_prebicat_data.
  Proof.
    repeat split; intro.
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_id2_left _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_id2_right _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_vassocr _ _ _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_lwhisker_id2 _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_id2_rwhisker _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_lwhisker_vcomp _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_rwhisker_vcomp _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_vcomp_lunitor _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_vcomp_runitor _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_lwhisker_lwhisker _ _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_rwhisker_lwhisker _ _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_rwhisker_rwhisker _ _ _ _ _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_vcomp_whisker _ _  _ _ _ _ _ _ _ _ _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_lunitor_linvunitor _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_linvunitor_lunitor _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_runitor_rinvunitor _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_rinvunitor_runitor _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_lassociator_rassociator _ _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_rassociator_lassociator _ _ _ _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_runitor_rwhisker _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_lassociator_lassociator _ _ _ _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  Qed.

  Definition disp_dirprod_prebicat : disp_prebicat C := _ ,, disp_dirprod_brebicat_laws.
End Disp_PreDirprod.
