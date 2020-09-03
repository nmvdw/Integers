(* Given a prebicategory C and a pseudofunctor F : C -> C, define a prebicategory of F-algebras *)
(* conform  'Constructing Higher ...', Example 2.9 *)
(* Using `unit` as 2-cells *)
(* From UniMath/Bicategories/DisplayedBicats/Examples/Algebras.v *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.Bicategories.TypePrebicat.
Require Import Integers.Bicategories.Invertible_2cells.
Require Import Integers.Bicategories.Unitors.
Require Import Integers.Bicategories.BicategoryLaws.
Require Import Integers.Bicategories.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import Integers.Bicategories.DispPrebicat.
Import DispPrebicat.Notations.

Require Import Integers.Bicategories.PseudoTransformation.
Require Import Integers.Bicategories.Composition.
Require Import Integers.Bicategories.Projection.


Local Open Scope cat.
Section Algebra.
  Context {C : prebicat}.
  Variable (F : pseudofunctor C C).

  Locate disp_functor_data.
  Definition disp_f_alg_ob_mor : Core.disp_cat_ob_mor C.
  Proof.
    use tpair.
    - intro a.
      exact (F a --> a).
    - intros a b ha hb f.
      exact (invertible_2cell (ha · f) (#F f · hb)).
  Defined.

  Definition disp_f_alg_id_comp
    : Core.disp_cat_id_comp C disp_f_alg_ob_mor.
  Proof.
    split.
    - cbn. intros a ha.
      refine (runitor ha • linvunitor ha • (pseudofunctor_id F a ▹ ha) ,, _).
      is_iso.
      exact (pseudofunctor_id F a).
    - cbn. intros a b c f g ha hb hc ff gg.
      refine ((lassociator ha f g)
                • (ff ▹ g)
                • rassociator (#F f) hb g
                • (#F f ◃ gg)
                • lassociator (#F f) (#F g) hc
                • (pseudofunctor_comp F f g ▹ hc) ,, _).
      is_iso.
      + exact ff.
      + exact gg.
      + exact (pseudofunctor_comp F f g).
  Defined.

  Definition disp_f_alg_1_id_comp_cells : disp_prebicat_1_id_comp_cells C.
  Proof.
    use tpair.
    - use tpair.
      + exact disp_f_alg_ob_mor.
      + exact disp_f_alg_id_comp.
    - intros a b f g θ. cbn. intros ha hb ff gg.
      exact unit.
  Defined.

  Definition disp_f_alg_ops : disp_prebicat_ops' disp_f_alg_1_id_comp_cells.
  Proof.
    repeat split.
  Qed.

  Definition disp_f_alg_ops_laws : disp_prebicat_laws (_ ,, disp_f_alg_ops).
  Proof.
    repeat split; intro; intros; apply isapropunit.
  Qed.

  Definition disp_f_alg_prebicat : disp_prebicat C
    := (_ ,, disp_f_alg_ops_laws).

  Definition prebicat_algebra := total_prebicat disp_f_alg_prebicat.
End Algebra.
