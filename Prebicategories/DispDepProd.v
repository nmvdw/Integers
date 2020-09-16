(* Given a prebicategory C, a type I, and for every i : I a displayed prebicategory, then we can make a displayed prebicategory with dependent functions as objects. *)
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

Require Import Integers.Prebicategories.TypePrebicat.
Require Import Integers.Prebicategories.Invertible_2cells.
Require Import Integers.Prebicategories.Unitors.
Require Import Integers.Prebicategories.BicategoryLaws.
Require Import Integers.Prebicategories.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import Integers.Prebicategories.DispPrebicat.
Import DispPrebicat.Notations.

Require Import Integers.Prebicategories.PseudoTransformation.
Require Import Integers.Prebicategories.Composition.
Require Import Integers.Prebicategories.Projection.


Local Open Scope cat.
Local Open Scope mor_disp.

Section DispDepProd.
  Context {C : prebicat}
          (I : UU)
          (D : I → disp_prebicat C).

  Definition disp_depprod_cat_ob_mor : disp_cat_ob_mor C.
  Proof.
    use tpair.
    - exact (λ a, ∏ (i : I), D i a).
    - exact (λ a b ha hb f, ∏ i : I, ha i -->[ f ] hb i).
  Defined.

  Definition disp_depprod_cat_id_comp : disp_cat_id_comp C disp_depprod_cat_ob_mor.
  Proof.
    split.
    - exact (λ a ha i, id_disp (ha i)).
    - exact (λ a b c f g ha hb hc ff gg i, ff i ;; gg i).
  Defined.

  Definition disp_depprod_1_id_comp_cells : disp_prebicat_1_id_comp_cells C.
  Proof.
    use tpair.
    - use tpair.
      + exact disp_depprod_cat_ob_mor.
      + exact disp_depprod_cat_id_comp.
    - exact (λ a b f g θ ha hb ff gg, ∏ i : I, ff i ==>[ θ ] gg i).
  Defined.

  Definition disp_depprod_ops : disp_prebicat_ops' disp_depprod_1_id_comp_cells.
  Proof.
    repeat split.
    - exact (λ a b f ha hb ff i, disp_id2 (ff i)).
    - exact (λ a b f ha hb ff i, disp_lunitor (ff i)).
    - exact (λ a b f ha hb ff i, disp_runitor (ff i)).
    - exact (λ a b f ha hb ff i, disp_linvunitor (ff i)).
    - exact (λ a b f ha hb ff i, disp_rinvunitor (ff i)).
    - exact (λ a b c d f g h ha hb hc hd ff gg hh i,
             disp_rassociator (ff i) (gg i) (hh i)).
    - exact (λ a b c d f g h ha hb hc hd ff gg hh i,
             disp_lassociator (ff i) (gg i) (hh i)).
    - exact (λ a b f g h θ γ ha hb ff gg hh θθ γγ i, θθ i •• γγ i).
    - exact (λ a b c f g1 g2 θ ha hb hc ff gg1 gg2 θθ i, ff i ◃◃ θθ i).
    - exact (λ a b c f1 f2 g θ ha hb hc ff1 ff2 gg θθ i, θθ i ▹▹ gg i).
  Defined.
  
  Definition disp_depprod_prebicat_laws_help
             {a b : C}
             {f g : a --> b}
             {θ γ : f ==> g}
             {ha : ∏ (i : I), D i a}
             {hb : ∏ (i : I), D i b}
             {ff : ∏ (i : I), ha i -->[ f ] hb i}
             {gg : ∏ (i : I), ha i -->[ g ] hb i}
             (θθ : ∏ (i : I), ff i ==>[ γ ] gg i)
             (p : θ = γ)
             (i : I)
    : transportb (λ α : f ==> g, ff i ==>[ α ] gg i) p (θθ i)
      =
      transportb (λ α : f ==> g, ∏ (i : I), ff i ==>[ α ] gg i) p θθ i.
  Proof.
    induction p.
    apply idpath.
  Qed.


  Definition disp_depprod_ops_laws
    : disp_prebicat_laws (disp_depprod_1_id_comp_cells ,, disp_depprod_ops).
  Proof.
    repeat split; intro; intros; use funextsec; intro
    ; refine (_ @ disp_depprod_prebicat_laws_help _ _ _).
    - apply disp_id2_left.
    - apply disp_id2_right.
    - apply disp_vassocr.
    - apply disp_lwhisker_id2.
    - apply disp_id2_rwhisker.
    - apply disp_lwhisker_vcomp.
    - apply disp_rwhisker_vcomp.
    - apply disp_vcomp_lunitor.
    - apply disp_vcomp_runitor.
    - apply disp_lwhisker_lwhisker.
    - apply disp_rwhisker_lwhisker.
    - apply disp_rwhisker_rwhisker.
    - apply disp_vcomp_whisker.
    - apply disp_lunitor_linvunitor.
    - apply disp_linvunitor_lunitor.
    - apply disp_runitor_rinvunitor.
    - apply disp_rinvunitor_runitor.
    - apply disp_lassociator_rassociator.
    - apply disp_rassociator_lassociator.
    - apply disp_runitor_rwhisker.
    - apply disp_lassociator_lassociator.
  Qed.

  Definition disp_depprod_prebicat : disp_prebicat C
    := (_ ,, disp_depprod_ops_laws).

  Definition prebicat_depprod := total_prebicat disp_depprod_prebicat.
End DispDepProd.
