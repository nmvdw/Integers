(* 
 - Some auxiliary lemmas
 - Definition of 'DFcell'
From 'UniMath/Bicategories/DisplayedBicats/Examples/Add2Cell.v' and 'UniMath/Bicategories/Core/BicategoryLaws.v'
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.Prebicategories.DispPrebicat.
Require Import Integers.Prebicategories.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import Integers.Prebicategories.PseudoTransformation.
Require Import Integers.Prebicategories.Composition.
Require Import Integers.Prebicategories.Identity.
Require Import Integers.Prebicategories.Projection.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.

(** Auxiliary lemmas **)
Definition linvunitor_natural
           {C : prebicat}
           {X Y : C}
           {f g : C⟦X, Y⟧}
           (η : f ==> g)
  : linvunitor g o η = (η ⋆⋆ id₂ (id₁ X)) o linvunitor f.
Proof.
  use (vcomp_rcancel (lunitor _ )).
  { apply is_invertible_2cell_lunitor. }
  rewrite vassocl.
  rewrite linvunitor_lunitor.
  use (vcomp_lcancel (lunitor _ )).
  { apply is_invertible_2cell_lunitor. }
  repeat rewrite vassocr.
  rewrite lunitor_linvunitor.
  rewrite id2_left, id2_right.
  apply (! lunitor_natural _ _ _ _ _ ).
Qed.

Definition lwhisker_hcomp
           {C : prebicat}
           {X Y Z : C}
           {f g : C⟦Y,Z⟧}
           (h : C⟦X, Y⟧)
           (α : f ==> g)
  : h ◃ α = id₂ h ⋆ α.
Proof.
  unfold hcomp.
  rewrite id2_rwhisker.
  rewrite id2_left.
  reflexivity.
Qed.

(** Definition of DFcell **)
Section AddEndpoints.
  Context {C : prebicat}.
  Variable (D : disp_prebicat C).

  Variable (S T : pseudofunctor C C).
  Variable (l r : pseudotrans
                    (comp_pseudofunctor S (pr1_pseudofunctor D))
                    (comp_pseudofunctor T (pr1_pseudofunctor D))).

  Definition add_path_endpoints_ob_mor : Core.disp_cat_ob_mor (total_prebicat D).
  Proof.
    use tpair.
    - exact (λ Aa, l Aa ==> r Aa).
    - intros Aa Bb α β ff.
      exact ((α ▹ (#T (#(pr1_pseudofunctor D) ff))) • pseudonaturality_of r ff
             = (pseudonaturality_of l ff) • (#S (#(pr1_pseudofunctor D) ff) ◃ β)).
  Defined.      


  Definition add_path_endpoints_id_comp
    : Core.disp_cat_id_comp (total_prebicat D) add_path_endpoints_ob_mor.
  Proof.
    split.
    - intros x xx.
      pose (pseudotrans_id_alt l x) as p.
      simpl.
      cbn in p.
      rewrite !pseudofunctor_id2 in p.
      rewrite id2_left, id2_right in p.
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact p.
      }
      clear p.
      refine (!_).
      pose (pseudotrans_id_alt r x) as p.
      cbn in p.
      rewrite !pseudofunctor_id2 in p.
      rewrite id2_left, id2_right in p.
      etrans.
      {
        apply maponpaths.
        exact p.
      }
      clear p.
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite vcomp_runitor.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite linvunitor_natural.
      rewrite <- lwhisker_hcomp.
      rewrite !vassocl.
      rewrite vcomp_whisker.
      apply idpath.
    - intros x y z f g xx yy zz Hf Hg ; cbn.
      pose (pseudotrans_comp_alt l f g) as pl.
      pose (pseudotrans_comp_alt r f g) as pr.
      cbn in pl, pr ; rewrite pl, pr ; clear pl pr.
      rewrite !vassocr.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite <- rwhisker_rwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite <- lwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_vcomp.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths_2.
        apply maponpaths.
        apply Hf.
      }
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite lwhisker_vcomp.
      etrans.
      {
        apply maponpaths.
        apply Hg.
      }
      rewrite <- lwhisker_vcomp.
      reflexivity.
  Qed.

  Definition add_path_endpoints_1_id_comp_cells : disp_prebicat_1_id_comp_cells (total_prebicat D).
  Proof.
    use tpair.
    - use tpair.
      + exact add_path_endpoints_ob_mor.
      + exact add_path_endpoints_id_comp.
    - intros Aa Bb f g θ. cbn. intros α δ ε γ.
      exact unit.
  Defined.

  Definition add_path_endpoints_ops : disp_prebicat_ops' add_path_endpoints_1_id_comp_cells.
  Proof.
    repeat split; exact tt.
  Qed.

  (* DFcell *)
  Definition add_path_endpoints_prebicat : disp_prebicat (total_prebicat D).
  Proof.
    use tpair.
    - exists add_path_endpoints_1_id_comp_cells.
      exact add_path_endpoints_ops.
    - abstract (repeat use tpair; red; intros; apply (proofirrelevance _ isapropunit)).
  Defined.

  Definition add_path_endpoints : prebicat := total_prebicat add_path_endpoints_prebicat.
End AddEndpoints.
