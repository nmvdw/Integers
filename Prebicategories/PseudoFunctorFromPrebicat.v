(** Pseudofunctors over precategories **)
(* Compiled from different files in UniMath/Bicategories *)
(* Invertible_2cells.v, Unitors.v, BicategoryLaws.v are modified versions of their counterparts in the UniMath library, I changed `bicat` to `prebicat`. *)
(* `map1cells_ops_laws` in Map1Cells.v uses `apply D`, which probably uses the fact that 2-cells are sets, so bigger changes have to be made there (see bottom of this file). *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
(*Require Import UniMath.Bicategories.Core.BicategoryLaws.*)
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.Prebicategories.TypePrebicat.
Require Import Integers.Prebicategories.DispPrebicat.
Require Import Integers.Prebicategories.BicategoryLaws.
Require Import Integers.Prebicategories.Unitors.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.

(* from UM/Bi/PF/Display/Base.v *)
Section BasePseudoFunctor.
  Variable (C D : prebicat). (* <- *)

Definition ps_base_data : prebicat_data.
  Proof.
    use build_prebicat_data.
    - exact (ob C → ob D).
    - exact (λ f g, ∏ (x : C), f x --> g x).
    - exact (λ f g α β, ∏ (x : C), α x ==> β x).
    - exact (λ f x, id₁ (f x)).
    - exact (λ f g h α β x, α x · β x).
    - exact (λ f g α x, id₂ (α x)).
    - exact (λ f g α β γ m₁ m₂ x, m₁ x • m₂ x).
    - exact (λ f g h α β γ m x, α x ◃ m x).
    - exact (λ f g h α β γ m x, m x ▹ γ x).
    - exact (λ f g α x, lunitor (α x)).
    - exact (λ f g α x, linvunitor (α x)).
    - exact (λ f g α x, runitor (α x)).
    - exact (λ f g α x, rinvunitor (α x)).
    - exact (λ f₁ f₂ f₃ f₄ α β γ x, lassociator (α x) (β x) (γ x)).
    - exact (λ f₁ f₂ f₃ f₄ α β γ x, rassociator (α x) (β x) (γ x)).
  Defined.

  Definition ps_base_laws : prebicat_laws ps_base_data.
  Proof.
    repeat split ; intros ; apply funextsec ; intro.
    - apply id2_left.

    - apply id2_right.
    - apply vassocr.
    - apply lwhisker_id2.
    - apply id2_rwhisker.
    - apply lwhisker_vcomp.
    - apply rwhisker_vcomp.
    - apply vcomp_lunitor.
    - apply vcomp_runitor.
    - apply lwhisker_lwhisker.
    - apply rwhisker_lwhisker.
    - apply rwhisker_rwhisker.
    - apply vcomp_whisker.
    - apply lunitor_linvunitor.
    - apply linvunitor_lunitor.
    - apply runitor_rinvunitor.
    - apply rinvunitor_runitor.
    - apply lassociator_rassociator.
    - apply rassociator_lassociator.
    - apply runitor_rwhisker.
    - apply lassociator_lassociator.
  Qed.

  Definition ps_base : prebicat.
  Proof.
    unfold prebicat.
    exists ps_base_data.
    exact ps_base_laws.
  Defined.

End BasePseudoFunctor.
    
(* from UM/Bi/PF/Display/Map1Cells.v *)
Section Map1Cells.
  Variable (C D : prebicat). (* <- *)

  Definition map1cells_disp_cat : disp_cat_ob_mor (ps_base C D).
  Proof.
    use tpair.
    - exact (λ F₀, ∏ (X Y : C), X --> Y → F₀ X --> F₀ Y).
    - exact (λ F₀ G₀ F₁ G₁ η, ∏ (X Y : C) (f : X --> Y),
             invertible_2cell (η X · G₁ X Y f) (F₁ X Y f · η Y)).
  Defined.
  

  Definition map1cells_disp_cat_id_comp : disp_cat_id_comp (ps_base C D) map1cells_disp_cat.
  Proof.
    use tpair.
    - cbn.
      refine (λ F₀ F₁ X Y f, (lunitor (F₁ X Y f) • rinvunitor (F₁ X Y f) ,, _)). Locate is_iso.
      is_iso.
    - cbn.
      refine (λ F₀ G₀ H₀ η₁ ε₁ F₁ G₁ H₁ η₂ ε₂ X Y f,
              (rassociator (η₁ X) (ε₁ X) (H₁ X Y f))
                • (η₁ X ◃ ε₂ X Y f)
                • lassociator (η₁ X) (G₁ X Y f) (ε₁ Y)
                • (η₂ X Y f ▹ ε₁ Y)
                • rassociator (F₁ X Y f) (η₁ Y) (ε₁ Y) ,, _).
      is_iso.
      + apply ε₂.
      + apply η₂.
  Defined.

  Definition map1cells_disp_cat_2cell : disp_2cell_struct map1cells_disp_cat
    := λ F₀ G₀ η₁ ε₁ m F₁ G₁ η₂ ε₂,
       ∏ (X Y : C) (f : X --> Y),
       η₂ X Y f • (F₁ X Y f ◃ m Y)
       =
       (m X ▹ G₁ X Y f) • ε₂ X Y f.

  Definition map1cells_prebicat_1 : disp_prebicat_1_id_comp_cells (ps_base C D).
  Proof.
    use tpair.
    - use tpair.
      + exact map1cells_disp_cat.
      + exact map1cells_disp_cat_id_comp.
    - exact (λ F₀ G₀ η₁ ε₁ m F₁ G₁ η₂ ε₂,
             ∏ (X Y : C) (f : X --> Y),
             η₂ X Y f • (F₁ X Y f ◃ m Y)
             =
             (m X ▹ G₁ X Y f) • ε₂ X Y f).
  Defined.

  Definition map1cells_ops : disp_prebicat_ops' map1cells_prebicat_1.
  Proof.
    repeat split.
    - intros F₀ G₀ η₁ F₁ G₁ η₂ X Y f ; cbn in *.
      rewrite lwhisker_id2, id2_right.
      rewrite id2_rwhisker, id2_left.
      reflexivity.
    - intros F₀ G₀ η₁ F₁ G₁ η₂ X Y f ; cbn in *.
      rewrite !vassocl.
      rewrite (lwhisker_hcomp _ (lunitor _)).
      rewrite triangle_l.
      rewrite <- !rwhisker_hcomp.
      rewrite rwhisker_vcomp.
      rewrite !vassocl.
      rewrite rinvunitor_runitor, id2_right.
      rewrite lunitor_triangle.
      rewrite vcomp_lunitor.
      use Invertible_2cells.vcomp_move_R_pM.
      { is_iso. }
      cbn.
      rewrite !vassocr.
      rewrite <- lunitor_assoc.
      reflexivity.
    - intros F₀ G₀ η₁ F₁ G₁ η₂ X Y f ; cbn in *.
      rewrite !vassocl.
      use Invertible_2cells.vcomp_move_R_pM.
      { is_iso. }
      cbn.
      refine (_ @ vassocl _ _ _).
      rewrite !runitor_triangle.
      rewrite (rwhisker_hcomp _ (runitor _)).
      rewrite <- triangle_r.
      rewrite vcomp_runitor.
      rewrite <- lwhisker_vcomp, <- lwhisker_hcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite rinvunitor_triangle.
      rewrite rinvunitor_runitor, id2_left.
      reflexivity.
    - intros F₀ G₀ η₁ F₁ G₁ η₂ X Y f ; cbn in *.
      rewrite !vassocr.
      use Invertible_2cells.vcomp_move_L_Mp.
      { is_iso. }
      cbn.
      refine (vassocl _ _ _ @ _).
      rewrite <- linvunitor_assoc.
      rewrite lwhisker_hcomp.
      rewrite triangle_l_inv, <- rwhisker_hcomp.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
      rewrite lunitor_triangle.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite vcomp_lunitor.
      rewrite !vassocr.
      rewrite linvunitor_lunitor, id2_left.
      reflexivity.
    - intros F₀ G₀ η₁ F₁ G₁ η₂ X Y f ; cbn in *.
      rewrite !vassocr.
      use Invertible_2cells.vcomp_move_L_Mp.
      { is_iso. }
      cbn.
      refine (vassocl _ _ _ @ _).
      rewrite rinvunitor_triangle.
      rewrite (rwhisker_hcomp _ (rinvunitor _)).
      rewrite <- triangle_r_inv.
      rewrite <- lwhisker_hcomp.
      rewrite lwhisker_vcomp.
      rewrite !vassocr.
      rewrite linvunitor_lunitor, id2_left.
      rewrite rinvunitor_triangle.
      rewrite rinvunitor_natural.
      rewrite <- rwhisker_hcomp.
      reflexivity.
    - intros F₀ G₀ H₀ K₀ α₁ η₁ ε₁ F₁ G₁ H₁ K₁ α₂ η₂ ε₂ X Y f ; cbn in *.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocl.
      refine (!(_ @ _)).
      {
        rewrite !vassocr.
        do 7 apply maponpaths_2.
        symmetry.
        rewrite lwhisker_hcomp, rwhisker_hcomp.
        rewrite vassocl.
        apply inverse_pentagon.
      }
      rewrite !vassocl.
      apply maponpaths.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      use Invertible_2cells.vcomp_move_L_pM.
      { is_iso. }
      cbn.
      etrans.
      {
        rewrite !vassocr.
        do 5 apply maponpaths_2.
        rewrite lwhisker_hcomp.
        rewrite vassocl, <- inverse_pentagon_6.
        rewrite <- rwhisker_hcomp.
        reflexivity.
      }
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        reflexivity.
      }
      apply maponpaths.
      use Invertible_2cells.vcomp_move_L_pM.
      { is_iso. }
      cbn.
      etrans.
      {
        rewrite !vassocr.
        do 3 apply maponpaths_2.
        rewrite !vassocl.
        rewrite lwhisker_hcomp, rwhisker_hcomp.
        symmetry.
        apply inverse_pentagon.
      }
      rewrite (lwhisker_hcomp _ (rassociator _ _ _)), (rwhisker_hcomp _ (rassociator _ _ _)).
      rewrite <- inverse_pentagon.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_rwhisker_alt.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite rassociator_lassociator, id2_right.
      reflexivity.
    - intros F₀ G₀ H₀ K₀ α₁ η₁ ε₁ F₁ G₁ H₁ K₁ α₂ η₂ ε₂ X Y f ; cbn in *.
      rewrite <- !lwhisker_vcomp, <- !rwhisker_vcomp.
      rewrite !vassocl.
      use Invertible_2cells.vcomp_move_L_pM.
      { is_iso. }
      cbn.
      etrans.
      {
        rewrite !vassocr.
        do 8 apply maponpaths_2.
        rewrite lwhisker_hcomp, rwhisker_hcomp.
        symmetry.
        rewrite !vassocl.
        apply inverse_pentagon.
      }
      rewrite !vassocl.
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite lwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        reflexivity.
      }
      apply maponpaths.
      use Invertible_2cells.vcomp_move_L_pM.
      { is_iso. }
      cbn.
      etrans.
      {
        rewrite !vassocr.
        rewrite inverse_pentagon.
        rewrite <- lwhisker_hcomp, <- rwhisker_hcomp.
        rewrite !vassocl.
        rewrite !(maponpaths (λ z, _ • (_ • z)) (vassocr _ _ _)).
        rewrite lwhisker_vcomp.
        rewrite rassociator_lassociator.
        rewrite lwhisker_id2, id2_left.
        rewrite !vassocl.
        reflexivity.
      }
      apply maponpaths.
      etrans.
      {
        rewrite !vassocr.
        rewrite rwhisker_lwhisker_rassociator.
        rewrite !vassocl.
        reflexivity.
      }
      apply maponpaths.
      use Invertible_2cells.vcomp_move_L_pM.
      { is_iso. }
      cbn.
      etrans.
      {
        rewrite !vassocr.
        do 4 apply maponpaths_2.
        rewrite vassocl, lwhisker_hcomp, rwhisker_hcomp.
        symmetry.
        apply inverse_pentagon.
      }
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite rassociator_lassociator, id2_left.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      symmetry.
      rewrite lwhisker_hcomp, rwhisker_hcomp.
      apply inverse_pentagon_6.
    - intros F₀ G₀ α₁ η₁ ε₁ m₂ n₂ F₁ G₁ α₂ η₂ ε₂ m₃ n₃ X Y f ; cbn in *.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocr.
      rewrite m₃.
      rewrite !vassocl.
      rewrite n₃.
      rewrite !vassocr.
      rewrite rwhisker_vcomp.
      reflexivity.
    - intros F₀ G₀ H₀ α₁ η₁ ε₁ m₂ F₁ G₁ H₁ α₂ η₂ ε₂ m₃ X Y f ; cbn in *.
      rewrite !vassocr.
      rewrite <- rwhisker_lwhisker_rassociator.
      rewrite !vassocl.
      apply maponpaths.
      rewrite lwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite lwhisker_vcomp.
      rewrite <- m₃.
      rewrite <- lwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      rewrite vcomp_whisker.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      reflexivity.
    - intros F₀ G₀ H₀ α₁ η₁ ε₁ m₂ F₁ G₁ H₁ α₂ η₂ ε₂ m₃ X Y f ; cbn in *.
      rewrite !vassocr.
      rewrite rwhisker_rwhisker_alt.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite vcomp_whisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_vcomp.
      rewrite m₃.
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      rewrite <- rwhisker_rwhisker.
      reflexivity.
  Qed.
  
(*
  Definition map1cells_ops_laws : disp_prebicat_laws (_ ,, map1cells_ops).
  Proof.
    repeat split ; intro ; intros ; do 3 (apply funextsec ; intro) ; apply D.
  Qed.

  Definition map1cells_disp_prebicat : disp_prebicat (ps_base C D)
    := (_ ,, map1cells_ops_laws).

    

    
    (* from UM/Bi/PF/Display/PseudoFunctorBicat.v *)
Section pseudofunctors.
  Variable (C D : prebicat). (* <- *)

  Definition psfunctor_data_disp : disp_prebicat (map1cells C D).
*)
