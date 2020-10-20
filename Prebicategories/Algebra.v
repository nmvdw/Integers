(* Given a prebicategory C and a pseudofunctor F : C -> C, define a prebicategory of F-algebras *)
(* conform  'Constructing Higher ...', Example 2.9 *)
(* ~~Using `unit` as 2-cells~~ why did I do this? *)
(* From UniMath/Bicategories/DisplayedBicats/Examples/Algebras.v *)
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
Section Algebra.
  Context {C : prebicat}.
  Variable (F : pseudofunctor C C).

  Locate disp_functor_data.
  Definition disp_alg_ob_mor : Core.disp_cat_ob_mor C.
  Proof.
    use tpair.
    - intro a.
      exact (F a --> a).
    - intros a b ha hb f.
      exact (invertible_2cell (ha · f) (#F f · hb)).
  Defined.

  Definition disp_alg_id_comp
    : Core.disp_cat_id_comp C disp_alg_ob_mor.
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

  Definition disp_alg_1_id_comp_cells : disp_prebicat_1_id_comp_cells C.
  Proof.
    use tpair.
    - use tpair.
      + exact disp_alg_ob_mor.
      + exact disp_alg_id_comp.
    - intros a b f g θ. cbn. intros ha hb ff gg.
      (* exact unit. *)
      exact (ha ◃ θ • gg = ff • (##F θ ▹ hb)).      
  Defined.

  Definition disp_alg_lunitor
             {a b : C}
             (f : a --> b)
             (ha : F a --> a)
             (hb : F b --> b)
             (ff : invertible_2cell (ha · f) (#F f · hb))
    : disp_2cells (lunitor f) (@id_disp C disp_alg_1_id_comp_cells a ha;; ff) ff.
  Proof.
    cbn.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    rewrite rwhisker_hcomp.
    rewrite <- triangle_r.
    rewrite <- lwhisker_hcomp.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    use vcomp_move_L_Mp. Locate vcomp_move_L_Mp.
    { is_iso.
      refine (pseudofunctor_is_iso _ (lunitor f,,_)).
      is_iso.
    }
    cbn.
    rewrite pseudofunctor_linvunitor.
    rewrite !vassocl.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    apply (maponpaths (λ z, z • _)).
    rewrite !vassocl.
    rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
    use vcomp_move_L_pM.
    { is_iso. }
    cbn. 
    rewrite !vassocr.
    assert (((lunitor ha ▹ f) • ff) • (linvunitor (# F f) ▹ hb)
            =
            rassociator _ _ _ • (_ ◃ ff) • lassociator _ _ _) as p.
    {
      use vcomp_move_R_Mp.
      { is_iso. }
      use vcomp_move_R_pM.
      { is_iso. }
      cbn.
      rewrite !vassocr.
      rewrite <- linvunitor_assoc.
      rewrite !vassocl.
      rewrite <- lunitor_assoc.
      rewrite lwhisker_hcomp.
      rewrite lunitor_natural.
      rewrite !vassocr.
      rewrite linvunitor_lunitor.
      rewrite id2_left.
      reflexivity.
    }
    etrans.
    { exact (maponpaths_2 _ p _). }
    clear p.
    rewrite !vassocl.
    rewrite rwhisker_rwhisker.
    rewrite !vassocr.
    apply (maponpaths (λ z, z • _)).
    rewrite rwhisker_rwhisker_alt.
    rewrite !vassocl.
    apply maponpaths.
    exact (!vcomp_whisker _ _).
  Qed.

  Definition disp_alg_runitor_help
             {a b : C}
             (f : a --> b)
             (ha : F a --> a)
             (hb : F b --> b)
             (ff : ha · f ==> # F f · hb)
    : (ha ◃ runitor f) • ff
      =
      (lassociator ha f (identity b))
        • (ff ▹ identity b)
        • rassociator (# F f) hb (identity b)
        • (# F f ◃ runitor hb).
  Proof.
    use vcomp_move_R_pM.
    { is_iso. }
    cbn.
    rewrite !vassocl.
    rewrite runitor_triangle.
    rewrite !vassocr.
    rewrite rinvunitor_triangle.
    rewrite rwhisker_hcomp.
    rewrite <- rinvunitor_natural.
    rewrite !vassocl.
    rewrite rinvunitor_runitor.
    apply (!id2_right ff).
  Qed.

  Definition disp_alg_runitor
             {a b : C}
             (f : a --> b)
             (ha : disp_alg_1_id_comp_cells a)
             (hb : F b --> b)
             (ff : ha -->[ f ] hb)
    : disp_2cells (runitor f) (ff;; @id_disp C disp_alg_1_id_comp_cells b hb) ff.
  Proof.
    cbn.
    rewrite disp_alg_runitor_help.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocl.
    apply maponpaths.
    apply maponpaths.
    apply maponpaths.
    rewrite !vassocr.
    use vcomp_move_L_Mp.
    {
      is_iso.
      refine (pseudofunctor_is_iso F (runitor f ,, _)).
      is_iso.
    }
    cbn.
    rewrite !vassocl.
    apply maponpaths.
    rewrite pseudofunctor_rinvunitor.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    apply (maponpaths (λ z, z • _)).
    rewrite !vassocl.
    rewrite rwhisker_lwhisker.
    rewrite !vassocr.
    apply (maponpaths (λ z, z • _)).
    rewrite lwhisker_hcomp.
    rewrite rwhisker_hcomp.
    apply (!triangle_l_inv _ _).
  Qed.

  Definition disp_alg_lassociator
             {a b c d : C}
             {f : a --> b}
             {g : b --> c}
             {h : c --> d}
             {ha : disp_alg_1_id_comp_cells a}
             {hb : disp_alg_1_id_comp_cells b}
             {hc : disp_alg_1_id_comp_cells c}
             {hd : disp_alg_1_id_comp_cells d}
             (ff : ha -->[ f ] hb)
             (gg : hb -->[ g ] hc)
             (hh : hc -->[ h ] hd)
    : disp_2cells (rassociator f g h)
                  ((ff;; gg)%mor_disp;; hh)
                  (ff;; (gg;; hh)%mor_disp).
  Proof.
    cbn.
    assert ((ha ◃ rassociator f g h) • lassociator ha f (g · h)
            =
            lassociator ha (f · g) h
                        • (lassociator ha f g ▹ h)
                        • rassociator (ha · f) g h) as p.
    {
      use vcomp_move_L_Mp.
      { is_iso. }
      cbn.
      rewrite !vassocl.
      rewrite pentagon.
      rewrite <- !lwhisker_hcomp.
      rewrite <- !rwhisker_hcomp.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite rassociator_lassociator.
      rewrite lwhisker_id2.
      apply maponpaths_2.
      apply id2_left.
    }
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    rewrite p.
    clear p.
    rewrite !vassocl.
    apply maponpaths.
    apply maponpaths.
    rewrite !vassocr.
    rewrite <- rwhisker_rwhisker_alt.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !vassocr.
    use vcomp_move_L_Mp.
    {
      is_iso.
      refine (pseudofunctor_is_iso F (rassociator f g h ,, _)).
      is_iso.
    }
    cbn.
    pose (pseudofunctor_lassociator F f g h) as p.
    rewrite <- lwhisker_vcomp.
    rewrite !vassocl.
    rewrite (maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
    rewrite rwhisker_lwhisker.
    rewrite !vassocl.
    rewrite !rwhisker_vcomp.
    rewrite vassocl in p.
    cbn in p.
    etrans.
    {
      do 5 apply maponpaths.
      exact p.
    }
    clear p.
    rewrite <- !rwhisker_vcomp.
    rewrite !vassocr.
    apply (maponpaths (λ z, z • _)).
    rewrite <- lwhisker_vcomp.
    rewrite !vassocl.
    rewrite !(maponpaths (λ z, _ • (_ • (_ • z))) (vassocr _ _ _)).
    pose (pentagon hd (#F h) (#F g) (#F f)) as p.
    rewrite <- !lwhisker_hcomp in p.
    rewrite <- !rwhisker_hcomp in p.
    rewrite vassocr in p.
    etrans.
    {
      do 3 apply maponpaths.
      apply maponpaths_2.
      exact (!p).
    }
    clear p.
    rewrite <- lwhisker_vcomp.
    use vcomp_move_R_pM.
    { is_iso. }
    use vcomp_move_R_pM.
    { is_iso. }
    rewrite !vassocl.
    use vcomp_move_R_pM.
    { is_iso. }
    cbn.
    assert ((#F f ◃ rassociator hb g h)
              • lassociator (#F f) hb (g · h)
              • lassociator (#F f · hb) g h
              • (rassociator (#F f) hb g ▹ h)
            = lassociator (#F f) (hb · g) h) as p.
    {
      rewrite !vassocl.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite pentagon.
      rewrite <- lwhisker_hcomp.
      rewrite <- rwhisker_hcomp.
      rewrite !vassocl.
      rewrite rwhisker_vcomp.
      rewrite lassociator_rassociator.
      rewrite id2_rwhisker.
      rewrite id2_right.
      rewrite !vassocr.
      rewrite lwhisker_vcomp.
      rewrite rassociator_lassociator.
      rewrite lwhisker_id2.
      apply id2_left.
    }
    rewrite !vassocr.
    refine (!(_ @ !_)).
    {
      do 6 apply maponpaths_2.
      exact p.
    }
    clear p.
    rewrite <- rwhisker_lwhisker.
    rewrite <- !lwhisker_vcomp.
    rewrite !vassocl.
    apply maponpaths.
    rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
    rewrite lwhisker_lwhisker.
    rewrite !vassocl.
    use vcomp_move_R_pM.
    { is_iso. }
    use vcomp_move_R_pM.
    { is_iso. }
    cbn.
    assert ((rassociator (#F f) (#F g) (hc · h))
              • (#F f ◃ lassociator (#F g) hc h)
              • lassociator (#F f) (#F g · hc) h
              • (lassociator (#F f) (#F g) hc ▹ h)
            =
            lassociator (#F f · #F g) hc h) as p.
    {
      rewrite !vassocl.
      rewrite lwhisker_hcomp.
      rewrite rwhisker_hcomp.
      rewrite <- pentagon.
      rewrite !vassocr.
      rewrite rassociator_lassociator.
      apply id2_left.
    }
    rewrite !vassocr.
    refine (!(_ @ !_)).
    {
      do 4 apply maponpaths_2.
      exact p.
    }
    clear p.
    rewrite rwhisker_rwhisker.
    rewrite !vassocl.
    rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
    rewrite lassociator_rassociator.
    rewrite id2_left.
    rewrite rwhisker_rwhisker.
    rewrite !vassocr.
    apply (maponpaths (λ z, z • _)).
    apply (!vcomp_whisker _ _).
  Qed.    
    
  Definition disp_alg_ops : disp_prebicat_ops' disp_alg_1_id_comp_cells.
  Proof.
    repeat split.
    - cbn. intros a b f ha hb ff.
      rewrite lwhisker_id2, id2_left, pseudofunctor_id2, id2_rwhisker, id2_right.
      reflexivity.
    - cbn. intros a b f ha hb ff.
      exact (disp_alg_lunitor f ha hb ff).
    - cbn. intros a b f ha hb ff.
      exact (disp_alg_runitor f ha hb ff).
    - cbn. intros a b f ha hb ff.
      use vcomp_move_R_pM.
      { is_iso. }
      rewrite vassocr.
      use vcomp_move_L_Mp.
      {
        is_iso.
        refine (pseudofunctor_is_iso F (linvunitor f ,, _)).
        is_iso.
      }
      exact (!disp_alg_lunitor f ha hb ff).
    - cbn. intros a b f ha hb ff.      
      use vcomp_move_R_pM.
      { is_iso. }
      rewrite vassocr.
      use vcomp_move_L_Mp.
      {
        is_iso.
        refine (pseudofunctor_is_iso F (rinvunitor f ,, _)).
        is_iso.
      }
      exact (!disp_alg_runitor f ha hb ff).
    - cbn. intros a b c d f g h ha hb hc hd ff gg hh.
      exact (disp_alg_lassociator ff gg hh).
    - cbn. intros a b c d f g h ha hb hc hd ff gg hh.
      use vcomp_move_R_pM.
      { is_iso. }
      rewrite vassocr.
      use vcomp_move_L_Mp.
      {
        is_iso.
        refine (pseudofunctor_is_iso F (lassociator f g h ,, _)).
        is_iso.
      }
      cbn.
      exact (!disp_alg_lassociator ff gg hh).
    - cbn. intros a b f g h θ γ ha hb ff gg hh θθ γγ.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      rewrite γγ.
      rewrite !vassocr.
      rewrite θθ.
      rewrite !vassocl.
      rewrite !rwhisker_vcomp.
      apply maponpaths.
      apply maponpaths.
      exact (!pseudofunctor_vcomp F θ γ).
    - cbn. intros a b c f g h θ ha hb hc ff gg hh θθ.
      rewrite !vassocr.
      rewrite lwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_vcomp.
      refine (!(_ @ !_)).
      {
        do 5 apply maponpaths.
        exact (pseudofunctor_lwhisker F f θ).
      }
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      apply (maponpaths (λ z, z • _)).
      rewrite !vassocl.
      rewrite <- rwhisker_lwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite lwhisker_vcomp.
      refine (!(!_ @ !_)).
      {
        do 3 apply maponpaths.
        exact θθ.
      }
      rewrite <- lwhisker_vcomp.
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      rewrite lwhisker_lwhisker_rassociator.
      rewrite !vassocr.
      apply maponpaths_2.
      apply maponpaths_2.
      exact (!vcomp_whisker ff θ).
    - cbn. intros a b c f g h θ ha hb hc ff gg hh θθ.
      rewrite !vassocr.
      rewrite rwhisker_lwhisker.
      rewrite !vassocl.
      apply maponpaths.
      rewrite rwhisker_vcomp.
      refine (!(_ @ !_)).
      {
        do 5 apply maponpaths.
        exact (pseudofunctor_rwhisker F h θ).
      }
      rewrite <- rwhisker_vcomp.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite rwhisker_rwhisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite !vassocl.
      rewrite <- vcomp_whisker.
      rewrite !vassocr.
      apply maponpaths_2.
      rewrite rwhisker_vcomp.
      etrans.
      {
        apply maponpaths_2.
        apply maponpaths.
        exact θθ.
      }
      rewrite <- rwhisker_vcomp.
      rewrite !vassocl.
      apply maponpaths.
      exact (rwhisker_rwhisker_alt h hb (## F θ)).
  Qed.

  (*
  Definition disp_alg_ops_laws : disp_prebicat_laws (_ ,, disp_alg_ops).
  Proof.
    repeat split; intro; intros; apply isapropunit.
  Qed.

  Definition disp_alg_prebicat : disp_prebicat C
    := (_ ,, disp_alg_ops_laws).

  Definition prebicat_algebra := total_prebicat disp_alg_prebicat.
*)
End Algebra.
