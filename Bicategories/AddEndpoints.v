(* Adding endpoints using a prebicategory C *)
(* Conform 'Bicategories in Univalent Foundations', Definition 9.12 using prebicategories, or 'Constructing Higher ...', Example 2.11, using prebicategories and T=Id. *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
(*Require Import UniMath.CategoryTheory.DisplayedCats.Core.*)
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.Bicategories.TypePrebicat.
Require Import Integers.Bicategories.DispPrebicat.
Require Import Integers.Bicategories.Invertible_2cells.
Require Import Integers.Bicategories.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import Integers.Bicategories.PseudoTransformation.
Require Import Integers.Bicategories.Composition.
Require Import Integers.Bicategories.Projection.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.


(*linvunitor (l Aa) • (id₁ (S (pr1 Aa)) ◃ α)*)

Lemma linvunitor_vcomp {C : prebicat} {a b : C} (f g : a --> b) (θ : f ==> g)
  : linvunitor f • (identity _ ◃ θ) = θ • linvunitor g.
Proof.
  refine (_ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _).
  - apply maponpaths.
    apply (!id2_right (identity a ◃ θ)).
  - apply vassocr.
  - apply maponpaths.
    apply (!lunitor_linvunitor _).
  - apply vassocr.
  - apply maponpaths_2.    
    apply (!vassocr _ _ _).
  - apply maponpaths_2.
    apply maponpaths.
    apply vcomp_lunitor.
  - apply maponpaths_2.
    apply vassocr.
  - apply maponpaths_2.
    apply maponpaths_2.
    apply linvunitor_lunitor.
  - apply maponpaths_2.
    apply id2_left.
Qed.



  
(* the objects over (A, a) are 2-cells. They could also be equalities *)
Section AddEndpoints.
  Context {C : prebicat}.
  Variable (D : disp_prebicat C).

  Variable (S : pseudofunctor C C).
  Variable (l r : pseudotrans (comp_pseudofunctor S (pr1_pseudofunctor D)) (pr1_pseudofunctor D)).

  Definition add_path_endpoints_ob_mor : Core.disp_cat_ob_mor (total_prebicat D).
  Proof.
    use tpair.
    - exact (λ Aa, l Aa ==> r Aa).
    - intros Aa Bb α β ff.
      exact ((α ▹ #(pr1_pseudofunctor D) ff) • pseudonaturality_of r ff
             = (pseudonaturality_of l ff) • (#S (#(pr1_pseudofunctor D) ff) ◃ β)).
  Defined.      

  Definition add_path_endpoints_id_comp
    : Core.disp_cat_id_comp (total_prebicat D) add_path_endpoints_ob_mor.
  Proof.
    split.
    * intros Aa α. simpl. cbn in α.
        refine (_ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @_ @ !(_ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @_)).
        -- apply maponpaths.
           apply (pseudotrans_id_alt r Aa).
        -- cbn.
           apply maponpaths.
           apply maponpaths.
           apply maponpaths.
           apply maponpaths.
           apply pseudofunctor_id2.
        -- apply maponpaths.
           apply maponpaths.
           apply maponpaths.
           apply id2_right.
        -- apply maponpaths.
           apply maponpaths_2.
           apply maponpaths_2.
           apply maponpaths_2.
           apply lwhisker_id2.
        -- apply maponpaths.
           apply maponpaths_2.
           apply maponpaths_2.
           apply id2_left.
        -- apply vassocr.
        -- apply maponpaths_2.
           apply vassocr.
        -- apply maponpaths_2.
           apply maponpaths_2.
           apply vcomp_runitor.
        -- apply vassocl.
        -- apply vassocl.
           
        -- apply maponpaths_2.
           apply (pseudotrans_id_alt l Aa).
        -- cbn.
           apply maponpaths_2.
           apply maponpaths.        
           apply maponpaths.
           apply maponpaths.
           apply pseudofunctor_id2.
        -- apply maponpaths_2.
           apply maponpaths.
           apply maponpaths.
           apply id2_right.
        -- apply maponpaths_2.
           apply maponpaths_2.
           apply maponpaths_2.
           apply maponpaths_2.
           apply lwhisker_id2.
        -- apply maponpaths_2.
           apply maponpaths_2.
           apply maponpaths_2.
           apply id2_left.
        -- apply vassocl.
        -- apply maponpaths.
           apply vcomp_whisker.
        -- apply vassocl.
        -- apply maponpaths.
           apply vassocr.
        -- apply maponpaths.
           apply maponpaths_2.
           apply linvunitor_vcomp.
        -- apply maponpaths.
           apply (!vassocr _ _ _ ).
      * intros Aa Bb Cc ff gg. cbn. intros α β γ ε θ.
        pose (pseudotrans_comp_alt r ff gg) as pr.
        pose (pseudotrans_comp_alt l ff gg) as pl.
        cbn in pr, pl; rewrite pr, pl; clear pr pl.
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
          apply ε.
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
          apply θ.
        }
        apply (!lwhisker_vcomp _ _ _).
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

  Definition add_path_endpoints_prebicat : disp_prebicat (total_prebicat D).
  Proof.
    use tpair.
    - exists add_path_endpoints_1_id_comp_cells.
      exact add_path_endpoints_ops.
    - abstract (repeat split; repeat intro; apply isapropunit).
  Defined.

  Definition add_path_endpoints : prebicat := total_prebicat add_path_endpoints_prebicat.
End AddEndpoints.
