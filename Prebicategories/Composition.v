(** Compositions of pseudofunctors over precategories **)
(* Copied from UniMath/Bicategories/PseudoFunctors/Examples/Composition.v *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

(*Require Import Integers.Prebicategories.TypePrebicat.
Require Import Integers.Prebicategories.DispPrebicat.*)
Require Import Integers.Prebicategories.Invertible_2cells.
Require Import Integers.Prebicategories.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.

Section FunctorComposition.
  Context {C D E : prebicat}.
  Variable (G : pseudofunctor D E) (F : pseudofunctor C D).

  Definition comp_pseudofunctor_data : pseudofunctor_data C E.
  Proof.
    use make_pseudofunctor_data.
    - exact (λ a, G (F a)).
    - exact (λ _ _ f, #G (#F f)).
    - exact (λ _ _ _ _ θ, ##G (##F θ)).
    - exact (λ a, pseudofunctor_id G (F a) • ##G (pseudofunctor_id F a)).
    - exact (λ _ _ _ f g, pseudofunctor_comp G (#F f) (#F g) • ##G (pseudofunctor_comp F f g)).
  Defined.

  Definition comp_is_pseudofunctor : pseudofunctor_laws comp_pseudofunctor_data.
  Proof.
    repeat split.
    - intros a b f. cbn.
      refine (_ @ _).
      + apply maponpaths.
        apply pseudofunctor_id2.
      + apply pseudofunctor_id2.
    - intros a b f g h θ γ. cbn.
      refine (_ @ _).
      + apply maponpaths.
        apply pseudofunctor_vcomp.
      + apply pseudofunctor_vcomp.
    - intros a b c f g h θ. cbn.
      refine (_ @ _ @ _ @!(_ @ _ @ _ @ _)).
      + apply vassocl.
      + apply maponpaths.
        apply (!pseudofunctor_vcomp _ _ _).
      + apply maponpaths.
        apply maponpaths.
        apply pseudofunctor_lwhisker.
      + apply vassocr.
      + apply maponpaths_2.
        apply (!pseudofunctor_lwhisker _ _ _).
      + apply (!vassocr _ _ _).
      + apply maponpaths.
        apply (!pseudofunctor_vcomp G _ _).
    - intros a b c f g h θ. cbn.
      refine (_ @ _ @ _ @!(_ @ _ @ _ @ _)).
      + apply vassocl.
      + apply maponpaths.
        apply (!pseudofunctor_vcomp _ _ _).
      + apply maponpaths.
        apply maponpaths.
        apply pseudofunctor_rwhisker.
      + apply vassocr.
      + apply maponpaths_2.
        apply (!pseudofunctor_rwhisker _ _ _).
      + apply (!vassocr _ _ _).
      + apply maponpaths.
        apply (!pseudofunctor_vcomp G _ _).
    - intros a b f. cbn.
      refine (_ @ _ @ _).
      + apply pseudofunctor_lunitor.
      + apply maponpaths.
        apply maponpaths.
        apply pseudofunctor_lunitor.
      + rewrite <- rwhisker_vcomp.
        rewrite !vassocr.
        rewrite !pseudofunctor_vcomp.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        refine (!(_)).
        * apply maponpaths_2.
          apply maponpaths_2.
          apply (!pseudofunctor_rwhisker _ _ _).
    - intros a b f. cbn.
      refine (_ @ _ @ _).
      + apply pseudofunctor_runitor.
      + apply maponpaths.
        apply maponpaths.
        apply pseudofunctor_runitor.
      + rewrite <- lwhisker_vcomp.
        rewrite !pseudofunctor_vcomp.
        rewrite !vassocl.
        apply maponpaths.
        rewrite !vassocr.
        refine (!_).
        * apply maponpaths_2.
          apply maponpaths_2.
          apply (!pseudofunctor_lwhisker _ _ _).
    - intros a b c d f g h. cbn.
      rewrite <- !lwhisker_vcomp.
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        apply maponpaths.
        apply maponpaths.
        apply (!pseudofunctor_vcomp _ _ _).
      }
      rewrite !(maponpaths (λ z, _ • z) (vassocr _ _ _)).
      etrans.
      {
        apply maponpaths.
        apply maponpaths_2.
        apply (!pseudofunctor_lwhisker _ _ _).
      }
      rewrite !vassocl.
      etrans.
      {
        apply maponpaths.
        apply maponpaths.
        apply (!pseudofunctor_vcomp _ _ _).
      }
      rewrite !vassocr.
      etrans.
      {
        apply maponpaths.
        apply maponpaths.
        apply pseudofunctor_lassociator.
      }
      rewrite !pseudofunctor_vcomp.
      rewrite !vassocl.
      rewrite !vassocr.
      apply (maponpaths (λ z, z • _)).
      etrans.
      {
        apply maponpaths_2.
        apply pseudofunctor_lassociator.
      }
      rewrite !vassocl.
      apply (maponpaths (λ z, _ • z)).
      etrans.
      {
        apply maponpaths.
        apply pseudofunctor_rwhisker.
      }
      rewrite <- !rwhisker_vcomp.
      apply vassocr.
  Qed.

  Definition comp_pseudofunctor : pseudofunctor C E.
  Proof.
    use make_pseudofunctor.
    - exact comp_pseudofunctor_data.
    - exact comp_is_pseudofunctor.
    - split.
      + intro a. cbn.
        is_iso.
        * exact (pseudofunctor_id G (F a)).
        * exact (pseudofunctor_is_iso G (pseudofunctor_id F a)).
      + intros a b c f g. cbn.
        is_iso.
        * exact (pseudofunctor_comp G (#F f) (#F g)).
        * exact (pseudofunctor_is_iso G (pseudofunctor_comp F f g)).
  Defined.

  Definition comp_pseudofunctor_cell
             {a b : C}
             {f g : a --> b}
             (θ : f ==> g)
    : ## comp_pseudofunctor θ = ## G (## F θ).
  Proof.
    apply idpath.
  Qed.

  Definition comp_pseudofunctor_psfunctor_id
             (a : C)
    : pr1 (pseudofunctor_id comp_pseudofunctor a)
      =
      pseudofunctor_id G (F a) • ##G (pseudofunctor_id F a).
  Proof.
    apply idpath.
  Qed.

  Definition comp_pseudofunctor_pseudofunctor_comp
             {a b c : C}
             (f : a --> b) (g : b --> c)
    : pr1 (pseudofunctor_comp comp_pseudofunctor f g)
      =
      pseudofunctor_comp G (#F f) (#F g) • ##G (pseudofunctor_comp F f g).
  Proof.
    apply idpath.
  Qed.

End FunctorComposition.
