(** The projection of the total prebicategory of a displayed prebicategory to the base **)
(* Copied from UniMath/Bicategories/PseudoFunctors/Examples/Projection.v *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

(*Require Import Integers.Prebicategories.TypePrebicat.*)
Require Import Integers.Prebicategories.DispPrebicat.
Require Import Integers.Prebicategories.Invertible_2cells.
Require Import Integers.Prebicategories.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.

Section Projection.
  Context {C : prebicat}.
  Variable (D : disp_prebicat C).

  Definition pr1_pseudofunctor_data : pseudofunctor_data (total_prebicat D) C.
  Proof.
    use make_pseudofunctor_data.
    - exact (λ a, pr1 a).
    - exact (λ _ _ f, pr1 f).
    - exact (λ _ _ _ _ θ, pr1 θ).
    - exact (λ a, (id2 (identity (pr1 a)))).
    - exact (λ _ _ _ f g, id2 (pr1 f · pr1 g)).
  Defined.

  Definition pr1_pseudofunctor_laws : pseudofunctor_laws pr1_pseudofunctor_data.
  Proof.
    repeat split.
    - intros a b c f g h θ. cbn.
      refine (_ @ _).
      + apply id2_left.
      + apply (!id2_right _).
    - intros a b c f g h θ. cbn.
      refine (_ @ _).
      + apply id2_left.
      + apply (!id2_right _).
    - intros a b f. cbn.
      refine (!(_ @ _ @ _)).
      + apply maponpaths_2.
        apply maponpaths_2.
        apply id2_rwhisker.
      + apply maponpaths_2.
        apply id2_left.
      + apply id2_left.
    - intros a b f. cbn.
      refine (!(_ @ _ @ _)).
      + apply maponpaths_2.
        apply maponpaths_2.
        apply lwhisker_id2.
      + apply maponpaths_2.
        apply id2_left.
      + apply id2_left.
    - intros a b c d f g h. cbn.
      refine (_ @ _ @ _ @!(_ @ _ @ _)).
      + apply maponpaths_2.
        apply maponpaths_2.
        apply lwhisker_id2.
      + apply maponpaths_2.
        apply id2_left.
      + apply id2_left.
      + apply maponpaths_2.
        apply maponpaths.
        apply id2_rwhisker.
      + apply id2_right.
      + apply id2_right.
  Qed.
  
  Definition pr1_pseudofunctor : pseudofunctor (total_prebicat D) C.
  Proof.
    use make_pseudofunctor.
    - exact pr1_pseudofunctor_data.
    - exact pr1_pseudofunctor_laws.
    - split.
      + intro a. cbn.
        is_iso.
      + intros a b c f g. cbn.
        is_iso.
  Defined.
  
End Projection.
