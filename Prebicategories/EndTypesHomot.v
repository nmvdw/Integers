(** Displayed prebicategory over the prebicategory `type_prebicat` of types with ~ as 2-cells, adding endomorphisms **)
(* does not work *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Require Import Integers.Prebicategories.TypePrebicat.
Require Import Integers.Prebicategories.DispPrebicat.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.

Definition endtypes_homot_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells type_prebicat.
Proof.
  use tpair.
  - use tpair.
    + (** Objects and 1-cells **)
      use tpair.
      * intro X.
        exact (X → X).
      * intros X Y s r f.
        exact (∏ x, f (s x) = r (f x)).
    + use tpair.
      * cbn.
        intros X s x.
        exact (idpath (s x)).
      * cbn.
        intros X Y Z f g s r t p q x.
        exact (maponpaths g (p x) @ q (f x)).
  - unfold disp_2cell_struct.
    cbn.
    intros X Y f g θ s r p q.
    exact (∏ x, p x @ maponpaths r (θ x) = θ (s x) @ q x).
Defined.

Definition endtypes_homot_disp_prebicat_ops
  : disp_prebicat_ops' endtypes_homot_disp_prebicat_1_id_comp_cells.
Proof.
  repeat split; cbn.
  - intros X Y f s r p x.
    exact (pathscomp0rid _).
  - intros X Y f s r p x.
    exact (pathscomp0rid _).
  - intros X Y f s r p x.
    refine (_ @ _ @ _).
    + apply maponpaths_2.
      apply maponpaths_2.
      exact (maponpathsidfun _).
    + exact (pathscomp0rid _).
    + exact (pathscomp0rid _).
  - intros X Y f s r p x.
    exact (pathscomp0rid _).
  - intros X Y f s r p x.
    apply maponpaths_2.
    exact (!maponpathsidfun _).
  - intros X Y Z W f g h r s t w p q u x.
    refine (_ @ _ @ !(_ @ _)).
    + apply maponpaths_2.
      apply maponpaths_2.
      apply maponpathscomp0.
    + apply pathscomp0rid.
    + apply maponpaths_2.
      apply (!maponpathscomp _ _ _).
    + apply path_assoc.
  - intros X Y Z W f g h r s t w p q u x.
    refine (_ @ _ @ !(_ @ _)).
    + apply pathscomp0rid.
    + apply maponpaths_2.
      apply (!maponpathscomp _ _ _).
    + apply maponpaths_2.
      apply maponpathscomp0.
    + apply (!path_assoc _ _ _).
  - intros X Y f g h θ γ s r p q u θθ γγ x.
    unfold homotcomp.
    refine (_ @ _ @ _ @ _ @ _ @ _).
    + apply maponpaths.
      apply maponpathscomp0.
    + apply path_assoc.
    + apply maponpaths_2.
      apply θθ.
    + apply (!path_assoc _ _ _).
    + apply maponpaths.
      apply γγ.
    + apply path_assoc.
  - intros X Y Z f g h θ s r t p q u θθ x.
    unfold funhomotsec.
    refine (_ @ _ @ _ @ _ @ _).
    + apply (!path_assoc _ _ _).
    + apply maponpaths.
      apply θθ.
    + apply path_assoc.      
    + apply maponpaths_2.
      apply homotsec_natural.
    + apply (!path_assoc _ _ _).
  - intros X Y Z f g h θ s r t p q u θθ x.
    unfold homotfun.
    refine (_ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _).
    + apply (!path_assoc _ _ _).
    + apply maponpaths.
      apply maponpaths.
      apply maponpathscomp.
    + apply maponpaths.
      apply (!homotsec_natural u _).
    + apply path_assoc.
    + apply maponpaths_2.
      apply maponpaths.
      apply (!maponpathscomp _ _ _).
    + apply maponpaths_2.
      apply (!maponpathscomp0 _ _ _).
    + apply maponpaths_2.
      apply maponpaths.
      apply θθ.
    + apply maponpaths_2.
      apply maponpathscomp0.
    + apply (!path_assoc _ _ _).
Defined.

Definition endtypes_homot_prebicat : disp_prebicat type_prebicat.
Proof.
  use tpair.
  - exists endtypes_homot_disp_prebicat_1_id_comp_cells.
    apply endtypes_homot_disp_prebicat_ops.
  - repeat split; repeat intro.
    * cbn in ηη.
Abort.
