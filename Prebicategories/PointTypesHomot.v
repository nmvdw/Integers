(** Displayed prebicategory over the prebicategory `type_prebicat` of types with ~ as 2-cells, adding points **)
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

Definition pointtypes_homot_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells type_prebicat.
Proof.
  use tpair.
  - use tpair.
    + (** Objects and 1-cells **)
      use tpair.
      * intro X.
        exact X.
      * intros X Y x y f.
        exact (f x = y).
    + use tpair.
      * cbn.
        intros X x.
        exact (idpath x).
      * cbn.
        intros X Y Z f g x y z ff gg.
        exact (maponpaths g ff @ gg).
  - unfold disp_2cell_struct.
    cbn.
    intros X Y f g θ x y ff gg.
    exact (ff = θ x @ gg).
Defined.

Definition pointtypes_homot_disp_prebicat_ops
           : disp_prebicat_ops' pointtypes_homot_disp_prebicat_1_id_comp_cells.
Proof.
  repeat split; cbn.
  - intros X Y f x y ff.
    refine (_ @ _).
    + apply maponpaths_2.
      exact (maponpathsidfun _).
    + exact (pathscomp0rid _).
  - intros X Y f x y ff.
    refine (!(_ @ _)).
    + apply maponpaths_2.
      exact (maponpathsidfun _).
    + exact (pathscomp0rid _).
  - intros X Y Z W f g h x y z w ff gg hh.
    refine (_ @ _ @ _).
    + apply maponpaths_2.
      apply maponpathscomp0.
    + apply (!path_assoc _ _ _).
    + apply maponpaths_2.
      apply maponpathscomp.
  - intros X Y Z W f g h x y z w ff gg hh.
    refine (!(_ @ _ @ _)).
    + apply maponpaths_2.
      apply maponpathscomp0.
    + apply (!path_assoc _ _ _).
    + apply maponpaths_2.
      apply maponpathscomp.
  - intros X Y f g h θ γ x y ff gg hh θθ γγ.
    unfold homotcomp.
    refine (_ @ _ @ !_).
    + exact θθ.
    + apply maponpaths.
      exact γγ.
    + apply (!path_assoc _ _ _).
  - intros X Y Z f g h θ x y z ff gg hh θθ.
    unfold funhomotsec.
    refine (_ @ _ @ _ @ _).
    + apply maponpaths.
      exact θθ.
    + apply path_assoc.
    + apply maponpaths_2.
      apply homotsec_natural.
    + apply (!path_assoc _ _ _).
  - intros X Y Z f g h θ x y z ff gg hh θθ.
    unfold homotfun.
    refine (_ @ _ @ _).
    + apply maponpaths_2.
      apply maponpaths.
      exact θθ.
    + apply maponpaths_2.
      apply maponpathscomp0.
    + apply (!path_assoc _ _ _).
Defined.


Definition pointtypes_homot_prebicat : disp_prebicat type_prebicat.
Proof.
  use tpair.
  - exists pointtypes_homot_disp_prebicat_1_id_comp_cells.
    apply pointtypes_homot_disp_prebicat_ops.
  - repeat split; repeat intro. (*; cbn in *.*)
    + cbn in x, y, ff, gg, ηη |- *.
      unfold homotrefl, homotsec.        
      refine (_ @ _ @ !(_)).
      * apply pathscomp0rid.
      * unfold pathscomp0.
        cbn.
        apply maponpathsidfun.
      *(* Check (ff = η x @ gg).
        Check (@functtransportb (∏ x0 : a, f x0 = g x0) UU (λ α, ff = α x @ gg) (λ A, A) η η (id2_left η) ηη).*)
        unfold transportb.

        
        (** voor _ hebben we een functie nodig die aan elke θ een θθ toekent **)
        Abort.
(*        apply apd.
        Check (id2_left η).

        apply (@functtransportb (∏ x0 : a, f x0 = g x0) UU (λ α, ff = α x @ gg) (λ A, A) η η (id2_left η) ηη).
      * apply transportb_const.
      *)
