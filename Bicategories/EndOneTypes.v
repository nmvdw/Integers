(** Unfinished: Displayed bicategory that adds endomorphisms to the bicategory of one-types **)
(* Compare with UniMath/Bicategories/DisplayedBicats/Examples/PointedOneTypes.v *)

(** todo: het zo maken dat het op DisplayedBicats/Examples/PointedOneTypes.v lijkt **)
(** todo: afmaken als we het nodig hebben **)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.
Local Open Scope bicategory_scope.

Definition e1types_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells one_types.
Proof.
  use tpair.
  - use tpair.
    + (** Objects and 1-cells **)
      use tpair.
      * (** Objects over a one type X are endomorphisms X → X **)
        exact (λ X, pr1 X → pr1 X).
      * (** 1-cells over f are properties: f preserves endomorphisms **)
        intros  X Y s r f.
        exact (∏ x, f (s x) = r (f x)).
    + (** Identity and composition **)
      use tpair.
      * simpl.
        intros X s x.
        exact (idpath _).
      * simpl.
        intros X Y Z f g s r t p q x.
        exact (maponpaths g (p x) @ q (f x)).
  - simpl. unfold disp_2cell_struct. simpl.
    intros X Y f g θ s r p q.
    exact (∏ x, p x @ maponpaths r (θ x) = θ (s x) @ q x).
Defined.


Definition e1types_disp_prebicat_ops
  : disp_prebicat_ops e1types_disp_prebicat_1_id_comp_cells.
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

(* .... *)
