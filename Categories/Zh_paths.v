(*
 - The precategory `TYPE2` of types with a point and two endomorphisms, corresponding with zero, successor and predecessor.
 - An attempt to add the path constructor 'sec' to this. Only the data are added.
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.Type.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import Integers.Categories.disp_precat.
Require Import Integers.Categories.total_precat.
Require Import Integers.Categories.point_constructors.

Local Open Scope cat.
Local Open Scope mor_disp.


(** Precategory with an added point and two endomorphisms *)
Definition disp2 : disp_precat type_precat.
Proof.
  apply dirprod_disp_precat.
  - exact disp_point_end.
  - exact disp_end.
Defined.

Definition TYPE2 : precategory := total_precategory disp2.

(** An attempt to add the type of 'sec' as displayed objects. **)
Definition disp_sec_h_data : disp_cat_data TYPE2.
Proof.
  use tpair.
  - use make_disp_cat_ob_mor.
    + cbn.
      intro XX.
      exact (∏ z : (pr1 XX), pr22 XX (pr212 XX z) = z).
    + cbn.
      intros XX YY ε η ff.
      exact (∏ z : (pr1 XX), pr22 ff (pr212 XX z) @ maponpaths (pr22 YY) ((pr212 ff z)) @ η (pr1 ff z) = maponpaths (pr1 ff) (ε z)).
  - split.
    + cbn. intros XX ε z.
      unfold idfun.
      exact (!maponpathsidfun (ε z)).
    + cbn. intros XX YY ZZ ff gg ε η θ fff ggg z.
      refine (_ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _).
      * apply maponpaths.
        apply maponpaths_2.
        apply maponpathscomp0.
      * apply maponpaths.
        apply maponpaths_2.
        apply maponpaths_2.
        apply (maponpathscomp (pr1 gg)).
      * apply (!path_assoc _ _ _).
      * apply maponpaths.
        apply maponpaths.
        apply (!path_assoc _ _ _).
      * apply maponpaths.
        apply path_assoc.
      * apply maponpaths.
        apply maponpaths_2.
        exact (!homotsec_natural (pr22 gg) (pr212 ff z)).
      * apply maponpaths.
        apply (!path_assoc _ _ _).
      * apply maponpaths.
        apply maponpaths.
        exact (ggg (pr1 ff z)).
      * apply maponpaths.
        apply maponpaths_2.
        apply (!maponpathscomp _ _ _).
      * apply maponpaths.
        apply (!maponpathscomp0 (pr1 gg) _ _).
      * apply (!maponpathscomp0 (pr1 gg) _ _).
      * apply maponpaths.
        exact (fff z).
      * apply (maponpathscomp (pr1 ff)).
Defined.
