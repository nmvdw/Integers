Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.Type.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import Integers.disp_precat.
Require Import Integers.total_precat.
Require Import Integers.point_constructors.

Local Open Scope cat.

Local Open Scope mor_disp.


(** ℤh **)
(**
Precategory with an added point and two endomorphisms
  *)
Definition disp2 : disp_precat type_precat.
Proof.
  apply dirprod_disp_precat.
  - exact disp_point_end.
  - exact disp_end.
Defined.

Definition TYPE2 : precategory := total_precategory disp2.

(** WIP
Adding the first coherency
 *)
(* morfismen in _end zijn omgedraaid, maar nog niet hier *)

(*
Definition disp_sec_h_data : disp_cat_data TYPE2.
Proof.
  use tpair.
  - use make_disp_cat_ob_mor.
    + cbn.
      intro XX.
      exact (∏ z : (pr1 XX), pr22 XX (pr212 XX z) = z).
    + cbn.
      intros XX YY ε η ff.
      exact (∏ z : (pr1 XX), η (pr1 ff z) = ((maponpaths (pr22 YY) (!(pr212 ff z))) @ (!(pr22 ff (pr212 XX z))) @ (maponpaths (pr1 ff) (ε z)))).
  - split.
    + cbn. intros XX ε z.
      unfold idfun.
      refine (!_).
      exact (maponpathsidfun (ε z)).
    + cbn. intros XX YY ZZ ff gg ε η θ fff ggg z.
      refine (_ @ _ @ _ @ _ @ !(!_ @ _ @ _ @ _)).
      * apply ggg.
      * apply maponpaths.
        apply maponpaths.
        apply maponpaths.
        exact (fff z).
      * apply maponpaths.
        apply maponpaths.
        apply maponpathscomp0.
      * apply maponpaths.
        apply maponpaths.
        apply maponpaths.
        apply maponpathscomp0.
      * apply maponpaths.
        apply maponpaths.
        (* apply maponpathscomp. *)

        Abort.
*)
