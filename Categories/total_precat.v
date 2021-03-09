(* 
 - Total precategories.
 - The projection functor from the total precategory to its base.
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Core.Functors. 

Require Import Integers.Categories.disp_precat.

Local Open Scope cat.

Local Open Scope mor_disp.


(** Total precategories **)
(* From 'UniMath/Categories/DisplayedCats/Core.v' *)
Definition total_precategory_ob_mor {C : precategory_data} (D : disp_cat_data C)
: precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact (∑ x:C, D x).
  - intros xx yy.
    exact (∑ (f : pr1 xx --> pr1 yy), pr2 xx -->[f] pr2 yy).
Defined.

Definition total_precategory_id_comp {C : precategory_data} (D : disp_cat_data C)
  : precategory_id_comp (total_category_ob_mor D).
Proof.
  apply tpair.
  - simpl. intros c. exists (identity _). apply id_disp.
  - intros xx yy zz ff gg. simpl.
    exists (pr1 ff · pr1 gg).
    exact (pr2 ff ;; pr2 gg).
Defined.

Definition total_precategory_data {C : precategory_data} (D : disp_cat_data C) : precategory_data.
Proof.
  use make_precategory_data.
  - exact (total_category_ob_mor D).
  - exact (pr1 (total_category_id_comp D)).
  - exact (pr2 (total_category_id_comp D)).
Defined.

Lemma total_precategory_is_precat {C : precategory} (D : disp_precat C) :
  is_precategory (total_precategory_data D).
Proof.
  apply is_precategory_one_assoc_to_two.
  repeat apply tpair; simpl.
  - intros xx yy ff; cbn.
    use total2_paths_f; simpl.
    + apply id_left.
    + eapply pathscomp0.
      * apply maponpaths.
        exact id_left_disp.
      * apply transportfbinv.
  - intros xx yy ff; cbn.
    use total2_paths_f; simpl.
    + apply id_right.
    + eapply pathscomp0.
      * apply maponpaths.
        exact id_right_disp.
      * apply transportfbinv.
  - intros xx yy zz ww ff gg hh.
    use total2_paths_f; simpl.
    + apply assoc.
    + eapply pathscomp0.
      * apply maponpaths.
        exact assoc_disp.
      * apply transportfbinv.
Qed.

Definition total_precategory {C : precategory} (D : disp_precat C) : precategory :=
  total_precategory_data D ,, total_precategory_is_precat D.


(** First projection of total precategory **)
(* From 'UniMath/Categories/DisplayedCats/Core.v' *)
Definition pr1_precat_data {C : precategory} (D : disp_precat C) :
  functor_data (total_precategory D) C.
Proof.
  exists pr1.
  intros a b.
  exact pr1.
Defined.

Lemma pr1_precat_is_functor {C : precategory} (D : disp_precat C) :
  is_functor (pr1_precat_data D).
Proof.
  apply tpair.
  - intro x.
    apply idpath.
  - intros x y z f g.
    apply idpath.
Qed.

Definition pr1_precat {C : precategory} (D : disp_precat C) : functor (total_precategory D) C :=
  make_functor (pr1_precat_data D) (pr1_precat_is_functor D).
