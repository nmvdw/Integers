Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.Core.Functors. 

Require Import Integers.Categories.disp_precat.

Local Open Scope cat.

Local Open Scope mor_disp.


(**
Some more auxiliary definitions for displayed precategories.
Copied from 'DisplayedCats/Core.v', but adapted to work with our definition of categories with non-set homs. *)
Definition disp_cat_data_from_disp_precat {C} (D : disp_precat C)
  := pr1 D : disp_cat_data C.
Coercion disp_cat_data_from_disp_precat : disp_precat >-> disp_cat_data.

Definition id_left_disp {C} {D : disp_precat C}
  {x y} {f : x --> y} {xx : D x} {yy} {ff : xx -->[f] yy}
: id_disp _ ;; ff = transportb _ (id_left _) ff
:= pr1 (pr2 D) _ _ _ _ _ _.


Definition id_right_disp {C} {D : disp_precat C}
  {x y} {f : x --> y} {xx : D x} {yy} {ff : xx -->[f] yy}
  : ff ;; id_disp _ = transportb _ (id_right _) ff
:= pr1 (pr2 (pr2 D)) _ _ _ _ _ _.

Definition assoc_disp {C} {D : disp_precat C}
  {x y z w} {f} {g} {h} {xx : D x} {yy : D y} {zz : D z} {ww : D w}
  {ff : xx -->[f] yy} {gg : yy -->[g] zz} {hh : zz -->[h] ww}
: ff ;; (gg ;; hh) = transportb _ (assoc _ _ _) ((ff ;; gg) ;; hh)
 := pr2 (pr2 (pr2 D)) _ _ _ _ _ _ _ _ _ _ _ _ _ _.

(**
Definitions of total precategories, again taken from the definition of total categories of 'DisplayedCats/Core.v' and adapted.
 *)
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
(* Copied from Disp/Core *)
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
