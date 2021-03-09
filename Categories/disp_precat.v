(*
 - The precategory `TYPE` with types as objects and functions as morphisms.
 - Displayed precategories.
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Local Open Scope cat.
Local Open Scope mor_disp.

(** The precategory of types **)
(* Defined as `type_precat` in 'UniMath/CategoryTheory/categories/Core.v' *)
Definition TYPE_data : precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact Type.
    + exact (λ X Y, X → Y).
  - exact (λ X x, x).
  - exact (λ X Y Z f g x, g(f x)).
Defined.

Definition TYPE_is_precategory
  : is_precategory TYPE_data.
Proof.
  use make_is_precategory.
  - exact (λ X Y f, idpath _).
  - exact (λ X Y f, idpath _).
  - exact (λ W X Y Z f g h, idpath _).
  - exact (λ W X Y Z f g h, idpath _).
Qed.

Definition TYPE : precategory := make_precategory TYPE_data TYPE_is_precategory.

(** Displayed precategories **)
(* From 'UniMath/Categories/DisplayedCats/Core.v' *)
Definition disp_precat_axioms
           {C : precategory}
           (D : disp_cat_data C)
  : UU
:= (∏ x y (f : x --> y) (xx : D x) yy (ff : xx -->[f] yy),
     id_disp _ ;; ff
     =
     transportb _ (id_left _) ff)
   × (∏ x y (f : x --> y) (xx : D x) yy (ff : xx -->[f] yy),
     ff ;; id_disp _
     =
     transportb _ (id_right _) ff)
   × (∏ x y z w f g h (xx : D x) (yy : D y) (zz : D z) (ww : D w)
        (ff : xx -->[f] yy) (gg : yy -->[g] zz) (hh : zz -->[h] ww),
     ff ;; (gg ;; hh)
     =
     transportb _ (assoc _ _ _) ((ff ;; gg) ;; hh)).

Definition disp_precat (C : precategory) : UU
  := ∑ (D : disp_cat_data C), disp_precat_axioms D.

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


(** Direct products of displayed precategories. **)
(* From 'UniMath/Categories/DisplayedCats/Constructions.v' *)
Definition dirprod_disp_precat_axioms {C : precategory} (D1 D2 : disp_precat C)
  : disp_precat_axioms (dirprod_disp_cat_data (pr1 D1) (pr1 D2)).
Proof.
  repeat apply make_dirprod.
  - intros.
    apply dirprod_paths; use (id_left_disp @ !_).
    + apply pr1_transportf.
    + apply pr2_transportf.
  - intros.
    apply dirprod_paths; use (id_right_disp @ !_).
    + apply pr1_transportf.
    + apply pr2_transportf.
  - intros. apply dirprod_paths; use (assoc_disp @ !_).
    + use pr1_transportf.
    + apply pr2_transportf.
Qed.

Definition dirprod_disp_precat {C : precategory} (D1 D2 : disp_precat C) : disp_precat C := dirprod_disp_cat_data D1 D2 ,, dirprod_disp_precat_axioms D1 D2.
