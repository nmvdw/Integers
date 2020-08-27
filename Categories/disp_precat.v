Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.


(**
The scope `cat` allows one to write `x --> y` for the morphisms from `x` to `y`.
In addition, you can write `f · g` for the composition (compositional order).
The identity morphism is denoted by `identity`.
 *)
Local Open Scope cat.

(**
The scope `mor_disp` contains notation for displayed categories.
It introduces the notation `xx -->[ f ] yy` for displayed morphisms over `f` from `xx` to `yy`.
The displayed identity is denoted by `id_disp`.
 *)
Local Open Scope mor_disp.

(**
The precategory `type_precat` has types as objects and functions as morphisms and it is defined already in UniMath.
We will use this category in the remainder of the formalization.
To illustrate the definition of a precategory, we repeat how this category is defined.
 *)
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

(**
Next we look at displayed precategories.
Note that for these, we don't want the displayed morphisms to be a set.
The definition is copied from UniMath (from `disp_cat_axioms`).

Note the type of
- `transportb : ∏ (X : UU) (P : X → UU) (x x' : X), x = x' → P x' → P x`
- `transportf : ∏ (X : UU) (P : X → UU) (x x' : X), x = x' → P x → P x'`
`transportf` corresponds to `transport` in the HoTT book.
`transportb P p x` is an abbreviation for `transportf P (!p) x`.
 *)
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
Direct products of displayed precategories.
Copied from 'DisplayedCats/Constructions.v'
 *)
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
