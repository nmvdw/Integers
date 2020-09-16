(* Copy of some lemmas UniMath.Bicategories.Core.Bicat.v *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Local Open Scope bicategory_scope.
Local Open Scope cat.

Lemma inv_cell_eq {C : prebicat} {a b : C} {f g : C ⟦a, b⟧} (x y : f ==> g)
      (inv_x : is_invertible_2cell x) (inv_y : is_invertible_2cell y)
      (p : inv_x^-1 = inv_y^-1)
  : x = y.
Proof.
  apply (vcomp_rcancel _ (is_invertible_2cell_inv inv_x)).
  rewrite vcomp_rinv, p.
  apply (!vcomp_rinv _).
Defined.
