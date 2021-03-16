(*
 - Definition of wild categories
 - Some lemmas for invertible 2-cells
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Notations.

Local Open Scope cat.

(** Definition of wild category **)
(* They are just the data for prebicategories *)
Notation wild_cat_2cell_struct := prebicat_2cell_struct.
Notation wild_cat_1_id_comp_cells := prebicat_1_id_comp_cells.
Notation wild_cat_cells := prebicat_cells.
Notation wild_cat_2_id_comp_struct := prebicat_2_id_comp_struct.
Notation wild_cat := prebicat_data.
Notation make_wild_cat := make_prebicat_data.
Notation build_wild_cat := build_prebicat_data.

(** Lemmas for invertible 2-cells **)
Definition is_invertible_2cell {C : wild_cat}
           {a b : C} {f g : a --> b} (θ : f ==> g)
  : UU := g ==> f.

Definition make_is_invertible_2cell {C : wild_cat}
           {a b : C} {f g : a --> b}
           (θ : f ==> g)
           (γ : g ==> f)
  : is_invertible_2cell θ
  := γ.

Definition inv_cell {C : wild_cat} {a b : C} {f g : a --> b} {θ : f ==> g}
  (c : is_invertible_2cell θ) : g ==> f := c.

Notation "inv_θ ^-1" := (inv_cell inv_θ) : bicategory_scope.

Definition is_invertible_2cell_inv {C : prebicat_data} {a b : C} {f g : a --> b}
           {θ : f ==> g} (inv_θ : is_invertible_2cell θ)
  : is_invertible_2cell (inv_θ^-1)
  := make_is_invertible_2cell _ θ.

Definition is_invertible_2cell_id₂ {C : prebicat} {a b : C} (f : a --> b)
  : is_invertible_2cell (id2 f)
  := make_is_invertible_2cell (id2 f) (id2 f).

Definition invertible_2cell {C : wild_cat}
           {a b : C} (f g : a --> b) : UU
  := ∑ θ : f ==> g, is_invertible_2cell θ.

Definition make_invertible_2cell {C : wild_cat}
           {a b : C} {f g : a --> b}
           {θ : f ==> g} (inv_θ : is_invertible_2cell θ)
  : invertible_2cell f g
  := θ,, inv_θ.

Coercion cell_from_invertible_2cell {C : wild_cat}
         {a b : C} {f g : a --> b} (θ : invertible_2cell f g)
  : f ==> g
  := pr1 θ.

Coercion property_from_invertible_2cell {C : wild_cat}
         {a b : C} {f g : a --> b}
         (θ : invertible_2cell f g)
  : is_invertible_2cell θ
  := pr2 θ.

Definition id2_invertible_2cell {C : prebicat} {a b : C} (f : a --> b)
  : invertible_2cell f f
  := make_invertible_2cell (is_invertible_2cell_id₂ f).
