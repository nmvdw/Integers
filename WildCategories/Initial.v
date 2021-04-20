(** 
 - Initial objects in wild categories
 - Initial objects are equivalent
**)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.

Require Import Integers.WildCategories.WildCat.

Local Open Scope cat.

(** Initial objects **)
Section Initial.
  Context {C : wild_cat}
          (i : C).

  Definition initial_exists (c : C) : UU := i --> c.

  Definition initial_unique {c : C} (α β : i --> c) : UU := α ==> β.

  Definition is_initial : UU
    := (∏ (c : C), initial_exists c)
         × ∏ {c : C} (α β : i --> c), initial_unique α β.
End Initial.

Definition initial_object (C : wild_cat) : UU
  := ∑ (i : C), is_initial i.

Coercion object_from_initial_object
           {C : wild_cat}
           (i : initial_object C)
  : C
  := pr1 i.

Definition initial_mor
           {C : wild_cat}
           (i : initial_object C)
           (c : C)
  : i --> c
  := pr12 i c.

Definition initial_2cell
           {C : wild_cat}
           {i : initial_object C}
           {c : C}
           (α β : i --> c)
  : α ==> β
  := pr22 i c α β.

Definition build_initial_object
           {C : wild_cat}
           (i : C)
           (hf : ∏ c, i --> c)
           (hθ : ∏ (c : C) (α β : i --> c), α ==> β)
  : initial_object C
  := i ,, hf ,, hθ.

(** Initial objects are equivalent **)
Lemma initial_objects_equivalent
      {C : wild_cat}
      (i j : initial_object C)
  : are_equivalent i j.
Proof.
  exact (initial_mor i j,, initial_mor j i,, initial_2cell _ _,, initial_2cell _ _).
Qed.
