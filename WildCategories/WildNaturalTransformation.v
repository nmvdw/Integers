(** Wild Natural Transformations between Wild Functors over Wild Categories **)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.WildCategories.WildCat.
Require Import Integers.WildCategories.DispWildCat.
Require Import Integers.WildCategories.Invertible_2cells.
Require Import Integers.WildCategories.WildFunctor.
Import WildFunctor.Notations.

Local Open Scope cat.
Local Open Scope mor_disp_scope.


Definition wild_nat_trans {C D : wild_cat} (F G : wild_functor C D) : UU.
Proof.
  use total2.
  - exact (∏ a : C, F a --> G a).
  - intro η₀.
    exact (∏ {a b : C} (f : a --> b), invertible_2cell (η₀ a · #G f) (#F f · η₀ b)).
Defined.

Definition make_wild_nat_trans
           {C D : wild_cat}
           {F G : wild_functor C D}
           (η₀ : ∏ a : C, F a --> G a)
           (η₁ : ∏ {a b : C} (f : a --> b), invertible_2cell (η₀ a · #G f) (#F f · η₀ b))
  : wild_nat_trans F G.
Proof.
  exact (η₀ ,, η₁).
Defined.

(* Data projections *)
Definition wild_nat_trans_objects
           {C D : wild_cat}
           {F G : wild_functor C D}
           (η : wild_nat_trans F G)
           (a : C)
  : F a --> G a
  := pr1 η a.

Coercion wild_nat_trans_objects : wild_nat_trans >-> Funclass.

Definition wild_nat_trans_morphisms
           {C D : wild_cat}
           {F G : wild_functor C D}
           (η : wild_nat_trans F G)
           {a b : C}
           (f : a --> b)
  : invertible_2cell (η a · #G f) (#F f · η b)
  := pr2 η a b f.

Local Notation "'#'" := wild_nat_trans_morphisms.

(* Examples *)
