(** Adding adjunctions **)
(* An adjunction are:
 functors  L : C -> D                R : D -> C
 nat_trans ε : R ⋯ L ==> id_D       η : id_C ==> L ⋯ R
 2-cell    tR : η₀(R₀(a)) · R₁(ε₀(a)) ==> id₁(R₀(a))  for a : D
           tL : L₁(η₀(a)) · ε₀(L₀(a)) ==> id₁(L₀(a))  for a : C *)


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
Require Import Integers.WildCategories.WildNaturalTransformation.
Import WildNaturalTransformation.Notations.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Definition adjunction
           {C D : wild_cat}
           (L : wild_functor C D)
           (R : wild_functor D C)
  : UU.
Proof.
  use total2.
  - exact (wild_nat_trans (R ⋯ L) (id_wild_functor D) × wild_nat_trans (id_wild_functor C) (L ⋯ R)).
  - intro units.
    destruct units as [ε η].
    exact (∏ (a : D), η (R a) · #R (ε a) ==> id₁ (R a)
                        ×
                        ∏ (a : C), #L (η a) · ε (L a) ==> id₁ (L a)).
Defined.
