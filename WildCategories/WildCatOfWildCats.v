(** The Wild Category of Wild Categories, Wild Functors and Wild Natural Transformations **)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import sem.signature.hit_signature.

Require Import Integers.WildCategories.WildCat.
Require Import Integers.WildCategories.DispWildCat.
Require Import Integers.WildCategories.WildFunctor.
Import WildFunctor.Notations.
Require Import Integers.WildCategories.WildNaturalTransformation.
Import WildNaturalTransformation.Notations.

Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.


Definition wild_cat_of_wild_cats : wild_cat.
Proof.
  use build_wild_cat.
  - exact wild_cat.
  - exact (λ C D, wild_functor C D).
  - exact (λ C D F G, wild_nat_trans F G).
  - exact (λ C, id_wild_functor C).
  - exact (λ C D E F G, F ⋯ G).
  - exact (λ C D F, id_wild_nat_trans F).
  - exact (λ C D F G H η γ, comp_wild_nat_trans η γ).
  - exact (λ C D E F G H η, lwhisker_wild_nat_trans F η).
  - exact (λ C D E F G H η, rwhisker_wild_nat_trans η H).
  - exact (λ C D F, lunitor_wild_nat_trans F).
  - exact (λ C D F, linvunitor_wild_nat_trans F).
  - exact (λ C D F, runitor_wild_nat_trans F).
  - exact (λ C D F, rinvunitor_wild_nat_trans F).
  - exact (λ C D E B F G H, lassociator_wild_nat_trans F G H).
  - exact (λ C D E B F G H, rassociator_wild_nat_trans F G H).
Defined.
