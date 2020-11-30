(* Left adjoints preserve initial objects *)
(* If L : C -> D is left adjoint and i initial in C, then L(i) is initial in D *)


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
Require Import Integers.WildCategories.Initial.
Require Import Integers.WildCategories.Adjunction.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Lemma adjunction_preserves_initial
      {C D : wild_cat}
      (A : adjunction C D)
      (i : initial_object C)
  : initial_object D.
Proof.
  use build_initial_object.
  - exact (adj_left A i).
  - exact (λ d, #(adj_left A) (initial_mor i (adj_right A d)) · (adj_counit A d)).
  - intros d α β.
    pose (initial_2cell
             (adj_unit A i · #(adj_right A) α)
             (adj_unit A i · #(adj_right A) β)) as θ.
    exact (linvunitor α
           • ((adj_tL A i)^-1 ▹ α)
           • rassociator _ _ _
           • (#(adj_left A) (adj_unit A i) ◃ $(adj_counit A) α)
           • lassociator _ _ _
           • (wild_functor_comp (adj_left A) _ _ ▹ adj_counit A d)
           • (##(adj_left A) θ ▹ adj_counit A d)
           • ((wild_functor_comp (adj_left A) _ _)^-1 ▹ adj_counit A d)
           • rassociator _ _ _
           • (#(adj_left A) (adj_unit A i) ◃ ($(adj_counit A) β)^-1)
           • lassociator _ _ _
           • (adj_tL A i ▹ β)
           • lunitor β).
Qed.
