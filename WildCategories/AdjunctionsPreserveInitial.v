(* 
 - Adjunctions preserve initial objects
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.

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

(** Adjunctions preserve initial objects **)
Lemma adjunction_preserves_initial
      {C D : wild_cat}
      (A : adjunction C D)
      (i : initial_object C)
  : initial_object D.
Proof.
  use build_initial_object.
  - exact (adj_left A i).
  - exact (λ d, #(adj_left A) (initial_mor i (adj_right A d)) · (adj_counit A d)).
  - intros d f g.
    pose (initial_2cell
             (adj_unit A i · #(adj_right A) f)
             (adj_unit A i · #(adj_right A) g)) as θ.
    exact (linvunitor f
           • ((adj_tL A i)^-1 ▹ f)
           • rassociator _ _ _
           • (#(adj_left A) (adj_unit A i) ◃ $(adj_counit A) f)
           • lassociator _ _ _
           • (wild_functor_comp (adj_left A) _ _ ▹ adj_counit A d)
           • (##(adj_left A) θ ▹ adj_counit A d)
           • ((wild_functor_comp (adj_left A) _ _)^-1 ▹ adj_counit A d)
           • rassociator _ _ _
           • (#(adj_left A) (adj_unit A i) ◃ ($(adj_counit A) g)^-1)
           • lassociator _ _ _
           • (adj_tL A i ▹ g)
           • lunitor g).
Qed.
