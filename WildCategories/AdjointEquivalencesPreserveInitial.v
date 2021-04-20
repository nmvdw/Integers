(* 
 - Adjoint equivalences preserve initial objects
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
Require Import Integers.WildCategories.WildNaturalIsomorphism.
Require Import Integers.WildCategories.Initial.
Require Import Integers.WildCategories.AdjointEquivalence.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(** Adjunctions preserve initial objects **)
Lemma adjunction_preserves_initial
      {C D : wild_cat}
      (A : adjoint_equivalence C D)
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

Lemma adjunction_preserves_initial_inv
      {C D : wild_cat}
      (A : adjoint_equivalence C D)
      (j : initial_object D)
  : initial_object C.
Proof.
  use build_initial_object.
    - exact (adj_right A j).
    - exact (λ c, #(adj_right A) (initial_mor j (adj_left A c))
                   · wild_nat_iso_trans_inv (adj_unit A) c).
    - intros c f g.
      pose (initial_2cell
               (wild_nat_iso_trans_inv (adj_counit A) j · #(adj_left A) f)
               (wild_nat_iso_trans_inv (adj_counit A) j · #(adj_left A) g)) as θ.
      exact (linvunitor f
                        • ((adj_tR_inv A j)^-1 ▹ f)
                        • rassociator _ _ _
                        • (_ ◃ $(wild_nat_iso_trans_inv (adj_unit A)) f)
                        • lassociator _ _ _
                        • (wild_functor_comp (adj_right A) _ _ ▹ _)
                        • (##(adj_right A) θ ▹ _)
                        • ((wild_functor_comp (adj_right A) _ _)^-1 ▹ _)
                        • rassociator _ _ _
                        • (_ ◃ ($(wild_nat_iso_trans_inv (adj_unit A)) g)^-1)
                        • lassociator _ _ _
                        • (adj_tR_inv A j ▹ _)
                        • lunitor g).
Qed.
