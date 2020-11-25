(** Adding adjunctions **)
(* An adjunction are:
 functors     L : C -> D                R : D -> C
 nat_trans    ε : R ⋯ L ==> id_D       η : id_C ==> L ⋯ R
 inv.2-cell  tR : η₀(R₀(a)) · R₁(ε₀(a)) ==> id₁(R₀(a))  for a : D
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

Definition is_adjunction
           {C D : wild_cat}
           (L : wild_functor C D)
           (R : wild_functor D C)
  : UU.
Proof.
  use total2.
  - exact (wild_nat_trans (R ⋯ L) (id_wild_functor D) × wild_nat_trans (id_wild_functor C) (L ⋯ R)).
  - intro units.
    destruct units as [ε η].
    exact ((∏ (a : D), invertible_2cell (η (R a) · #R (ε a)) (id₁ (R a)))
             ×
             ∏ (a : C), invertible_2cell (#L (η a) · ε (L a)) (id₁ (L a))).
Defined.

Definition adjunction (C D : wild_cat) : UU
  := ∑ (L : wild_functor C D) (R : wild_functor D C), is_adjunction L R.

Definition make_adjunction
           {C D : wild_cat}
           (L : wild_functor C D)
           (R : wild_functor D C)
           (ε : wild_nat_trans (R ⋯ L) (id_wild_functor D))
           (η : wild_nat_trans (id_wild_functor C) (L ⋯ R))
           (tR : ∏ (a : D), invertible_2cell (η (R a) · #R (ε a)) (id₁ (R a)))
           (tL : ∏ (a : C), invertible_2cell (#L (η a) · ε (L a)) (id₁ (L a)))
  : adjunction C D
  := L ,, R ,, (ε ,, η) ,, tR ,, tL.

Definition adj_left {C D : wild_cat} (A : adjunction C D)
  : wild_functor C D
  := pr1 A.

(*Coercion adj_left : adjunction >-> wild_functor.*)

Definition adj_right {C D : wild_cat} (A : adjunction C D)
  : wild_functor D C
  := pr12 A.

Definition adj_counit {C D : wild_cat} (A : adjunction C D)
  : wild_nat_trans ((adj_right A) ⋯ (adj_left A)) (id_wild_functor D)
  := pr1 (pr122 A).

Definition adj_unit {C D : wild_cat} (A : adjunction C D)
  : wild_nat_trans (id_wild_functor C) ((adj_left A) ⋯ (adj_right A))
  := pr2 (pr122 A).

Definition adj_tR {C D : wild_cat} (A : adjunction C D)
  : ∏ (a : D), invertible_2cell
                 ((adj_unit A) (adj_right A a) · #(adj_right A) (adj_counit A a))
                 (id₁ (adj_right A a))
  := pr1 (pr222 A).

Definition adj_tL {C D : wild_cat} (A : adjunction C D)
  : ∏ (a : C), invertible_2cell
                 (#(adj_left A) (adj_unit A a) · adj_counit A (adj_left A a))
                 (id₁ (adj_left A a))
  := pr2 (pr222 A).

Definition lad
           {C D : wild_cat}
           (A : adjunction C D)
           {a : C} {b : D}
           (g : adj_left A a --> b)
  : a --> adj_right A b
  := adj_unit A a · #(adj_right A) g.

Definition rad
           {C D : wild_cat}
           (A : adjunction C D)
           {a : C} {b : D}
           (f : a --> adj_right A b)
  : adj_left A a --> b
  := #(adj_left A) f · adj_counit A b.

Lemma to_rad
      {C D : wild_cat}
      (A : adjunction C D)
      {a : C} {b : D}
      (f : a --> adj_right A b)
      (g : adj_left A a --> b)
  : lad A g ==> f → g ==> rad A f.
Proof.
(*  pose (adj_left A) as L.
  pose (adj_right A) as R.
  pose (adj_counit A) as ε.
  pose (adj_unit A) as η.
  pose (adj_tR A) as tR.
  pose (adj_tL A) as tL.
  intro θ.
  unfold rad.
  refine (linvunitor g • _).
  refine ((tL a)^-1 ▹ g • _).
  refine (rassociator _ _ _ • _).
  refine (#L (η a) ◃ $ε g • _).
  refine (lassociator _ _ _ • _).
  refine (wild_functor_comp L _ _ ▹ ε b • _).
  unfold lad in θ.
  refine (##L θ ▹ ε b). *)
  exact (λ θ, linvunitor g
              • ((adj_tL A a)^-1 ▹ g)
              • rassociator _ _ _
              • (#(adj_left A) (adj_unit A a) ◃ $(adj_counit A) g)
              • lassociator _ _ _
              • (wild_functor_comp (adj_left A) _ _ ▹ (adj_counit A) b)
              • (##(adj_left A) θ ▹ (adj_counit A) b)).
Qed.  
