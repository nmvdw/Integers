(*
 - Wild natural isomorphisms between wild wunctors over wild categories
 - Identity wild natural isomorphism
From 'UniMath/Bicategories/Transformations/PseudoTransformation.v'
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
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

(** Wild natural isomorphisms **)
Definition are_inv
           {C D : wild_cat}
           {F G : wild_functor C D}
           (η : wild_nat_trans F G)
           (η_inv : wild_nat_trans G F)
  : UU.
Proof.
  refine (_ × _).
  - exact (∏ a : C, invertible_2cell ((η a) · (η_inv a)) (identity (F a))).
  - exact (∏ a : C, invertible_2cell ((η_inv a) · (η a)) (identity (G a))).
Defined.
    
Definition wild_nat_iso
           {C D : wild_cat}
           (F G : wild_functor C D)
  : UU
  := ∑ (η : wild_nat_trans F G)
       (η_inv : wild_nat_trans G F),
     are_inv η η_inv.

Definition make_wild_nat_iso
           {C D : wild_cat}
           {F G : wild_functor C D}
           (η : wild_nat_trans F G)
           (η_inv : wild_nat_trans G F)
           (η_r : ∏ a : C, invertible_2cell ((η a) · (η_inv a)) (identity (F a)))
           (η_l : ∏ a : C, invertible_2cell ((η_inv a) · (η a)) (identity (G a)))
  : wild_nat_iso F G
  := (η,, η_inv,, η_r,, η_l).

(** Projections **)
Definition wild_nat_iso_trans
           {C D : wild_cat}
           {F G : wild_functor C D}
           (θ : wild_nat_iso F G)
  : wild_nat_trans F G
  := pr1 θ.

Definition wild_nat_iso_trans_inv
           {C D : wild_cat}
           {F G : wild_functor C D}
           (θ : wild_nat_iso G F)
  : wild_nat_trans F G
  := pr12 θ.

Coercion wild_nat_iso_trans : wild_nat_iso >-> wild_nat_trans.

Definition wild_nat_iso_r
           {C D : wild_cat}
           {F G : wild_functor C D}
           (θ : wild_nat_iso F G)
  : ∏ a : C,
          invertible_2cell ((θ a) · ((wild_nat_iso_trans_inv θ) a)) (identity (F a))
  := pr122 θ.

Definition wild_nat_iso_l
           {C D : wild_cat}
           {F G : wild_functor C D}
           (θ : wild_nat_iso F G)
  : ∏ a : C,
          invertible_2cell (((wild_nat_iso_trans_inv θ) a) · (θ a)) (identity (G a))
  := pr222 θ.

(** Identity wild natural isomorphisms**)
Definition id_wild_nat_iso {C D : wild_cat} (F : wild_functor C D)
  : wild_nat_iso F F.
Proof.
  use make_wild_nat_iso.
  - exact (id_wild_nat_trans F).
  - exact (id_wild_nat_trans F).
  - exact (λ a, lunitor (id₁ (F a)),, rinvunitor (id₁ (F a))).
  - exact (λ a, runitor (id₁ (F a)),, linvunitor (id₁ (F a))).
Defined.
