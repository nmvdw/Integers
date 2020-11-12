(** Wild Functors between Wild Categories **)
(* Compiled from different files in UniMath/Bicategories, mainly PseudoFunctors/Display/PseudoFunctorBicat.v and PseudoFunctors/PseudoFunctor.v *)
(* UniMath defines pseudofunctors as instances of the pseudofunctor category, here they are defined directly. *)
(* This file also contains the identity, composition and projection wild functor, from UniMath/Bicategories/PseudoFunctors/Examples/Identity.v, Composition.v and Projection.v *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.WildCategories.WildCat.
Require Import Integers.WildCategories.DispWildCat.
Require Import Integers.WildCategories.Invertible_2cells. Import Notations.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.

Definition wild_functor (C D : wild_cat) : UU.
Proof.
  use total2.
  - exact (C → D).
  - intro F₀.
    use total2.
    + exact (∏ (a b : C), a --> b → F₀ a --> F₀ b).
    + intro F₁.
      exact ((∏ {a b : C} (f g : a --> b), f ==> g → F₁ a b f ==> F₁ a b g)
             × (∏ (a : C), invertible_2cell (id₁ (F₀ a)) (F₁ a a (id₁ a)))
             × (∏ {a b c : C} (f : a --> b) (g : b --> c),
                invertible_2cell (F₁ a b f · F₁ b c g) (F₁ a c (f · g)))).
Defined.

(* Data projections *)
Definition wild_functor_objects {C D : wild_cat} (F : wild_functor C D) : C → D
  := pr1 F.

Coercion wild_functor_objects : wild_functor >-> Funclass.

Definition wild_functor_morphisms {C D : wild_cat} (F : wild_functor C D) (a b : C)
  : a --> b → F a --> F b
  := pr12 F a b.

(* Coercing into functor_data makes # available for input, but not for output *)
Coercion functor_data_from_pseudofunctor_ob_mor_cell
         {C D : wild_cat}
         (F : wild_functor C D)
  : functor_data C D
  := pr1 F ,, wild_functor_morphisms F.
Local  Notation "'#'" := wild_functor_morphisms.

Definition wild_functor_cells {C D : wild_cat} (F : wild_functor C D)
           {a b : C} {f g : a --> b}
  : f ==> g → #F f ==> #F g
  := pr122 F a b f g.

Local Notation "'##'" := wild_functor_cells.

Definition wild_functor_id {C D : wild_cat} (F : wild_functor C D) (a : C)
  : invertible_2cell (id₁ (F a)) (#F (id₁ a))
  := pr1 (pr222 F) a.

Definition wild_functor_comp {C D : wild_cat} (F : wild_functor C D)
           {a b c : C} (f : a --> b) (g : b --> c)
  : invertible_2cell (#F f · #F g) (#F (f · g))
  := pr2 (pr222 F) a b c f g.

Definition make_wild_functor
           {C D : wild_cat}
           (F : C → D)
           (F₁ : ∏ {a b : C}, a --> b → F a --> F b)
           (F₂ : ∏ {a b : C} {f g : a --> b}, f ==> g → F₁ f ==> F₁ g)
           (Fi : ∏ {a : C}, invertible_2cell (id₁ (F a)) (F₁ (id₁ a)))
           (Fc : ∏ {a b c : C} {f : a --> b} {g : b --> c},
                 invertible_2cell (F₁ f · F₁ g) (F₁ (f · g)))
  : wild_functor C D.
Proof.
  exact (F ,, F₁ ,, F₂ ,, Fi ,, Fc).
Defined.

(* Isos are preserved *)
Definition wild_functor_is_iso
           {C D : wild_cat}
           (F : wild_functor C D)
           {a b : C}
           {f g : a --> b}
           (θ : invertible_2cell f g)
  : is_invertible_2cell (##F θ)
  := ##F (θ^-1).

(* Examples *)

Definition id_wild_functor (C : wild_cat) : wild_functor C C.
Proof.
  use make_wild_functor.
  - exact (λ a, a).
  - exact (λ a b f, f).
  - exact (λ a b f g θ, θ).
  - exact (λ a, id₂ (id₁ a) ,, id₂ (id₁ a)).
  - exact (λ a b c f g, id₂ (f · g) ,, id₂ (f · g)).
Defined.

Definition comp_wild_functor
           {C D E : wild_cat}
           (F : wild_functor C D)
           (G : wild_functor D E)
  : wild_functor C E.
Proof.
  use make_wild_functor.
  - exact (λ a, G (F a)).
  - exact (λ a b f, (#G (#F f))).
  - exact (λ a b f g θ, (##G (##F θ))).
  - intros a. cbn.
    use make_invertible_2cell.
    + exact (wild_functor_id G (F a) • ##G (wild_functor_id F a)).
    + cbn. is_iso.
      * exact (wild_functor_id G (F a)).
      * exact (wild_functor_is_iso G (wild_functor_id F a)).
  - intros a b c f g. cbn.
    use make_invertible_2cell.
    exact (wild_functor_comp G (#F f) (#F g) • ##G (wild_functor_comp F f g)).    
    + cbn. is_iso.
      * exact (wild_functor_comp G (#F f) (#F g)).
      * exact (wild_functor_is_iso G (wild_functor_comp F f g)).
Defined.

Definition pr1_wild_functor {C : wild_cat} (D : disp_wild_cat C)
  : wild_functor (total_wild_cat D) C.
Proof.
  use make_wild_functor.
  - exact (λ a, pr1 a).
  - exact (λ a b f, pr1 f).
  - exact (λ a b f g θ, pr1 θ).
  - exact (λ a, id2 (identity (pr1 a)) ,, id2 (identity (pr1 a))).
  - exact (λ a b c f g, id2 (pr1 f · pr1 g) ,, id2 (pr1 f · pr1 g)).
Defined.

Module Notations.
  Notation "'#'" := wild_functor_morphisms.
  Notation "'##'" := wild_functor_cells.
  Notation "F ⋯ G" := (comp_wild_functor F G) (at level 40). 
End Notations.
