(** Pseudofunctors over precategories **)
(* Compiled from different files in UniMath/Bicategories *)
(* UniMath defines pseudofunctors as instances of the pseudofunctor category, I want to define them directly (like how UniMath defines functors on categories) *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.Bicategories.TypePrebicat.
Require Import Integers.Bicategories.DispPrebicat.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.
  
Section pseudofunctors.
Variable (C D : prebicat).
  
Definition pseudofunctor_data : UU.
Proof.
  use total2.
  - use total2.
    + exact (C → D).
    + intro F₀.
      exact (∏ a b : C, a --> b → F₀ a --> F₀ b).
  - intro F₁.
    exact ((∏ a b : C, ∏ f g : C ⟦ a, b ⟧, f ==> g → pr2 F₁ a b f ==> pr2 F₁ a b g)
         × (∏ a : C, id₁ (pr1 F₁ a) ==> pr2 F₁ a a (id₁ a))
                        × (∏ a b c : C, ∏ f : C ⟦ a, b ⟧, ∏ g : C ⟦ b, c ⟧, pr2 F₁ a b f · pr2 F₁ b c g ==> pr2 F₁ a c (f · g))).
Defined.    

(** Data projections **)
Definition F₀ (F : pseudofunctor_data) : C → D
  := pr11 F.

Definition F₁ (F : pseudofunctor_data) {a b : C} : a --> b → F₀ F a --> F₀ F b
  := pr21 F a b.

Definition F₂ (F : pseudofunctor_data) {a b : C} {f g : C ⟦ a, b ⟧}
  : f ==> g → F₁ F f ==> F₁ F g
  := pr12 F a b f g.

Definition Fid (F : pseudofunctor_data) {a : C} : id₁ (F₀ F a) ==> F₁ F (id₁ a)
  := pr122 F a.

Definition Fcomp (F : pseudofunctor_data) {a b c : C} {f : C ⟦ a, b ⟧} {g : C ⟦ b, c ⟧}
  : F₁ F f · F₁ F g ==> F₁ F (f · g)
  := pr222 F a b c f g.

Definition make_pseudofunctor_data
           (F₀ : C → D)
           (F₁ : ∏ {a b : C}, C⟦a,b⟧ → D⟦F₀ a, F₀ b⟧)
           (F₂ : ∏ {a b : C} {f g : C⟦a,b⟧}, f ==> g → F₁ f ==> F₁ g)
           (Fid : ∏ (a : C), identity (F₀ a) ==> F₁ (identity a))
           (Fcomp : (∏ (a b c : C) (f : a --> b) (g : b --> c),
                     F₁ f · F₁ g ==> F₁ (f · g)))
  : pseudofunctor_data.
Proof.
  exact ((F₀ ,, F₁) ,, (F₂ ,, Fid ,, Fcomp)).
Defined.


(** todo **)
(* F₂s are invertible *)

(* psfunctor laws *)

(* Notation *)

(* More laws and lemmas *)

(* Use styles of UM/Bi/PF/PseudoFunctor.v, Integers/Bi/DispPrebicat.v and UM/Core/Functors.v *)
