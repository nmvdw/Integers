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
    exact (∏ a b : C, ∏ f g : C ⟦ a, b ⟧, f ==> g → pr2 F₁ a b f ==> pr2 F₁ a b g
         × ∏ a : C, id₁ (pr1 F₁ a) ==> pr2 F₁ a a (id₁ a)
                        × ∏ a b c : C, ∏ f : C ⟦ a, b ⟧, ∏ g : C ⟦ b, c ⟧, pr2 F₁ a b f · pr2 F₁ b c g ==> pr2 F₁ a c (f · g)).
Defined.    
