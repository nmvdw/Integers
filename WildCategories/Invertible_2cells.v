(** Invertible 2-cells **)
(* From UniMath.Bicategories.Core.Invertible_2cells.v *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Notations.

Require Import Integers.WildCategories.WildCat.

Local Open Scope cat.

Lemma is_invertible_2cell_vcomp {C : wild_cat} {a b : C} {f g h: a --> b}
      {x : f ==> g} (inv_x : is_invertible_2cell x)
      {y : g ==> h} (inv_y : is_invertible_2cell y)
  : is_invertible_2cell (x • y).
Proof.
  use make_is_invertible_2cell.
  - exact (inv_y^-1 • inv_x^-1).
Defined.

Lemma is_invertible_2cell_lwhisker {C : wild_cat} {a b c : C}
      (f : a --> b) {g1 g2 : b --> c}
      {x : g1 ==> g2} (inv_x : is_invertible_2cell x)
  : is_invertible_2cell (f ◃ x).
Proof.
  use make_is_invertible_2cell.
  - exact (f ◃ inv_x^-1).
Defined.


Lemma is_invertible_2cell_rwhisker {C : wild_cat} {a b c : C} {f1 f2 : a --> b} (g : b --> c)
      {x : f1 ==> f2} (inv_x : is_invertible_2cell x)
  : is_invertible_2cell (x ▹ g).
Proof.
  use make_is_invertible_2cell.
  - exact (inv_x^-1 ▹ g).
Defined.


Definition is_invertible_2cell_hcomp
       {C : wild_cat}
       {a b c : C}
       {f₁ g₁ : b --> c} {f₂ g₂ : a --> b}
       (η₁ : f₁ ==> g₁) (η₂ : f₂ ==> g₂)
       (inv_η₁ : is_invertible_2cell η₁)
       (inv_η₂ : is_invertible_2cell η₂)
  : is_invertible_2cell (η₁ ⋆⋆ η₂).
Proof.
  use make_is_invertible_2cell.
  - exact (inv_η₁^-1 ⋆⋆ inv_η₂^-1).
Defined.

(* .. *)


Ltac is_iso :=
  match goal with
  | [ |- is_invertible_2cell (runitor _) ] => apply is_invertible_2cell_runitor
  | [ |- is_invertible_2cell (rinvunitor _) ] => apply is_invertible_2cell_rinvunitor
  | [ |- is_invertible_2cell (lunitor _) ] => apply is_invertible_2cell_lunitor
  | [ |- is_invertible_2cell (linvunitor _) ] => apply is_invertible_2cell_linvunitor
  | [ |- is_invertible_2cell (rassociator _ _ _)] => apply is_invertible_2cell_rassociator
  | [ |- is_invertible_2cell (lassociator _ _ _)] => apply is_invertible_2cell_lassociator
  | [ |- is_invertible_2cell (_ ^-1)] => apply is_invertible_2cell_inv ; is_iso
  | [ |- is_invertible_2cell (_ • _)] => apply is_invertible_2cell_vcomp ; is_iso
  | [ |- is_invertible_2cell (_ ◃ _)] => apply is_invertible_2cell_lwhisker ; is_iso
  | [ |- is_invertible_2cell (_ ▹ _)] => apply is_invertible_2cell_rwhisker ; is_iso
  | [ |- is_invertible_2cell (_ ⋆⋆ _)] => apply is_invertible_2cell_hcomp ; is_iso
  | [ |- is_invertible_2cell (_ ⋆ _)] => apply is_invertible_2cell_hcomp ; is_iso
  | [ |- is_invertible_2cell (id₂ _)] => apply is_invertible_2cell_id₂
  | _ => try assumption
  end.

Definition inv_of_invertible_2cell
           {C : wild_cat}
           {X Y : C}
           {f g : X --> Y}
  : invertible_2cell f g → invertible_2cell g f.
Proof.
  intro θ.
  use make_invertible_2cell.
  - exact (θ^-1).
  - is_iso. 
Defined.


Definition comp_of_invertible_2cell
           {C : wild_cat}
           {X Y : C}
           {f g h : X --> Y}
  : invertible_2cell f g → invertible_2cell g h → invertible_2cell f h.
Proof.
  intros θ γ.
  use make_invertible_2cell.
  - exact (θ • γ).
  - is_iso.
    + exact θ.
    + exact γ.
Defined.
