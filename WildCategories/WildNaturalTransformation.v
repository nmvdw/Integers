(*
 - Wild natural transformations between wild wunctors over wild categories
 - Identity and composition wild natural transformations
 - Whiskering wild natural transformations
 - Unitor and associator wild natural transformations
 - Wild category of wild categories
 - Notation
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

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(** Wild natural transformations**)
Definition wild_nat_trans {C D : wild_cat} (F G : wild_functor C D) : UU.
Proof.
  use total2.
  - exact (∏ a : C, F a --> G a).
  - intro η₀.
    exact (∏ {a b : C} (f : a --> b), invertible_2cell (η₀ a · #G f) (#F f · η₀ b)).
Defined.

Definition make_wild_nat_trans
           {C D : wild_cat}
           {F G : wild_functor C D}
           (η₀ : ∏ a : C, F a --> G a)
           (η₁ : ∏ {a b : C} (f : a --> b), invertible_2cell (η₀ a · #G f) (#F f · η₀ b))
  : wild_nat_trans F G.
Proof.
  exact (η₀ ,, η₁).
Defined.

(** Data projections **)
Definition wild_nat_trans_objects
           {C D : wild_cat}
           {F G : wild_functor C D}
           (η : wild_nat_trans F G)
           (a : C)
  : F a --> G a
  := pr1 η a.

Coercion wild_nat_trans_objects : wild_nat_trans >-> Funclass.

Definition wild_nat_trans_morphisms
           {C D : wild_cat}
           {F G : wild_functor C D}
           (η : wild_nat_trans F G)
           {a b : C}
           (f : a --> b)
  : invertible_2cell (η a · #G f) (#F f · η b)
  := pr2 η a b f.

Local Notation "'$'" := wild_nat_trans_morphisms.

(** Identity and composition wild natural transformations**)
Definition id_wild_nat_trans {C D : wild_cat} (F : wild_functor C D)
  : wild_nat_trans F F.
Proof.
  use make_wild_nat_trans.
  - exact (λ a, id₁ (F a)).
  - intros a b f. cbn.
    use make_invertible_2cell.
    + exact (lunitor (#F f) • rinvunitor (#F f)).
    + is_iso.
Defined.

Definition comp_wild_nat_trans
           {C D : wild_cat}
           {F G H : wild_functor C D}
           (η : wild_nat_trans F G)
           (γ : wild_nat_trans G H)
  : wild_nat_trans F H.
Proof.
  use make_wild_nat_trans.
  - exact (λ a, η a · γ a).
  - intros a b f. cbn.
    use make_invertible_2cell.
    + exact (rassociator (η a) (γ a) (#H f)
                         • (η a ◃ $γ f)
                         • lassociator (η a) (#G f) (γ b)
                         • ($η f ▹ γ b)
                         • rassociator (#F f) (η b) (γ b)).
            
    + is_iso.
      * exact (($γ f)^-1).
      * exact (($η f)^-1).
Defined.

(** Whiskering wild natural transformations **)
Definition lwhisker_wild_nat_trans
           {C D E : wild_cat}
           (F : wild_functor C D)
           {G H : wild_functor D E}
           (η : wild_nat_trans G H)
  : wild_nat_trans (F ✦ G) (F ✦ H).
Proof.
  use make_wild_nat_trans.
  - exact (λ a, η (F a)).
  - exact (λ a b f, $η (#F f)).
Defined.

Definition rwhisker_wild_nat_trans
           {C D E : wild_cat}
           {F G : wild_functor C D}
           (H : wild_functor D E)
           (η : wild_nat_trans F G)
  : wild_nat_trans (F ✦ H) (G ✦ H).
Proof.
  use make_wild_nat_trans.
  - exact (λ a, #H (η a)).
  - intros a b f.
    use make_invertible_2cell.
    + exact (wild_functor_comp H (η a) (#G f) • ##H ($η f) • (wild_functor_comp H (#F f) (η b))^-1).
    + is_iso.
      * exact ((wild_functor_comp H (η a) (#G f))^-1).
      * exact (wild_functor_is_iso H _).
Defined.

(** Unitor wild natural transformations **)
Definition lunitor_wild_nat_trans
           {C D : wild_cat}
           (F : wild_functor C D)
  : wild_nat_trans (id_wild_functor C ✦ F) F.
Proof.
  use make_wild_nat_trans.
  - exact (λ a, identity (F a)).
  - intros a b f.
    use make_invertible_2cell.
    + exact (lunitor (#F f) • rinvunitor (#F f)).
    + is_iso.
Defined.

Definition linvunitor_wild_nat_trans
           {C D : wild_cat}
           (F : wild_functor C D)
  : wild_nat_trans F (id_wild_functor C ✦ F).
Proof.
  use make_wild_nat_trans.
  - exact (λ a, identity (F a)).
  - intros a b f.
    use make_invertible_2cell.
    + exact (lunitor (#F f) • rinvunitor (#F f)).
    + is_iso.
Defined.

Definition runitor_wild_nat_trans
           {C D : wild_cat}
           (F : wild_functor C D)
  : wild_nat_trans (F ✦ id_wild_functor D) F.
Proof.
  use make_wild_nat_trans.
  - exact (λ a, identity (F a)).
  - intros a b f.
    use make_invertible_2cell.
    + exact (lunitor (#F f) • rinvunitor (#F f)).
    + is_iso.
Defined.

Definition rinvunitor_wild_nat_trans
           {C D : wild_cat}
           (F : wild_functor C D)
  : wild_nat_trans F (F ✦ id_wild_functor D).
Proof.
  use make_wild_nat_trans.
  - exact (λ a, identity (F a)).
  - intros a b f.
    use make_invertible_2cell.
    + exact (lunitor (#F f) • rinvunitor (#F f)).
    + is_iso.
Defined.


(** Associator wild natural transformations **)
Definition lassociator_wild_nat_trans
           {C D E B : wild_cat}
           (F : wild_functor C D)
           (G : wild_functor D E)
           (H : wild_functor E B)
  : wild_nat_trans (F ✦ (G ✦ H)) ((F ✦ G) ✦ H).
Proof.
  use make_wild_nat_trans.
  - exact (λ a, identity (H (G (F a)))).
  - intros a b f.
    use make_invertible_2cell.
    + exact (lunitor (#H (#G (#F f))) • rinvunitor (#H (#G (#F f)))).
    + is_iso.
Defined.

Definition rassociator_wild_nat_trans
           {C D E B : wild_cat}
           (F : wild_functor C D)
           (G : wild_functor D E)
           (H : wild_functor E B)
  : wild_nat_trans ((F ✦ G) ✦ H) (F ✦ (G ✦ H)).
Proof.
  use make_wild_nat_trans.
  - exact (λ a, identity (H (G (F a)))).
  - intros a b f.
    use make_invertible_2cell.
    + exact (lunitor (#H (#G (#F f))) • rinvunitor (#H (#G (#F f)))).
    + is_iso.
Defined.

(** Wild category of wild categories, wild funcotrs and wild natural transformations **)
Definition wildcatcat : wild_cat.
Proof.
  use build_wild_cat.
  - exact wild_cat.
  - exact wild_functor.
  - exact @wild_nat_trans.
  - exact id_wild_functor.
  - exact @comp_wild_functor.
  - exact @id_wild_nat_trans.
  - exact @comp_wild_nat_trans.
  - exact @lwhisker_wild_nat_trans.
  - exact @rwhisker_wild_nat_trans.
  - exact @lunitor_wild_nat_trans.
  - exact @linvunitor_wild_nat_trans.
  - exact @runitor_wild_nat_trans.
  - exact @rinvunitor_wild_nat_trans.
  - exact @lassociator_wild_nat_trans.
  - exact @rassociator_wild_nat_trans.
Defined.

(** Notation **)
Module Notations.
  Notation "'$'" := wild_nat_trans_morphisms.
End Notations.
