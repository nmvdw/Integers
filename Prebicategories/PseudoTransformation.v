(**
 - Definition of pseudotransformations between pseudofunctors over precategories 
 - Data projections
 - Law projections
 - Builders
 - Derived laws
 - Notation
From 'UniMath/Bicategories/Transformations/PseudoTransformation.v'
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.

Require Import Integers.Prebicategories.Invertible_2cells.
Require Import Integers.Prebicategories.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope cat.
Local Open Scope bicategory_scope.

(** Pseudotransformations **)
Definition pseudotrans_data
           {C D : prebicat}
           (F G : pseudofunctor C D)
  : UU.
Proof.
  use total2.
  - exact (∏ a : C, F a --> G a).
  - intro η₀.
    exact (∏ {a b : C} (f : a --> b), invertible_2cell (η₀ a · #G f) (#F f · η₀ b)).
Defined.
    
Definition make_pseudotrans_data
           {C D : prebicat}
           {F G : pseudofunctor C D}
           (η₀ : ∏ (a : C), F a --> G a)
           (η₁ : ∏ (a b : C) (f : a --> b), invertible_2cell (η₀ a · #G f) (#F f · η₀ b))
  : pseudotrans_data F G
  := (η₀ ,, η₁).

(** Projections **)
Definition pseudotrans_objects
           {C D : prebicat}
           {F G : pseudofunctor C D}
           (η : pseudotrans_data F G)
           (a : C)
  : F a --> G a
  := pr1 η a.

Coercion pseudotrans_objects : pseudotrans_data >-> Funclass.

Definition pseudotrans_morphisms
           {C D : prebicat}
           {F G : pseudofunctor C D}
           (η : pseudotrans_data F G)
           {a b : C}
           (f : a --> b)
  : invertible_2cell (η a · #G f) (#F f · η b)
  := pr2 η a b f.

Local Notation "'$'" := pseudotrans_morphisms.

(** Laws **)
Section TransLaws.
  Context {C D : prebicat}
          {F G : pseudofunctor C D}.
  Variable (η : pseudotrans_data F G).

  Definition pseudotrans_naturality_law : UU
    := ∏ (X Y : C) (f g : X --> Y) (α : f ==> g),
       (η X ◃ ##G α) • $η g
       =
       ($η f) • (##F α ▹ η Y).
  
  Definition pseudotrans_id_law : UU
    := ∏ a : C, (η a ◃ pseudofunctor_id G a) • $η (identity a)
                = runitor (η a) • linvunitor (η a) • (pseudofunctor_id F a ▹ η a).
  
  Definition pseudotrans_comp_law : UU
    := ∏ {a b c : C} (f : a --> b) (g : b --> c),
       η a ◃ pseudofunctor_comp G f g • $η (f · g)
       = lassociator (η a) (#G f) (#G g)
                     • ($η f ▹ #G g)
                     • rassociator (#F f) (η b) (#G g)
                     • (#F f ◃ $η g)
                     •  lassociator (#F f) (#F g) (η c)
                     • (pseudofunctor_comp F f g ▹ η c).

(*  Definition is_pseudotrans : UU
    := pseudotrans_naturality_law
         × pseudotrans_id_law
         × pseudotrans_comp_law. *)
  
  Definition is_pseudotrans : UU
    := pseudotrans_id_law
         × pseudotrans_comp_law.
End TransLaws.

Definition pseudotrans {C D : prebicat} (F G : pseudofunctor C D) : UU.
Proof.
  use total2.
  - exact (pseudotrans_data F G).
  - exact is_pseudotrans.
Defined.

(** Projections (cont) **)

Definition pseudocomponent_of
           {C D : prebicat}
           {F G : pseudofunctor C D}
           (η : pseudotrans F G)
  : ∏ (a : C), F a --> G a
  := pr11 η.

Coercion pseudocomponent_of : pseudotrans >-> Funclass.

Definition pseudonaturality_of
           {C D : prebicat}
           {F G : pseudofunctor C D}
           (η : pseudotrans F G)
  : ∏ {a b : C} (f : a --> b), invertible_2cell (η a · #G f) (#F f · η b)
  := pr21 η.

Definition make_pseudotrans
           {C D : prebicat}
           {F G : pseudofunctor C D}
           (η : pseudotrans_data F G)
           (Hη : is_pseudotrans η)
  : pseudotrans F G
:= η ,, Hη.

Coercion pseudotrans_to_pseudotrans_data
         {C D : prebicat}
         {F G : pseudofunctor C D}
         (η : pseudotrans F G)
  : pseudotrans_data F G
      := pr1 η.

(*Definition pseudotrans_natural
           {C D : prebicat}
           {F G : pseudofunctor C D}
           (η : pseudotrans F G)
  : ∏ (X Y : C) (f g : X --> Y) (α : f ==> g),
    (η X ◃ ##G α)
      • pseudonaturality_of η g
    =
    (pseudonaturality_of η f) • (##F α ▹ η Y)
  := pr12 η.*)

(*
Definition pseudotrans_inv_natural
           {C D : prebicat}
           {F G : pseudofunctor C D}
           (η : pseudotrans F G)
  : ∏ (X Y : C) (f g : X --> Y) (α : f ==> g),
    (pseudonaturality_of η f)^-1 • (η X ◃ ##G α)
    =
    (##F α ▹ η Y) • (pseudonaturality_of η g)^-1.
Proof.
  intros X Y f g α.
  use vcomp_move_L_Mp.
  { is_iso. }
  etrans.
  { exact (vassocl _ _ _). }
  use vcomp_move_R_pM.
  { is_iso. }
  cbn.
  exact (pseudotrans_natural η X Y f g α).
Qed.  *)

Definition pseudotrans_id
           {C D : prebicat}
           {F G : pseudofunctor C D}
           (η : pseudotrans F G)
  : ∏ (a : C),
    (η a ◃ pseudofunctor_id G a)
      • pseudonaturality_of η (id₁ a)
      =
(runitor (η a))
      • linvunitor (η a)
      • (pseudofunctor_id F a ▹ η a)
  := pr12 η.

Definition pseudotrans_comp
           {C D : prebicat}
           {F G : pseudofunctor C D}
           (η : pseudotrans F G)
  : ∏ {a b c : C} (f : a --> b) (g : b --> c),
    (η a ◃ pseudofunctor_comp G f g)
      • pseudonaturality_of η (f · g)
    =
    (lassociator (η a) (#G f) (#G g))
      • (pseudonaturality_of η f ▹ (#G g))
      • rassociator (#F f) (η b) (#G g)
      • (#F f ◃ pseudonaturality_of η g)
      • lassociator (#F f) (#F g) (η c)
      • (pseudofunctor_comp F f g ▹ η c)
  := pr22 η.

(** Derived Laws **)

Definition pseudotrans_id_alt
           {C D : prebicat}
           {F G : pseudofunctor C D}
           (η : pseudotrans F G)
  : ∏ (a : C),
    cell_from_invertible_2cell (pseudonaturality_of η (id₁ a))
    =
    (η a ◃ (pseudofunctor_id G a)^-1)
      • runitor (η a)
      • linvunitor (η a)
      • (pseudofunctor_id F a ▹ η a).
Proof.
  intros a.
  rewrite !vassocl.
  use vcomp_move_L_pM.
  { is_iso. }
  cbn.
  rewrite !vassocr.
  exact (pseudotrans_id η a).
Qed.


Definition pseudotrans_comp_alt
           {C D : prebicat}
           {F G : pseudofunctor C D}
           (η : pseudotrans F G)
  : ∏ {a b c : C} (f : a --> b) (g : b --> c),
    cell_from_invertible_2cell (pseudonaturality_of η (f · g))
    =
    (η a ◃ (pseudofunctor_comp G f g)^-1)
      • lassociator (η a) (#G f) (#G g)
      • (pseudonaturality_of η f ▹ (#G g))
      • rassociator (#F f) (η b) (#G g)
      • (#F f ◃ pseudonaturality_of η g)
      • lassociator (#F f) (#F g) (η c)
      • (pseudofunctor_comp F f g ▹ η c).
Proof.
  intros a b c f g.
  rewrite !vassocl.
  use vcomp_move_L_pM.
  { is_iso. }
  cbn.
  rewrite !vassocr.
  exact (pseudotrans_comp η f g).
Qed.


Definition pseudotrans_inv_comp_alt
           {C D : prebicat}
           {F G : pseudofunctor C D}
           (η : pseudotrans F G)
  : ∏ {a b c : C} (f : a --> b) (g : b --> c),
    (pseudonaturality_of η (f · g))^-1
    =
    ((pseudofunctor_comp F f g)^-1 ▹ η c)
      • rassociator (#F f) (#F g) (η c)
      • (#F f ◃ ((pseudonaturality_of η g)^-1))
      • lassociator (#F f) (η b) (#G g)
      • ((pseudonaturality_of η f)^-1 ▹ (#G g))
      • (rassociator (η a) (#G f) (#G g))
      • (η a ◃ (pseudofunctor_comp G f g)).
Proof.
  intros a b c f g.
  use vcomp_move_L_pM.
  { is_iso. }
  use vcomp_move_R_Mp.
  { is_iso. }
  use vcomp_move_L_pM.
  { is_iso. apply (pseudofunctor_comp G). }
  simpl.
  rewrite pseudotrans_comp_alt.
  rewrite !vassocl.
  reflexivity.
Qed.

