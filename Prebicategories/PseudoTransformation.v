(** Pseudotransformations between pseudofunctors over precategories **)
(* Copied from UniMath/Bicategories/Transformations/PseudoTransformation.v *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

(*Require Import Integers.Prebicategories.TypePrebicat.
Require Import Integers.Prebicategories.DispPrebicat.*)
Require Import Integers.Prebicategories.Invertible_2cells.
Require Import Integers.Prebicategories.PseudoFunctor.
Import PseudoFunctor.Notations.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.

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

(* Data projections *)
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

(* unfinished *)
Definition id_pseudotrans
           {C D : prebicat}
           (F : pseudofunctor C D)
  : pseudotrans F F.
Proof.
  use make_pseudotrans.
  - use make_pseudotrans_data.
    + intro a.
      apply identity.
    + intros a b f.
      unfold invertible_2cell.
      exists ((pseudofunctor_id F a ▹ #F f) • pseudofunctor_comp F (identity a) f • ##F (lunitor f • rinvunitor f) • (pseudofunctor_comp F f (identity b))^-1 • (#F f ◃ (pseudofunctor_id F b)^-1)).

      is_iso.
      * unfold is_invertible_2cell.
        exists ((pseudofunctor_id F a)^-1).
        split.
        -- apply vcomp_rinv.
        -- apply vcomp_linv.
      * unfold is_invertible_2cell.
        exists ((pseudofunctor_comp F (id₁ a) f)^-1).
        split.
        -- apply vcomp_rinv.
        -- apply vcomp_linv.
      * use tpair.
        -- exact (##F (runitor f • linvunitor f)).
        -- split.
           ++ refine (_ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _).
              ** apply maponpaths.
                 apply pseudofunctor_vcomp.
              ** apply maponpaths_2.
                 apply pseudofunctor_vcomp.
              ** apply vassocr.
              ** apply maponpaths_2.
                 apply vassocl.
              ** apply maponpaths_2.
                 apply maponpaths.
                 apply (!pseudofunctor_vcomp _ _ _).
              ** apply maponpaths_2.
                 apply maponpaths.
                 apply maponpaths.
                 apply rinvunitor_runitor.
              ** apply maponpaths_2.
                 apply (!pseudofunctor_vcomp _ _ _ ).
              ** apply maponpaths_2.
                 apply maponpaths.
                 apply id2_right.
              ** apply (!pseudofunctor_vcomp _ _ _).
              ** apply maponpaths.
                 apply lunitor_linvunitor.
              ** apply pseudofunctor_id2.
           ++ refine (_ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _).
              ** apply maponpaths.
                 apply pseudofunctor_vcomp.
              ** apply maponpaths_2.
                 apply pseudofunctor_vcomp.
              ** apply vassocr.
              ** apply maponpaths_2.
                 apply vassocl.
              ** apply maponpaths_2.
                 apply maponpaths.
                 apply (!pseudofunctor_vcomp _ _ _).
              ** apply maponpaths_2.
                 apply maponpaths.
                 apply maponpaths.
                 apply linvunitor_lunitor.
              ** apply maponpaths_2.
                 apply (!pseudofunctor_vcomp _ _ _ ).
              ** apply maponpaths_2.
                 apply maponpaths.
                 apply id2_right.
              ** apply (!pseudofunctor_vcomp _ _ _).
              ** apply maponpaths.
                 apply runitor_rinvunitor.
              ** apply pseudofunctor_id2.
  - split.
    + unfold pseudotrans_id_law.
      intros. cbn.
Abort.
(*
                := id₁ F.
 *)

(* unfinished *)
Definition comp_pstrans
           {C D : prebicat}
           {F G H : pseudofunctor C D}
           (η : pseudotrans F G) (σ : pseudotrans G H)
  : pseudotrans F H.
Proof.
  use tpair.
  - use tpair.
    + intro a.
      apply (η a · σ a).
    + cbn.
      intros a b f.
      unfold invertible_2cell.
      exists (rassociator _ _ _ • (η a ◃ $σ f) • lassociator _ _ _ • ($η f ▹ σ b) • rassociator _ _ _).
      is_iso.
      * unfold is_invertible_2cell.
        exists (($σ f)^-1).
        split.
        -- apply vcomp_rinv.
        -- apply vcomp_linv.
      * unfold is_invertible_2cell.
        exists (($η f)^-1).
        split.
        -- apply vcomp_rinv.
        -- apply vcomp_linv.
  - unfold is_pseudotrans.
    split.
    + unfold pseudotrans_id_law.
      intro a. cbn.
Abort.

(* pseudotrans on data *)

