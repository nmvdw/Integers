(** Pseudofunctors over precategories **)
(* Compiled from different files in UniMath/Bicategories, mainly PseudoFunctors/Display/PseudoFunctorBicat.v and PseudoFuncgtors/PseudoFunctor.v *)
(* UniMath defines pseudofunctors as instances of the pseudofunctor category, here they are defined directly*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.Bicategories.TypePrebicat.
Require Import Integers.Bicategories.DispPrebicat.
Require Import Integers.Bicategories.Invertible_2cells.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.
  
Definition pseudofunctor_data (C D : prebicat) : UU.
Proof.
  use total2.
  - use total2.
    + exact (C → D).
    + intro F₀.
      exact (∏ a b : C, a --> b → F₀ a --> F₀ b).
  - intro F₁.
    exact ((∏ a b : C, ∏ f g : a --> b, f ==> g → pr2 F₁ a b f ==> pr2 F₁ a b g)
         × (∏ a : C, id₁ (pr1 F₁ a) ==> pr2 F₁ a a (id₁ a))
                        × (∏ a b c : C, ∏ f : a --> b, ∏ g : b --> c, pr2 F₁ a b f · pr2 F₁ b c g ==> pr2 F₁ a c (f · g))).
Defined.    


(** Data projections **)
Definition F₀ {C D : prebicat} (F : pseudofunctor_data C D) : C → D
  := pr11 F.

Definition F₁ {C D : prebicat} (F : pseudofunctor_data C D) {a b : C} : a --> b → F₀ F a --> F₀ F b
  := pr21 F a b.

Definition F₂ {C D : prebicat} (F : pseudofunctor_data C D) {a b : C} {f g : a --> b}
  : f ==> g → F₁ F f ==> F₁ F g
  := pr12 F a b f g.

Definition Fid {C D : prebicat} (F : pseudofunctor_data C D) (a : C) : id₁ (F₀ F a) ==> F₁ F (id₁ a)
  := pr122 F a.

Definition Fcomp {C D : prebicat} (F : pseudofunctor_data C D) {a b c : C} (f : a --> b) (g : b --> c)
  : F₁ F f · F₁ F g ==> F₁ F (f · g)
  := pr222 F a b c f g.

(* F on objects are functions *)
Coercion F₀ : pseudofunctor_data >-> Funclass.
(*Local Notation "'#'" := F₁.*)
Local Notation "'##'" := F₂.
(* We can use # F from functors *)
Coercion functor_data_from_pseudofunctor_ob_mor_cell
         {C D : prebicat}
         (F : pseudofunctor_data C D)
  : functor_data C D
      := pr1 F.

Definition make_pseudofunctor_data
           {C D : prebicat}
           (F₀ : C → D)
           (F₁ : ∏ {a b : C}, a --> b → F₀ a --> F₀ b)
           (F₂ : ∏ {a b : C} {f g : a --> b}, f ==> g → F₁ f ==> F₁ g)
           (Fid : ∏ (a : C), identity (F₀ a) ==> F₁ (identity a))
           (Fcomp : (∏ (a b c : C) (f : a --> b) (g : b --> c),
                     F₁ f · F₁ g ==> F₁ (f · g)))
  : pseudofunctor_data C D.
Proof.
  exact ((F₀ ,, F₁) ,, (F₂ ,, Fid ,, Fcomp)).
Defined.

(** Laws **)
Section FunctorLaws.
  Context {C D : prebicat}.
  Variable (F : pseudofunctor_data C D).


  Definition pseudofunctor_invertible_cells : UU
  := ((∏ a : C, is_invertible_2cell (Fid F a))
             ×
             (∏ {a b c : C} (f : a --> b) (g : b --> c),
              is_invertible_2cell (Fcomp F f g))).

  Definition pseudofunctor_id2_law : UU
    := (∏ {a b : C} (f : a --> b), ## F (id2 f) = id2 (F₁ F f)).

  Definition pseudofunctor_vcomp2_law : UU
    := (∏ {a b : C} {f g h : a --> b} (θ : f ==> g) (γ : g ==> h), ## F (θ • γ) = ## F θ • ## F γ).

  Definition pseudofunctor_lwhisker_law : UU
    := ∏ (a b c : C) (f : a --> b) (g₁ g₂ : b --> c) (θ : g₁ ==> g₂),
       Fcomp F f g₁ • ##F (f ◃ θ)
       =
       #F f ◃ ##F θ • Fcomp F f g₂.

  Definition pseudofunctor_rwhisker_law : UU
    := ∏ (a b c : C) (f₁ f₂ : a --> b) (g : b --> c) (θ : f₁ ==> f₂),
       Fcomp F f₁ g • ##F (θ ▹ g)
       =
       ##F θ ▹ #F g • Fcomp F f₂ g.
  
  Definition pseudofunctor_lunitor_law : UU
    := ∏ (a b : C) (f : a --> b),
       lunitor (#F f)
       =
       (Fid F a ▹ #F f)
         • Fcomp F (identity a) f
         • ##F (lunitor f).

  Definition pseudofunctor_runitor_law : UU
    := ∏ (a b : C) (f : a --> b),
       runitor (#F f)
       =
       (#F f ◃ Fid F b)
         • Fcomp F f (identity b)
         • ##F (runitor f).

    Definition pseudofunctor_lassociator_law : UU
    := ∏ (a b c d : C) (f : a --> b) (g : b--> c) (h : c --> d),
       (#F f ◃ Fcomp F g h)
         • Fcomp F f (g · h)
         • ##F (lassociator f g h)
       =
       (lassociator (#F f) (#F g) (#F h))
         • (Fcomp F f g ▹ #F h)
         • Fcomp F (f · g) h.

    Definition pseudofunctor_laws : UU
      := pseudofunctor_id2_law
         × pseudofunctor_vcomp2_law
         × pseudofunctor_lwhisker_law
         × pseudofunctor_rwhisker_law
         × pseudofunctor_lunitor_law
         × pseudofunctor_runitor_law
         × pseudofunctor_lassociator_law.

    Definition is_pseudofunctor : UU
      := pseudofunctor_laws × pseudofunctor_invertible_cells.

(*    Definition is_pseudofunctor_isaprop : isaprop is_pseudofunctor.
    Proof.
        repeat (apply isapropdirprod) ; repeat (apply impred ; intro)
        ; try (apply D) ; try (apply isaprop_is_invertible_2cell).
     Defined.
*)
End FunctorLaws.

Definition pseudofunctor (C D : prebicat) : UU.
Proof.
  use total2.
  - exact (pseudofunctor_data C D).
  - exact is_pseudofunctor.
Defined.

Definition make_pseudofunctor
           { C D : prebicat }
           (F : pseudofunctor_data C D)
           (HF : pseudofunctor_laws F)
           (Fcells : pseudofunctor_invertible_cells F)
  : pseudofunctor C D
  := (F ,, (HF ,, Fcells)).

Coercion pseudofunctor_to_pseudofunctor_data
         {C D : prebicat}
         (F : pseudofunctor C D)
  : pseudofunctor_data C D
  := pr1 F.

Definition pseudofunctor_on_cells
           {C D : prebicat}
           (F : pseudofunctor C D)
           {a b : C}
           {f g : a --> b}
           (θ : f ==> g)
  : #F f ==> #F g
  := pr121 F a b f g θ.

Definition pseudofunctor_id
           {C D : prebicat}
           (F : pseudofunctor C D)
           (a : C)
           : invertible_2cell (identity (F a)) (#F (identity a)).
Proof.
  refine (pr122 (pr1 F) a ,, _).
  apply F.
Defined.

Definition pseudofunctor_comp
           {C D : prebicat}
           (F : pseudofunctor C D)
           {a b c : C}
           (f : a --> b)
           (g : b --> c)
           : invertible_2cell (#F f · #F g) (#F (f · g)).
Proof.
  refine (pr222 (pr1 F) a b c f g ,, _).
  apply F.
Defined.

Section Projection.
  Context {C D : prebicat}.
  Variable (F : pseudofunctor C D).
  
  Definition pseudofunctor_id2
    : ∏ {a b : C} (f : a --> b), ##F (id2 f) = id2 (#F f)
    := pr1 (pr12 F).

  Definition pseudofunctor_vcomp
    : ∏ {a b : C} {f g h : a --> b} (θ : f ==> g) (γ : g ==> h),
      ##F (θ • γ) = ##F θ • ##F γ
    := pr12 (pr12 F).

  Definition pseudofunctor_lwhisker
    : ∏ {a b c : C} (f : a --> b) {g₁ g₂ : b --> c} (θ : g₁ ==> g₂),
      pseudofunctor_comp F f g₁ • ##F (f ◃ θ)
      =
      #F f ◃ ##F θ • pseudofunctor_comp F f g₂
    := pr122 (pr12 F).

  Definition pseudofunctor_rwhisker
    : ∏ {a b c : C} {f₁ f₂ : a --> b} (g : b --> c) (θ : f₁ ==> f₂),
      pseudofunctor_comp F f₁ g • ##F (θ ▹ g)
      =
      ##F θ ▹ #F g • pseudofunctor_comp F f₂ g
    := pr1 (pr222 (pr12 F)).

  Definition pseudofunctor_lunitor
    : ∏ {a b : C} (f : a --> b),
      lunitor (#F f)
      =
      (pseudofunctor_id F a ▹ #F f)
        • pseudofunctor_comp F (identity a) f
        • ##F (lunitor f)
    := pr12 (pr222 (pr12 F)).

  Definition pseudofunctor_runitor
    : ∏ {a b : C} (f : a --> b),
      runitor (#F f)
      =
      (#F f ◃ pseudofunctor_id F b)
        • pseudofunctor_comp F f (identity b)
        • ##F (runitor f)
    := pr122 (pr222 (pr12 F)).

  Definition pseudofunctor_lassociator
    : ∏ {a b c d : C} (f : a --> b) (g : b --> c) (h : c --> d) ,
      (#F f ◃ pseudofunctor_comp F g h)
        • pseudofunctor_comp F f (g · h)
        • ##F (lassociator f g h)
      =
      (lassociator (#F f) (#F g) (#F h))
        • (pseudofunctor_comp F f g ▹ #F h)
        • pseudofunctor_comp F (f · g) h
    := pr222 (pr222 (pr12 F)).
End Projection.

(** Isos are preserved *)
Definition pseudofunctor_is_iso
           {C D : prebicat}
           (F : pseudofunctor C D)
           {a b : C}
           {f g : a --> b}
           (α : invertible_2cell f g)
  : is_invertible_2cell (##F α).
Proof.
  use tpair.
  - exact (##F (α^-1)).
  - split; cbn.
    + rewrite <- pseudofunctor_vcomp.
      refine (!(_  @ _)).
      * apply (!pseudofunctor_id2 F f).
      * apply maponpaths.
        apply (!vcomp_rinv α).
    + rewrite <- pseudofunctor_vcomp.
      refine (!(_ @ _)).
      * apply (!pseudofunctor_id2 F g).
      * apply maponpaths.
        apply (!vcomp_linv α).
Defined.

Section PseudoFunctorDerivedLaws.
  Context {C D : prebicat}.
  Variable (F : pseudofunctor C D).

  Definition pseudofunctor_linvunitor
             {a b : C}
             (f : a --> b)
    : ##F (linvunitor f)
      =
      (linvunitor (#F f))
        • ((pseudofunctor_id F a) ▹ #F f)
        • (pseudofunctor_comp F _ _).
  Proof.
    rewrite !vassocl.
    cbn.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    use vcomp_move_R_Mp.
    {
      refine (pseudofunctor_is_iso F (linvunitor f ,, _)).
      is_iso.
    }
    cbn.
    apply pseudofunctor_lunitor.
  Qed.

  Definition pseudofunctor_rinvunitor
             {a b : C}
             (f : a --> b)
    : ##F (rinvunitor f)
      =
      (rinvunitor (#F f))
        • (#F f ◃ pseudofunctor_id F b)
        • pseudofunctor_comp F _ _.
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    use vcomp_move_R_Mp.
    {
      refine (pseudofunctor_is_iso F (rinvunitor f ,, _)).
      is_iso.
    }
    cbn.

    apply pseudofunctor_runitor.
  Qed.

  Definition pseudofunctor_rassociator
             {a b c d : C}
             (f : a --> b) (g : b --> c) (h : c --> d)
    : (pseudofunctor_comp F f g ▹ #F h)
        • pseudofunctor_comp F (f · g) h
        • ##F (rassociator f g h)
      =
      (rassociator (#F f) (#F g) (#F h))
        • (#F f ◃ pseudofunctor_comp F g h)
        • pseudofunctor_comp F f (g · h).
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    use vcomp_move_R_Mp.
    { refine (pseudofunctor_is_iso F (rassociator f g h ,, _)).
      is_iso.
    }
    cbn.
    symmetry.
    exact (pseudofunctor_lassociator F f g h).
  Qed.

  Definition pseudofunctor_comp_natural
             {a b c : C}
             {g₁ g₂ : b --> c} {f₁ f₂ : a --> b}
             (θg : g₁ ==> g₂) (θf : f₁ ==> f₂)
    : pseudofunctor_comp F f₁ g₁ • ##F (θf ⋆ θg)
      =
      (##F θf) ⋆ (##F θg) • pseudofunctor_comp F f₂ g₂.
  Proof.
    unfold hcomp.
    rewrite !pseudofunctor_vcomp.
    rewrite !vassocr.
    rewrite !pseudofunctor_rwhisker.
    rewrite !vassocl.
    apply maponpaths.
    apply pseudofunctor_lwhisker.
  Qed.
  
  Definition pseudofunctor_F_lunitor
             {a b : C}
             (f : a --> b)
    : ##F (lunitor f)
      =
      ((pseudofunctor_comp F (identity a) f)^-1)
        • ((pseudofunctor_id F a)^-1 ▹ #F f)
        • lunitor (#F f).
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    exact (!(pseudofunctor_lunitor F f)).
  Qed.

  Definition pseudofunctor_F_runitor
             {a b : C}
             (f : a --> b)
    : ##F (runitor f)
      =
      ((pseudofunctor_comp F f (identity b))^-1)
        • (#F f ◃ (pseudofunctor_id F b)^-1)
        • runitor (#F f).
  Proof.
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    exact (!(pseudofunctor_runitor F f)).
  Qed.

  Definition pseudofunctor_lassociator_alt
             {a b c d : C}
             (f : a --> b) (g : b --> c) (h : c --> d)
    : (pseudofunctor_comp F f (g · h))
        • ##F (lassociator _ _ _)
        • (pseudofunctor_comp F (f · g) h)^-1
        • ((pseudofunctor_comp F f g)^-1 ▹ #F h)
        • rassociator _ _ _
      =
      #F f ◃ (pseudofunctor_comp F g h)^-1.
  Proof.
    use vcomp_move_R_Mp.
    { is_iso. }
    use vcomp_move_R_Mp.
    { is_iso. }
    use vcomp_move_R_Mp.
    { is_iso. }
    rewrite !vassocl.
    use vcomp_move_L_pM.
    { is_iso. }
    cbn.
    rewrite !vassocr.
    apply (pseudofunctor_lassociator F f g h).
  Qed.
End PseudoFunctorDerivedLaws.

Section PseudoFunctorLocalFunctor.
  Context {C D : prebicat}.
  Variable (F : pseudofunctor C D) (X Y : C).

    Definition Fmor_data
    : functor_data (hom X Y) (hom (F X) (F Y)).
  Proof.
    use make_functor_data.
    - exact (λ f, # F f).
    - exact (λ _ _ α, ##F α).
  Defined.

  Definition Fmor_is_functor
    : is_functor Fmor_data.
  Proof.
    split.
    - intros f.
      exact (pseudofunctor_id2 F f).
    - intros f g h α β.
      exact (pseudofunctor_vcomp F α β).
  Defined.

  Definition Fmor
    : hom X Y ⟶ hom (F X) (F Y).
  Proof.
    use make_functor.
    - exact Fmor_data.
    - exact Fmor_is_functor.
  Defined.
End PseudoFunctorLocalFunctor.

Module Notations.
  Notation "'#'" := (F₁).
  Notation "'##'" := (F₂).
End Notations.

(* Use styles of UM/Bi/PF/PseudoFunctor.v, Integers/Bi/DispPrebicat.v and UM/Core/Functors.v *)


  
