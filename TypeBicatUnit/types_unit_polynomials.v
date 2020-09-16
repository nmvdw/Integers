(* Polynomials to pseudofunctors for the bicategory of types with unit *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Import PseudoFunctor.Notations.

Require Import sem.prelude.all.
Require Import sem.signature.hit_signature.

Require Import Integers.TypeBicatUnit.TypeChaotic.

Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.

Definition act (P : poly_code) (A : UU) : UU.
Proof.
  induction P as [X | | | ].
  - exact X.
  - exact A.
  - exact (IHP1 ⨿ IHP2).
  - exact (IHP1 × IHP2).
Defined.

Definition actmap (P : poly_code) {A B : UU} (f : A → B)
  : type_chaotic_bicat ⟦ act P A, act P B ⟧.
Proof.
  cbn.
  induction P as [X | | | ].
  - exact (λ y, y).
  - exact f.
  - exact (coprodf IHP1 IHP2).
  - exact (dirprodf IHP1 IHP2).
Defined.    

Definition poly_type_unit (P : poly_code)
  : psfunctor type_chaotic_bicat type_chaotic_bicat.
Proof.
  use make_psfunctor.
  - use make_psfunctor_data.
    + exact (act P).
    + exact (λ A B f, actmap P f).
    + exact (λ _ _ _ _ _, tt).
    + exact (λ _, tt).
    + exact (λ _ _ _ _ _, tt).
  - repeat split.
  - split.
    + exact (λ _, chaotic_invertible_2cell).
    + exact (λ _ _ _ _ _, chaotic_invertible_2cell).
Defined.

Notation "⦃ P ⦄" := (poly_type_unit P). 
