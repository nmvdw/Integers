(* Endpoints to pseudotransformations for the bicategory of types with unit *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Constant.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.

Require Import UniMath.Bicategories.Transformations.PseudoTransformation.

Require Import sem.prelude.all.
Require Import sem.signature.hit_signature.

Require Import Integers.TypeBicatUnit.TypeChaotic.
Require Import Integers.TypeBicatUnit.types_unit_polynomials.

Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.

Opaque comp_psfunctor.

Definition objects {A P Q : poly_code} (e : endpoint A P Q) (X : UU) (hX : act A X → X)
  : act P X →  act Q X.
Proof.
  induction e as [ | | | | | | | P Z z | | ].
  - exact (λ y, y).
  - exact (λ y, IHe2 (IHe1 y)).
  - exact inl.
  - exact inr.
  - exact pr1.
  - exact pr2.
  - exact (λ y, IHe1 y,, IHe2 y).
  - exact (λ y, z).
  - exact f.
  - exact hX.
Defined.

Definition endpoint_type_unit (A P Q : poly_code) (e : endpoint A P Q)
  : pstrans
      (comp_psfunctor ⦃ P ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)))
      (comp_psfunctor ⦃ Q ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄))).
Proof.
  use make_pstrans.
  - use make_pstrans_data.
    + destruct X as [ X hX].
      exact (objects e X hX).
    + exact (λ _ _ _, chaotic_invertible_2cell0).
  - repeat split.
Defined.

