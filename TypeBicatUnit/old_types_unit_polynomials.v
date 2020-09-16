(** Interpretation of polynomials in bicat of types with unit as 2-cells **)
(* Based on GrpdHITs/algebra/groupoid_polynomials.v and one_type_polynomials.v 
and GrpdHITs/signature/hit_signature.v *)

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
Require Import sem.algebra.one_types_polynomials.


Require Import Integers.TypeBicatUnit.TypeChaotic.

Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.

(* (* Use these from hit_signature.v *)
Definition poly_act_type_unit (P : poly_code) (X : type_unit_bicat)
           : type_unit_bicat.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact A.
  - exact X.
  - exact (IHP₁ ⨿ IHP₂).
  - exact (IHP₁ × IHP₂).
Defined.

Definition poly_act_type_unit_map (P : poly_code) (X Y : type_unit_bicat) (f : X → Y)
  : poly_act_type_unit P X → poly_act_type_unit P Y.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂ ].
  - exact (λ a, a).
  - exact f.
  - exact (coprodf IHP₁ IHP₂).
  - exact (dirprodf IHP₁ IHP₂).
Defined.
 *)

(** Preliminary operations we need *)




Definition poly_type_unit_homot
           (P : poly_code)
           {X Y : type_chaotic_bicat}
           {f g : X → Y}
           (p : f ~ g)
  : poly_map P f ~ poly_map P g.
Proof.
  induction P as [A | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ a, idpath a).  
  - exact p.
  - exact (coprodf_path IHP₁ IHP₂).
  - exact (dirprodf_path IHP₁ IHP₂).
Defined.

Definition poly_type_unit_data (P : poly_code)
  : psfunctor_data type_chaotic_bicat type_chaotic_bicat.
Proof.
  use make_psfunctor_data.
  - exact (λ X, poly_act P X).
  - exact (λ X Y, poly_map P).
  - exact (λ X Y f g x, tt).
  - exact (λ X, tt).
  - exact (λ X Y Z f g, tt).
Defined.

Definition poly_type_unit_laws (P : poly_code)
  : psfunctor_laws (poly_type_unit_data P).
Proof.
  repeat split.
Qed.

Definition poly_type_unit (P : poly_code)
  : psfunctor type_chaotic_bicat type_chaotic_bicat.
Proof.
  use make_psfunctor.
  - exact (poly_type_unit_data P).
  - exact (poly_type_unit_laws P).
  - split. 
    + exact (λ X, chaotic_invertible_2cell).
    + exact (λ X Y Z f g, chaotic_invertible_2cell).
Defined.

Notation "⦃ P ⦄" := (poly_type_unit P).
