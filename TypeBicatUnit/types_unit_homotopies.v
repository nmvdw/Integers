(* (Path) algebras for the bicategory of types with unit *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.
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
Require Import Integers.TypeBicatUnit.types_unit_endpoints.

Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.

Opaque comp_psfunctor.

Check disp_alg_bicat.

Definition DFcell {A P Q : poly_code} (l r : endpoint A P Q)
  : disp_bicat (total_bicat (disp_alg_bicat ⦃ A ⦄))
  := (add_cell_disp_cat (disp_alg_bicat ⦃ A ⦄) _ _ (endpoint_type_unit l) (endpoint_type_unit r)).

Definition DPathAlg (Σ : hit_signature) : bicat.
Proof.
  use total_bicat.
  
