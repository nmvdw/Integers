(** Interpretation of endpoints in types with unit as 2-cells. **)
(* Based on GrpHITs/algebra/one_type_endpoints.v *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Groupoids.


(*Require Import UniMath.CategoryTheory.DisplayedCats.Core.*)
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.

Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Base.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map1Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Map2Cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Identitor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.Compositor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Projection.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Constant.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.

Require Import sem.prelude.all.
Require Import sem.signature.hit_signature.
Require Import sem.algebra.one_types_polynomials.

Require Import Integers.TypeBicatUnit.TypeChaotic.
Require Import Integers.TypeBicatUnit.old_types_unit_polynomials.

Local Open Scope cat.
(*Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.*)

Opaque comp_psfunctor.


Definition sem_endpoint_type_unit
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X : type_chaotic_bicat}
           (c : poly_act A X → X)
  : poly_act P X → poly_act Q X
  := sem_endpoint_UU e c.

Definition endpoint_type_unit_natural
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X Y : type_chaotic_bicat}
           {cX : poly_act A X → X}
           {cY : poly_act A Y → Y}
           {f : X → Y}
           (ef : ((λ x, f (cX x)) ~ (λ x, cY (poly_map A f x))))
           (x : poly_act P X)
  : poly_map Q f (sem_endpoint_type_unit e cX x)
    =
    sem_endpoint_type_unit e cY (poly_map P f x).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ g | ].
  - (* Identity *)
    exact (idpath _).
  - (* Composition *)
    exact (IHe₂ (sem_endpoint_type_unit e₁ cX x)
           @ maponpaths (sem_endpoint_type_unit e₂ cY) (IHe₁ x)).
  - (* Left inclusion *)
    exact (idpath _).
  - (* Right inclusion *)
    exact (idpath _).
  - (* Left projection *)
    exact (idpath _).
  - (* Right projection *)
    exact (idpath _).
  - (* Pairing *)
    exact (pathsdirprod (IHe₁ x) (IHe₂ x)).
  - (* Constant *)
    exact (idpath _).
  - (* Constant map *)
    exact (idpath _).
  - (* Constructor *)
    exact (ef x).
Defined.
                      
Definition endpoint_type_unit_data
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : pstrans_data
      (comp_psfunctor (⦃ P ⦄) (pr1_psfunctor (disp_alg_bicat (⦃ A ⦄))))
      (comp_psfunctor (⦃ Q ⦄) (pr1_psfunctor (disp_alg_bicat (⦃ A ⦄)))).
Proof.
  use make_pstrans_data.
  - exact (λ X, sem_endpoint_type_unit e (pr2 X)).
  - intros X Y f.
    use make_invertible_2cell.
    + exact tt.
    + use tpair.
      * exact tt.
      * split; exact (idpath tt).
Defined.
(*
Definition endpoint_type_unit_natural_natural
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X Y : type_chaotic_bicat}
           {cX : poly_act A X → X}
           {cY : poly_act A Y → Y}
           {f g : X → Y}
           {ef : ((λ x, f (cX x)) ~ (λ x, cY (poly_map A f x)))}
           {eg : ((λ x, g (cX x)) ~ (λ x, cY (poly_map A g x)))}
           {αp : f ~ g}
           (αh : (λ x : poly_act A X, αp (cX x) @ eg x)
                 =
                 (λ x : poly_act A X, ef x @ maponpaths cY (poly_homot A αp x)))
           (x : poly_act P X)
  : poly_homot Q αp (sem_endpoint_type_unit e cX x)
               @ endpoint_type_unit_natural e eg x
    =
    endpoint_type_unit_natural e ef x
                               @ maponpaths (sem_endpoint_type_unit e cY) (poly_homot P αp x).
Proof.  
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q
                  | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ h | ].
  - (* Identity *)
    exact (pathscomp0rid _ @ !(maponpathsidfun _)).
  - (* Composition *)
    exact (path_assoc _ _ _
           @ maponpaths (λ z, z @ _) (IHe₂ (sem_endpoint_UU e₁ cX x))
           @ !(path_assoc _ _ _)
           @ maponpaths
               (λ z, _ @ z)
               (!(maponpathscomp0 _ _ _)
                @ maponpaths
                    (maponpaths (sem_endpoint_UU e₂ cY))
                    (IHe₁ x)
                @ maponpathscomp0 _ _ _
                @ maponpaths
                    (λ z, _ @ z)
                    (maponpathscomp _ _ _))
           @ path_assoc _ _ _).
  - (* Left inclusion *)
    exact (pathscomp0rid _).
  - (* Right inclusion *)
    exact (pathscomp0rid _).
  - (* Left projection *)
    exact (pathscomp0rid _ @ !(maponpaths_pr1_pathsdirprod _ _)).
  - (* Right projection *)
    exact (pathscomp0rid _ @ !(maponpaths_pr2_pathsdirprod _ _)).
  - (* Pairing *)
    exact (pathsdirprod_concat _ _ _ _
           @ paths_pathsdirprod (IHe₁ x) (IHe₂ x)
           @ !(pathsdirprod_concat _ _ _ _)
           @ maponpaths
               (λ z, _ @ z)
               (!(maponpaths_prod_path _ _ _))).
  - (* Constant *)
    exact (!(maponpaths_for_constant_function _ _)).
  - (* Constant map *)
    exact (idpath _).
  - (* Constructor *)
    exact (eqtohomot αh x).
Qed.*)


Definition endpoint_type_unit_is_pstrans
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : is_pstrans (endpoint_type_unit_data e).
Proof.
  repeat split.
Qed.

Definition endpoint_type_unit
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : pstrans
      (comp_psfunctor ⦃ P ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄)))
      (comp_psfunctor ⦃ Q ⦄ (pr1_psfunctor (disp_alg_bicat ⦃ A ⦄))).
Proof.
  use make_pstrans.
  - exact (endpoint_type_unit_data e).
  - exact (endpoint_type_unit_is_pstrans e).
Defined.
