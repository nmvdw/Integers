(** Interpretation of polynomials in bicat of types with unit as 2-cells **)
(* Based on GrpdHITs/algebra/groupoid_polynomials.v and one_type_polynomials.v 
and GrpdHITs/signature/hit_signature.v *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Algebras.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DispDepProd.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.Add2Cell.

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
(*Require Import sem.algebra.one_types_polynomials.*)


Require Import Integers.TypeBicatUnit.TypeChaotic.
Require Import Integers.TypeBicatUnit.types_unit_polynomials.
Require Import Integers.TypeBicatUnit.types_unit_endpoints.

Local Open Scope cat.
(*Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.*)


Definition homot_endpoint_types_unit
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l : ∏ (j : J), endpoint A (S j) I}
           {r : ∏ (j : J), endpoint A (S j) I}
           {Q : poly_code}
           {TR : poly_code}
           {al ar : endpoint A Q TR}
           {T : poly_code}
           {sl sr : endpoint A Q T}
           (p : homot_endpoint l r al ar sl sr)
           (X : total_bicat (disp_alg_bicat ⦃ A ⦄))
           (pX' : ∏ (j : J),
                  pr111 (endpoint_type_unit (l j)) X
                  ==>
                  pr111 (endpoint_type_unit (r j)) X)
        (*   (pX :  ∏ (i : J),
                 endpoint_type_unit (l i) X
                 ~
                 endpoint_type_unit (r i) X) *)
           (z : poly_act Q (pr1 X : type_chaotic_bicat))
           (p_arg : endpoint_type_unit al X z = endpoint_type_unit ar X z)
  : endpoint_type_unit sl X z = endpoint_type_unit sr X z.
Proof.
  Check (endpoint_type_unit sl X z).
  cbn in p_arg.
  Locate sem_endpoint_type_unit.


  induction p as [T e | T e₁ e₂ p IHp | T e₁ e₂ e₃ p₁ IHP₁ p₂ IHP₂
                  | T₁ T₂ e₁ e₂ e₃ h IHh
                  | R₁ R₂ T e₁ e₂ e₃ | T e | T e
                  | P R e₁ e₂ | P R e₁ e₂
                  | T₁ T₂ e₁ e₂ e₃ e₄ p₁ IHp₁ p₂ IHp₂
                  | P₁ P₂ P₃ e₁ e₂ e₃
                  | Z x T e | j e | ].

  - (** identity path *)
    exact (idpath _).
  - (** inverse path *)
    exact (!IHp).
  - (** concatenation of paths *)
    exact (IHP₁ @ IHP₂).
  - (** ap on paths *)
    exact (maponpaths (sem_endpoint_UU e₃ (pr2 X)) IHh).
  - (** associator *)
    apply idpath.
  - (** left unitor *)
    apply idpath.
  - (** right unitor *)
    apply idpath.
  - (** first projection *)
    apply idpath.
  - (** second projection *)
    apply idpath.
  - (** pairing *)
    exact (pathsdirprod IHp₁ IHp₂).
  - (** composition before pair *)
    apply idpath.
  - (** composition with constant *)
    apply idpath.
  - (** path constructor *)
    exact (pX' j).
  - (** path argument *)
    exact p_arg.
Defined.


  := sem_homot_endpoint_UU p (pr1 X : type_chaotic_bicat) (pr2 X) pX z p_arg.

 
(** Bicategory of prealgebras **)
Definition hit_prealgebra_type_unit
           (Σ : hit_signature)
  : bicat
  := total_bicat (disp_alg_bicat ⦃ point_constr Σ ⦄).

(** Projections and builders of prealgebras **)
Section HITPreAlgebraProjections.
  Context {Σ : hit_signature}
          (X : hit_prealgebra_type_unit Σ).

  Definition prealg_carrier_type_unit : type_chaotic_bicat := pr1 X.

  Definition prealg_constr_type_unit
    : (poly_act (point_constr Σ ) prealg_carrier_type_unit : type_chaotic_bicat) --> prealg_carrier_type_unit
    := pr2 X.

End HITPreAlgebraProjections.

Definition make_hit_prealgebra_type_unit
           {Σ : hit_signature}
           (X : type_chaotic_bicat)
           (f : poly_act (point_constr Σ) X → X)
  : hit_prealgebra_type_unit Σ
  := X ,, f.

Definition preserves_point_ot
           {Σ : hit_signature}
           {X Y : hit_prealgebra_type_unit Σ}
           (f : prealg_carrier_type_unit X → prealg_carrier_type_unit Y)
  : UU
  := ∏ (x : poly_act (point_constr Σ) (prealg_carrier_type_unit X)),
         f (prealg_constr_type_unit X x)
         =
         prealg_constr_type_unit Y (poly_map (point_constr Σ) f x).

Definition preserves_point_type_unit
           {Σ : hit_signature}
           {X Y : hit_prealgebra_type_unit Σ}
           (f : prealg_carrier_type_unit X --> prealg_carrier_type_unit Y)
  : UU
  := prealg_constr_type_unit X · f ==> # ⦃ point_constr Σ ⦄ f · prealg_constr_type_unit Y.

           
Section HITPreAlgebraMorProjections.
  Context {Σ : hit_signature}
          {X Y : hit_prealgebra_type_unit Σ}
          (f : X --> Y).

  Definition prealg_map_carrier_type_unit
    : prealg_carrier_type_unit X → prealg_carrier_type_unit Y
    := pr1 f.

  Definition prealg_map_commute_type_unit
    : preserves_point_type_unit prealg_map_carrier_type_unit
    := pr12 f.

End HITPreAlgebraMorProjections.

Definition make_hit_prealgebra_mor_type_unit
           {Σ : hit_signature}
           {X Y : hit_prealgebra_type_unit Σ}
           (f : prealg_carrier_type_unit X → prealg_carrier_type_unit Y)
           (Hf : preserves_point_type_unit f)
  : X --> Y.
Proof.
  use tpair.
  - exact f.
  - use make_invertible_2cell.
    + exact tt.
    + exact chaotic_invertible_2cell.
Defined.

(** Path Algebras for a HIT signature *)
Definition hit_path_algebra_disp_type_unit
           (Σ : hit_signature)
  : disp_bicat (hit_prealgebra_type_unit Σ)
  := disp_depprod_bicat
       (path_label Σ)
       (λ j, add_cell_disp_cat
             _ _ _
             (endpoint_type_unit (path_left Σ j))
             (endpoint_type_unit (path_right Σ j))).

Definition hit_path_algebra_type_unit
           (Σ : hit_signature)
  : bicat
  := total_bicat (hit_path_algebra_disp_type_unit Σ).

(** Projections *)
Section HITPathAlgebraProjections.
  Context {Σ : hit_signature}
          (X : hit_path_algebra_type_unit Σ).

  Definition path_alg_carrier_type_unit
    : type_chaotic_bicat
    := prealg_carrier_type_unit (pr1 X).

  Definition path_alg_constr_type_unit
    : (⦃ point_constr Σ ⦄ path_alg_carrier_type_unit : type_chaotic_bicat) → path_alg_carrier_type_unit
    := prealg_constr_type_unit (pr1 X).

  Definition path_alg_path_type_unit
             (j : path_label Σ)
    : endpoint_type_unit (path_left Σ j) (pr1 X)
      ==>
      endpoint_type_unit (path_right Σ j) (pr1 X)
    := pr2 X j.
End HITPathAlgebraProjections.

Definition make_hit_path_algebra_type_unit
           {Σ : hit_signature}
           (X : hit_prealgebra_type_unit Σ)
           (pX : ∏ (j : path_label Σ),
                 endpoint_type_unit (path_left Σ j) X
                 ==>
                 endpoint_type_unit (path_right Σ j) X)
  : hit_path_algebra_type_unit Σ
  := X ,, pX.

Definition preserves_path_type_unit
           {Σ : hit_signature}
           {X Y : hit_path_algebra_type_unit Σ}
           (f : pr1 X --> pr1 Y)
           (Hf : preserves_point_type_unit (pr1 f))
  : UU.
Proof.
Abort.

Section HITPathAlgebraMorProjections.
  Context {Σ : hit_signature}
          {X Y : hit_path_algebra_type_unit Σ}
          (f : X --> Y).

  Definition path_alg_map_carrier_type_unit
    : path_alg_carrier_type_unit X --> path_alg_carrier_type_unit Y
    := prealg_map_carrier_type_unit (pr1 f).

  Definition path_alg_map_commute_type_unit
    : prealg_constr_type_unit (pr1 X) · path_alg_map_carrier_type_unit
      ==>
      # ⦃ point_constr Σ ⦄ path_alg_map_carrier_type_unit · prealg_constr_type_unit (pr1 Y)
    := prealg_map_commute_type_unit (pr1 f).

  
  Definition path_alg_map_path_type_unit
             (j : path_label Σ)
             (x : poly_act (path_source Σ j) (pr11 X))
    : UU.
  Proof.
    Check path_alg_path_type_unit.
    Check (pr1 (psnaturality_of (endpoint_type_unit (path_right Σ j)) (pr1 f))).

    Check (pr2 Y j).
    Check (poly_map (path_source Σ j) (pr11 f) x).
    
   
  Abort.
End HITPathAlgebraMorProjections.

(*
Definition make_hit_path_alg_map_type_unit ... 
 *)

(** HIT algebras *)
Definition is_hit_algebra_one_types
           (Σ : hit_signature)
           (X : hit_path_algebra_type_unit Σ)
  : UU.
Proof.
pose (pr2 X) as p.
cbn in p.


Check (pr2 X).
Check (λ (j : homot_label Σ), homot_endpoint_types_unit (homot_left_path Σ j) (pr1 X)).


cbn in q.

  
  Check (∏ (j : homot_label Σ)
           (x : ⦃ homot_point_arg Σ j ⦄ (pr11 X) : type_chaotic_bicat)
           (p : endpoint_type_unit (homot_path_arg_left Σ j) (pr1 X) x
                =
                endpoint_type_unit (homot_path_arg_right Σ j) (pr1 X) x),
         homot_endpoint_types_unit (homot_left_path Σ j) (pr1 X) (pr2 X) x p
         =
         homot_endpoint_types_unit (homot_right_path Σ j) (pr1 X) (pr2 X) x p).
  
