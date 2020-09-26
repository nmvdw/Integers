
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import sem.signature.hit_signature.
Require Import sem.prelude.basics.

Require Import Integers.Prebicategories.DispPrebicat.
Require Import Integers.Prebicategories.PseudoFunctor.
Require Import Integers.Prebicategories.PseudoTransformation.
Require Import Integers.Prebicategories.Composition.
Require Import Integers.Prebicategories.Projection.
Require Import Integers.Prebicategories.Algebra.
Require Import Integers.Prebicategories.DispDepProd.
Require Import Integers.Prebicategories.AddEndpoints.
Require Import Integers.TypeHomot.type_homot.
Require Import Integers.TypeHomot.polynomials.
Require Import Integers.TypeHomot.endpoints.


Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.

Definition homot_endpoint_type
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) I}
           {Q TR : poly_code}
           {al ar : endpoint A Q TR}
           {T : poly_code}
           {sl sr : endpoint A Q T}
           (p : homot_endpoint l r al ar sl sr)
           (X : total_prebicat (disp_alg_prebicat ⦃ A ⦄))
           (pX : ∏ j : J, endpoint_type (l j) X
                          ~
                          endpoint_type (r j) X)
           (z : act Q (pr1 X))
           (p_arg : endpoint_type al X z = endpoint_type ar X z)
  : endpoint_type sl X z = endpoint_type sr X z.
Proof.
  induction p.
  - exact (idpath _).
  - exact (!IHp).
  - exact (IHp1 @ IHp2).
  - exact (maponpaths (endpoint_type e₃ X) IHp).
  - exact (idpath _).
  - exact (idpath _).
  - exact (idpath _).
  - exact (idpath _).
  - exact (idpath _).
  - exact (pathsdirprod IHp1 IHp2).
  - exact (idpath _).
  - exact (idpath _).
  - exact (pX j _).
  - exact p_arg.
Defined.

(** Prebicategory of prealgebras *)
Definition hit_prealgebra_type (Σ : hit_signature) : prebicat
  := total_prebicat (disp_alg_prebicat ⦃ point_constr Σ ⦄).

(** Projections and builders of prealgebras *)
Section HITPreAlgebraProjections.
  Context {Σ : hit_signature}
          (X : hit_prealgebra_type Σ).

  Definition prealg_carrier : type_prebicat := pr1 X.

  Definition prealg_constr
    : act (point_constr Σ) prealg_carrier → prealg_carrier
    := pr2 X.
End HITPreAlgebraProjections.

(*Arguments prealg_constr {_ _} _.*)

Definition make_hit_prealgebra
           {Σ : hit_signature}
           (X : UU)
           (f : act (point_constr Σ) X → X)
  : hit_prealgebra_type Σ
  := X,, f.

Definition preserves_point
           {Σ : hit_signature}
           {X Y : hit_prealgebra_type Σ}
           (f : prealg_carrier X → prealg_carrier Y) : UU
  := ∏ x : act (point_constr Σ) (prealg_carrier X),
           f (prealg_constr X x)
           =
           prealg_constr Y (actmap (point_constr Σ) f x).

Section HITPreAlgebraMorProjections.
  Context {Σ : hit_signature}
          {X Y : hit_prealgebra_type Σ}
          (f : X --> Y).

  Definition prealg_map_carrier
    : prealg_carrier X → prealg_carrier Y
    := pr1 f.

  Definition prealg_map_commute
    : preserves_point prealg_map_carrier
    := pr12 f.
End HITPreAlgebraMorProjections.

Definition make_hit_prealgebra_mor
           {Σ : hit_signature}
           {X Y : hit_prealgebra_type Σ}
           (f : prealg_carrier X → prealg_carrier Y)
           (Hf : preserves_point f)
  : X --> Y
  := f,, Hf,, type_prebicat_invertible_2cell.

(** Path Algebras for a HIT signature*)
(* Takes long to check (about 2.5 min) *)
Definition hit_path_algebra_disp_type
           (Σ : hit_signature)
  : disp_prebicat (hit_prealgebra_type Σ)
  := disp_depprod_prebicat
       (path_label Σ)
       (λ j, add_path_endpoints_prebicat
               _ _
               (endpoint_type (path_left Σ j))
               (endpoint_type (path_right Σ j))).
                  

Definition hit_path_algebra_type
           (Σ : hit_signature)
  : prebicat
  := total_prebicat (hit_path_algebra_disp_type Σ).

(** Projections *)
Section HITPathAlgebraProjections.
  Context {Σ : hit_signature}
          (X : hit_path_algebra_type Σ).

  Definition path_alg_carrier : UU
    := prealg_carrier (pr1 X).

  Definition path_alg_constr
    : act (point_constr Σ) path_alg_carrier → path_alg_carrier
    := prealg_constr (pr1 X).

  Definition path_alg_path
             (j : path_label Σ)
             (x : act (path_source Σ j) path_alg_carrier)
    : endpoint_type (path_left Σ j) (pr1 X) x
      =
      endpoint_type (path_right Σ j) (pr1 X) x
    := pr2 X j x.
End HITPathAlgebraProjections.
