(*
 - Paths from homotopy endpoints
 - Prebicategory of prealgebras (PreAlg)
 - Projections and builders for PreAlg
 - Prebicategory of path algebras (PathAlg)
 - Projections and builders for PathAlg
 - Prebicategory of HIT algebras (Alg)
 - Projections and builders for Alg*
From 'GrpdHITs/code/algebra/one_types_homotopies.v'
 *: not complete Qed is too slow on one of the projections
*)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Require Import sem.prelude.basics.

Require Import Integers.Prebicategories.DispPrebicat.
Require Import Integers.Prebicategories.PseudoFunctor.
Require Import Integers.Prebicategories.PseudoTransformation.
Require Import Integers.Prebicategories.Composition.
Require Import Integers.Prebicategories.Projection.
Require Import Integers.Prebicategories.Algebra.
Require Import Integers.Prebicategories.DispDepProd.
Require Import Integers.Prebicategories.AddEndpoints.
Require Import Integers.Prebicategories.FullSub.
Require Import Integers.signature.
Require Import Integers.type_prebicat.
Require Import Integers.Algebra.polynomials.
Require Import Integers.Algebra.endpoints.

Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.

(** Paths from homotopy endpoints **)
Definition homot_endpoint_type
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ j : J, endpoint A (S j) Id}
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
  : endpoint_type sl X z = endpoint_type sr X z
  := sem_homot_endpoint_UU p (pr1 X) (pr2 X) pX z p_arg.

(** Prebicategory of prealgebras (PreAlg) *)
Definition hit_prealgebra_type (Σ : hit_signature) : prebicat
  := total_prebicat (disp_alg_prebicat ⦃ point_constr Σ ⦄).

(** Projections and builders for PreAlg *)
Section HITPreAlgebraProjections.
  Context {Σ : hit_signature}
          (X : hit_prealgebra_type Σ).

  Definition prealg_carrier : type_prebicat := pr1 X.

  Definition prealg_constr
    : act (point_constr Σ) prealg_carrier → prealg_carrier
    := pr2 X.
End HITPreAlgebraProjections.

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

(** Prebicategory of path algebras (PathAlg) **)
(* Takes long to check (about 2.5 min in my case) *)
Definition hit_path_algebra_disp_type
           (Σ : hit_signature)
  : disp_prebicat (hit_prealgebra_type Σ)
  := disp_depprod_prebicat
       (path_label Σ)
       (λ j, add_path_endpoints_prebicat
               (disp_alg_prebicat ⦃ point_constr Σ ⦄)
               ⦃ path_source Σ j ⦄
               (endpoint_type (path_left Σ j))
               (endpoint_type (path_right Σ j))).

Definition hit_path_algebra_type
           (Σ : hit_signature)
  : prebicat
  := total_prebicat (hit_path_algebra_disp_type Σ).

(** Projections and builders for PathAlg *)
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

Definition make_hit_path_algebra
           {Σ : hit_signature}
           (X : hit_prealgebra_type Σ)
           (pX : ∏ (j : path_label Σ)
                   (x : act (path_source Σ j) (prealg_carrier X)),
                 endpoint_type (path_left Σ j) _ x
                 =
                 endpoint_type (path_right Σ j) _ x)
  : hit_path_algebra_type Σ
  := X,, pX.

Definition preserves_path
           {Σ : hit_signature}
           {X Y : hit_path_algebra_type Σ}
           (f : pr1 X --> pr1 Y)
           (Hf : preserves_point (pr1 f))
  : UU
  := ∏ (j : path_label Σ)
       (x : act (path_source Σ j) (path_alg_carrier X)),
     maponpaths (prealg_map_carrier f) (path_alg_path X j x)
                @ endpoint_type_mor (path_right Σ j) Hf x
     =
     endpoint_type_mor (path_left Σ j) Hf x
                       @ path_alg_path Y j (actmap (path_source Σ j) _ x).

Section HITPathAlgebraMorProjections.
  Context {Σ : hit_signature}
          {X Y : hit_path_algebra_type Σ}
          (f : X --> Y).

  Definition path_alg_map_carrier
    : path_alg_carrier X → path_alg_carrier Y
    := prealg_map_carrier (pr1 f).

  Definition path_alg_map_commute
    : ∏ (x : act (point_constr Σ) (path_alg_carrier X)),
      path_alg_map_carrier (path_alg_constr X x)
      =
      path_alg_constr Y (actmap (point_constr Σ) path_alg_map_carrier x)
    := prealg_map_commute (pr1 f).

  (*
  Definition path_alg_map_path
    : preserves_path (pr1 f) path_alg_map_commute.
  Proof.
    intros j x.
    unfold prealg_map_carrier, path_alg_map_commute.
    unfold prealg_map_commute, path_alg_path.
    pose (eqtohomot (pr2 f j) x) as p.
    cbn in p.
    unfold homotcomp, homotfun, funhomotsec in p.
    (* goal is nu exactly equal to p *)
    exact p. (* This is quick, no more subgoals *)
  Qed. (* Qed is slow *)
   *)
End HITPathAlgebraMorProjections.

Definition make_hit_path_alg_map
           {Σ : hit_signature}
           {X Y : hit_path_algebra_type Σ}
           (f : pr1 X --> pr1 Y)
           (pf : preserves_path _ (prealg_map_commute f))
  : X --> Y
  := f,, λ i, funextsec _ _ _ (pf i).

(** Prebicategory of HIT algebras (Alg) **)
Definition is_hit_algebra_type
           (Σ : hit_signature)
           (X : hit_path_algebra_type Σ)
  : UU
  := ∏ (j : homot_label Σ)
       (x : ⦃ homot_point_arg Σ j ⦄ (pr11 X))
       (p : endpoint_type (homot_path_arg_left Σ j) (pr1 X) x
            =
            endpoint_type (homot_path_arg_right Σ j) (pr1 X) x),
     homot_endpoint_type (homot_left_path Σ j) (pr1 X) (pr2 X) x p
     =
     homot_endpoint_type (homot_right_path Σ j) (pr1 X) (pr2 X) x p.

Definition hit_algebra_type
           (Σ : hit_signature)
  : prebicat
  := fullsubprebicat (hit_path_algebra_type Σ) (is_hit_algebra_type Σ).

(** Projections and builders for Alg *)
Section HITAlgebraProjections.
  Context {Σ : hit_signature}
          (X : hit_algebra_type Σ).

  Definition alg_carrier
    : UU
    := path_alg_carrier (pr1 X).

  Definition alg_constr
    : act (point_constr Σ) alg_carrier → alg_carrier
    := @path_alg_constr _ (pr1 X).

  Definition alg_path
             (j : path_label Σ)
             (x : act (path_source Σ j) alg_carrier)
    : endpoint_type (path_left Σ j) _ x
      =
      endpoint_type (path_right Σ j) _ x
    := path_alg_path (pr1 X) j x.
  
  Definition alg_homot
    : is_hit_algebra_type Σ (pr1 X)
    := pr2 X.
End HITAlgebraProjections.

Definition make_algebra
           {Σ : hit_signature}
           (X : hit_path_algebra_type Σ)
           (hX : is_hit_algebra_type Σ X)
  : hit_algebra_type Σ
  := X ,, hX.

(** Projections of algebra maps *)
Section HITAlgebraMapProjections.
  Context {Σ : hit_signature}
          {X Y : hit_algebra_type Σ}
          (f : X --> Y).

  Definition alg_map_carrier
    : alg_carrier X → alg_carrier Y
    := path_alg_map_carrier (pr1 f).

  Definition alg_map_commute
    : preserves_point alg_map_carrier
    := path_alg_map_commute (pr1 f).

  (* needs path_alg_map_path
  Definition alg_map_path
    : preserves_path _ alg_map_commute
    := path_alg_map_path (pr1 f).*)
End HITAlgebraMapProjections.

Definition make_algebra_map
           {Σ : hit_signature}
           {X Y : hit_algebra_type Σ}
           (f : pr1 X --> pr1 Y)
  : X --> Y
  := f ,, tt.

(** Projections of algebra 2-cells *)
Section HITAlgebraCellProjections.
  Context {Σ : hit_signature}
          {X Y : hit_algebra_type Σ}
          {f g : X --> Y}
          (α : f ==> g).

  Definition alg_2cell_carrier
    : alg_map_carrier f ~ alg_map_carrier g
    := pr111 α.
End HITAlgebraCellProjections.

(** Builder of 2-cells of algebras *)
Definition make_algebra_2cell
           {Σ : hit_signature}
           {X Y : hit_algebra_type Σ}
           {f g : X --> Y}
           (α : alg_map_carrier f ~ alg_map_carrier g)
  : f ==> g
  := (((α ,, tt) ,, λ _, tt) ,, tt).
