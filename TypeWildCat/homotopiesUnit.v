(** This uses Add2CellUnit **)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import sem.signature.hit_signature.

Require Import Integers.WildCategories.WildCat.
Require Import Integers.WildCategories.DispWildCat.
Require Import Integers.WildCategories.WildFunctor.
Import WildFunctor.Notations.
Require Import Integers.WildCategories.WildNaturalTransformation.
Require Import Integers.WildCategories.Add2CellUnit.
Require Import Integers.WildCategories.Algebra.
Require Import Integers.WildCategories.DispDepProd.
Require Import Integers.WildCategories.FullSub.
Require Import Integers.TypeWildCat.TypeWildCat.
Require Import Integers.TypeWildCat.polynomials.
Require Import Integers.TypeWildCat.endpoints.

Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.

Definition homot_endpoint_type
           {A : poly_code}
           {J : UU}
           {S : J → poly_code}
           {l r : ∏ (j : J), endpoint A (S j) I}
           {Q TR : poly_code}
           {al ar : endpoint A Q TR}
           {T : poly_code}
           {sl sr : endpoint A Q T}
           (p : homot_endpoint l r al ar sl sr)
           (X : total_wild_cat (disp_alg ⦃ A ⦄))
           (pX : ∏ (j : J),
                 endpoint_type (l j) X
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

(** Wild Category of prealgebras **)
Definition hit_prealgebra_type (Σ : hit_signature) : wild_cat
  := total_wild_cat (disp_alg ⦃ point_constr Σ ⦄).

(** Projections and builders of prealgebras **)
Definition prealg_carrier {Σ : hit_signature} (X : hit_prealgebra_type Σ)
  : UU := pr1 X.

Definition prealg_constr {Σ : hit_signature} {X : hit_prealgebra_type Σ}
  : act (point_constr Σ) (prealg_carrier X) → prealg_carrier X
  := pr2 X.

Definition make_hit_prealgebra
           {Σ : hit_signature}
           (X : UU)
           (f : act (point_constr Σ) X → X)
  : hit_prealgebra_type Σ
  := X ,, f.

Definition preserves_point
           {Σ : hit_signature}
           {X Y : hit_prealgebra_type Σ}
           (f : prealg_carrier X → prealg_carrier Y)
  : UU
  := ∏ (x : act (point_constr Σ) (prealg_carrier X)),
     f (prealg_constr x)
     =
     prealg_constr (actmap (point_constr Σ) f x).

Definition prealg_map_carrier
           {Σ : hit_signature}
           {X Y : hit_prealgebra_type Σ}
           (f : X --> Y)
  : prealg_carrier X → prealg_carrier Y
  := pr1 f.

Definition prealg_map_commute
           {Σ : hit_signature}
           {X Y : hit_prealgebra_type Σ}
           (f : X --> Y)
  : preserves_point (prealg_map_carrier f)
  := pr12 f.

Definition make_hit_prealgebra_mor
           {Σ : hit_signature}
           {X Y : hit_prealgebra_type Σ}
           (f : prealg_carrier X → prealg_carrier Y)
           (Hf : preserves_point f)
  : X --> Y.
Proof.
  use tpair.
  - exact f.
  - use make_invertible_2cell.
    + exact Hf.
    + exact (invhomot Hf).
Defined.

(** Path Algebras for a HIT signature **)
(* from here on, we use Add2CellUnit *)
Definition hit_path_algebra_disp (Σ : hit_signature)
  : disp_wild_cat (hit_prealgebra_type Σ)
  := (disp_depprod (path_label Σ)
                   (λ j, disp_add_cell
                           _ _
                           (endpoint_type (path_left Σ j))
                           (endpoint_type (path_right Σ j)) )).

Definition hit_path_algebra (Σ : hit_signature)
  : wild_cat
  := total_wild_cat (hit_path_algebra_disp Σ).

(** Projections **)
Section HITPathAlgebraProjections.
  Context {Σ : hit_signature}
          (X : hit_path_algebra Σ).

  Definition path_alg_carrier : UU := prealg_carrier (pr1 X).

  Definition path_alg_constr
    : act (point_constr Σ) path_alg_carrier → path_alg_carrier
    := @prealg_constr _ (pr1 X).

  
  Definition path_alg_path
             (j : path_label Σ)
             (x : act (path_source Σ j) path_alg_carrier)
    : endpoint_type (path_left Σ j) (pr1 X) x = endpoint_type (path_right Σ j) (pr1 X) x
    := pr2 X j x.
End HITPathAlgebraProjections.

Arguments path_alg_constr {_ _} _.

Definition make_hit_path_algebra
           {Σ : hit_signature}
           (X : hit_prealgebra_type Σ)
           (pX : ∏ (j : path_label Σ)
                   (x : act (path_source Σ j) (prealg_carrier X)),
                 endpoint_type (path_left Σ j) _ x
                 =
                 endpoint_type (path_right Σ j) _ x)
  : hit_path_algebra Σ
  := X ,, pX.

Definition preserves_path
           {Σ : hit_signature}
           {X Y : hit_path_algebra Σ}
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
          {X Y : hit_path_algebra Σ}
          (f : X --> Y).

  Definition path_alg_map_carrier
    : path_alg_carrier X → path_alg_carrier Y
    := prealg_map_carrier (pr1 f).

  Definition path_alg_map_commute
    : ∏ (x : act (point_constr Σ) (path_alg_carrier X)),
      path_alg_map_carrier (path_alg_constr x)
      =
      path_alg_constr (actmap (point_constr Σ) path_alg_map_carrier x)
    := prealg_map_commute (pr1 f).

  (*
  Definition path_alg_map_path
    : preserves_path (pr1 f) path_alg_map_commute.
  Proof.
    unfold preserves_path.
    intros j x.    
    pose (pr2 f j) as p.
    cbn in p.


    Check ((pr2 f)).
      := λ j x, eqtohomot (pr2 f j) x.
   *)
End HITPathAlgebraMorProjections.

Definition make_hit_alg_map
           {Σ : hit_signature}
           {X Y : hit_path_algebra Σ}
           (f : pr1 X --> pr1 Y)
           (pf : preserves_path _ (prealg_map_commute f))
  : X --> Y
  := f ,, λ j, tt.

(** HIT algebras **)
Definition is_hit_algebra
           (Σ : hit_signature)
           (X : hit_path_algebra Σ)
  : UU
  := ∏ (j : homot_label Σ)
       (x : ⦃ homot_point_arg Σ j ⦄ (pr11 X))
       (p : endpoint_type (homot_path_arg_left Σ j) (pr1 X) x
            =
            endpoint_type (homot_path_arg_right Σ j) (pr1 X) x),
     homot_endpoint_type (homot_left_path Σ j) (pr1 X) (pr2 X) x p
     =
     homot_endpoint_type (homot_right_path Σ j) (pr1 X) (pr2 X) x p.

Definition hit_algebra
           (Σ : hit_signature)
  : wild_cat
  := full_sub_wild_cat (hit_path_algebra Σ) (is_hit_algebra Σ).

(** Projections **)
Section HITAlgebraProjections.
  Context {Σ : hit_signature}
          (X : hit_algebra Σ).

  Definition alg_carrier : UU
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
    : is_hit_algebra Σ (pr1 X)
    := pr2 X.
End HITAlgebraProjections.

Definition make_algebra
           {Σ : hit_signature}
           (X : hit_path_algebra Σ)
           (hX : is_hit_algebra Σ X)
  : hit_algebra Σ
  := X ,, hX.

(** Projections of algebra maps **)
Section HITAlgebraMapProjections.
  Context {Σ : hit_signature}
          {X Y : hit_algebra Σ}
          (f : X --> Y).

  Definition alg_map_carrier
    : alg_carrier X → alg_carrier Y
    := path_alg_map_carrier (pr1 f).

  Definition alg_map_commute
    : preserves_point alg_map_carrier
    := path_alg_map_commute (pr1 f).

  (*
  Definition alg_map_path
    : preserves_path _ alg_map_commute
    := path_alg_map_path (pr1 f).
  *)
End HITAlgebraMapProjections.

Definition make_algebra_map
           {Σ : hit_signature}
           {X Y : hit_algebra Σ}
           (f : pr1 X --> pr1 Y)
  : X --> Y
  := f ,, tt.

Definition is_algebra_2cell
           {Σ : hit_signature}
           {X Y : hit_algebra Σ}
           {f g : X --> Y}
           (θ : alg_map_carrier f ~ alg_map_carrier g)
  : UU
  := ∏ (z : act (point_constr Σ) (alg_carrier X)),
     θ (alg_constr X z) @ alg_map_commute g z
     =
     alg_map_commute f z @ maponpaths (alg_constr Y) (poly_homot (point_constr Σ) θ z).

(** Projections of algebra 2-cells **)
Section HITAlgebraCellProjections.
  Context {Σ : hit_signature}
          {X Y : hit_algebra Σ}
          {f g : X --> Y}
          (θ : f ==> g).

  Definition alg_2cell_carrier
    : alg_map_carrier f ~ alg_map_carrier g
    := pr111 θ.

  (*
  Definition alg_2cell_commute
    : is_algebra_2cell alg_2cell_carrier.
  Proof.
    exact (eqhomot (pr211 θ)).
  Defined.*)
End HITAlgebraCellProjections.

(** Equality of algebra 2-cells *)
Definition algebra_2cell_eq
           {Σ : hit_signature}
           {X Y : hit_algebra Σ}
           {f g : X --> Y}
           {θ γ : f ==> g}
           (p : alg_2cell_carrier θ ~ alg_2cell_carrier γ)
  : θ = γ.
Proof.
  use subtypePath.
  { intro. apply isapropunit. }
  use subtypePath.
  { intro. use impred. intro. apply isapropunit. }
  use subtypePath.
  { intro. apply isapropunit. }
  exact (funextsec _ _ _ p).
Qed.

Definition alg_2cell_eq_component
           {Σ : hit_signature}
           {X Y : hit_algebra Σ}
           {f g : X --> Y}
           {θ γ : f ==> g}
           (p : θ = γ)
  : alg_2cell_carrier θ ~ alg_2cell_carrier γ
  := eqtohomot (maponpaths (λ z, pr111 z) p).

(** Builder of 2-cells of algebras **)
Definition make_algebra_2cell
           {Σ : hit_signature}
           {X Y : hit_algebra Σ}
           {f g : X --> Y}
           (θ : alg_map_carrier f ~ alg_map_carrier g)
  : f ==> g
  := ((θ ,, tt) ,, (λ j, tt)) ,, tt.
