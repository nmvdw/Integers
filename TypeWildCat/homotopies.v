
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
Require Import Integers.WildCategories.Add2Cell.
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

(** comp and id for disp_add_cell *)
(*
??: Not in def 2.1 but in Bicat.v
B: line of Bicat.v
L: line of BicategoryLaws.v
PF: PseudoFunctor.v
PT: PseudoTransformation.v

PT   pstrans_id_alt
PF   psfunctor_id2
13a  id2_left
13b  id2_right
13c  vassocr
??   vcomp_whisker
B586 vassocl
17   vcomp_runitor
B1207 linunitor_natural
L81  lwhisker_hcomp

PT   pstrans_comp_alt
20!  rwhisker_rwhisker
18   lwhisker_lwhisker
15b! rwhisker_vcomp
B843 rwhisker_lwhisker_rassociator
14b! lwhisker_vcomp
*)
(*Definition twc_*)



(*Check (λ (Σ : hit_signature) (j : path_label Σ),
       disp_add_cell _ _ (endpoint_type (path_left Σ j))
                     (endpoint_type (path_right Σ j)) _ _).*)
(*
Definition add_cell_id (Σ : hit_signature) (j : path_label Σ)
  : ∏ (Aa : total_wild_cat (disp_alg ⦃ point_constr Σ ⦄))
        (α : wild_cat_cells type_wild_cat (endpoint_type (path_left Σ j) Aa)
               (endpoint_type (path_right Σ j) Aa)),
        (α ▹ id₁ (pr1 Aa)) • wild_nat_trans_morphisms (endpoint_type (path_right Σ j)) (id₁ Aa) =
        wild_nat_trans_morphisms (endpoint_type (path_left Σ j)) (id₁ Aa)
        • (Functors.functor_on_morphisms ⦃ path_source Σ j ⦄ (id₁ (pr1 Aa)) ◃ α).
Proof.
 intros Aa α. cbn in Aa, α. simpl.





 
 
Definition add_cell_comp (Σ : hit_signature) (j : path_label Σ)
  :  ∏ (Aa Bb Cc : total_wild_cat (disp_alg ⦃ point_constr Σ ⦄))
        (f : total_wild_cat (disp_alg ⦃ point_constr Σ ⦄) ⟦ Aa, Bb ⟧)
        (g : total_wild_cat (disp_alg ⦃ point_constr Σ ⦄) ⟦ Bb, Cc ⟧)
        (α : wild_cat_cells type_wild_cat (endpoint_type (path_left Σ j) Aa)
               (endpoint_type (path_right Σ j) Aa))
        (β : wild_cat_cells type_wild_cat (endpoint_type (path_left Σ j) Bb)
               (endpoint_type (path_right Σ j) Bb))
        (γ : wild_cat_cells type_wild_cat (endpoint_type (path_left Σ j) Cc)
               (endpoint_type (path_right Σ j) Cc)),
        (α ▹ pr1 f) • wild_nat_trans_morphisms (endpoint_type (path_right Σ j)) f =
        wild_nat_trans_morphisms (endpoint_type (path_left Σ j)) f
        • (Functors.functor_on_morphisms ⦃ path_source Σ j ⦄ (pr1 f) ◃ β)
        → (β ▹ pr1 g) • wild_nat_trans_morphisms (endpoint_type (path_right Σ j)) g =
          wild_nat_trans_morphisms (endpoint_type (path_left Σ j)) g
          • (Functors.functor_on_morphisms ⦃ path_source Σ j ⦄ (pr1 g) ◃ γ)
          → (α ▹ pr1 f · pr1 g) • wild_nat_trans_morphisms (endpoint_type (path_right Σ j)) (f · g) =
            wild_nat_trans_morphisms (endpoint_type (path_left Σ j)) (f · g)
            • (Functors.functor_on_morphisms ⦃ path_source Σ j ⦄ (pr1 f · pr1 g) ◃ γ).
Proof.
  intros Aa Bb Cc f g α β γ ff gg.
  cbn in ff, gg.
  simpl.
  unfold lassociator, rassociator.
  simpl.
*)
  
(** Path Algebras for a HIT signature **)
(*Definition hit_path_algebra_disp (Σ : hit_signature)
  : disp_wild_cat (hit_prealgebra_type Σ)
  := (disp_depprod (path_label Σ)
                   (λ j, disp_add_cell
                           _ _
                           (endpoint_type (path_left Σ j))
                           (endpoint_type (path_right Σ j)) _ _)). *)
