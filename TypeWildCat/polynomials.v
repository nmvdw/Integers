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
Require Import Integers.TypeWildCat.TypeWildCat.

Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.

(** Preliminary **)

(* For coproduct *)
Definition coprodf_path
           {X1 X2 Y1 Y2 : UU}
           {f1 g1 : X1 → Y1}
           {f2 g2 : X2 → Y2}
           (p1 : f1 ~ g1)
           (p2 : f2 ~ g2)
           (x : X1 ⨿ X2)
  : coprodf f1 f2 x = coprodf g1 g2 x.
Proof.
  induction x as [x | x].
  - exact (maponpaths inl (p1 x)).
  - exact (maponpaths inr (p2 x)).
Defined.

Definition coprodf_id
           {X Y : UU}
           (x : X ⨿ Y)
  : coprodf (λ z, z) (λ z, z) x = x.
Proof.
  induction x as [x | x].
  - exact (idpath (inl x)).
  - exact (idpath (inr x)).
Defined.

Definition coprodf_comp
           {X1 X2 Y1 Y2 Z1 Z2 : UU}
           (f1 : X1 → Y1)
           (g1 : Y1 → Z1)
           (f2 : X2 → Y2)
           (g2 : Y2 → Z2)
           (x : X1 ⨿ X2)
  : (coprodf (g1 ∘ f1)%functions (g2 ∘ f2)%functions x
     =
     (coprodf g1 g2) (coprodf f1 f2 x))%functions.
Proof.
  induction x as [x | x].
  - exact (idpath (inl (g1 (f1 x)))).
  - exact (idpath (inr (g2 (f2 x)))).
Defined.

(* For product *)
Definition dirprodf_path
           {X1 X2 Y1 Y2 : UU}
           {f1 g1 : X1 → Y1}
           {f2 g2 : X2 → Y2}
           (p1 : f1 ~ g1)
           (p2 : f2 ~ g2)
           (x : X1 × X2)
  : dirprodf f1 f2 x = dirprodf g1 g2 x
  := pathsdirprod (p1 (pr1 x)) (p2 (pr2 x)).

Definition dirprodf_id
           {X Y : UU}
           (x : X × Y)
  : dirprodf (λ z, z) (λ z, z) x = x
  := pathsdirprod (idpath (pr1 x)) (idpath (pr2 x)).

Definition dirprodf_comp
           {X1 X2 Y1 Y2 Z1 Z2 : UU}
           (f1 : X1 → Y1)
           (g1 : Y1 → Z1)
           (f2 : X2 → Y2)
           (g2 : Y2 → Z2)
           (x : X1 × X2)
  : (dirprodf (g1 ∘ f1)%functions (g2 ∘ f2)%functions x
     =
     (dirprodf g1 g2) (dirprodf f1 f2 x))%functions
  := pathsdirprod (idpath (g1 (f1 (pr1 x)))) (idpath (g2 (f2 (pr2 x)))).



(* Polynomial acts on universe *)
Definition act (P : poly_code) (A : UU) : UU.
Proof.
  induction P as [X | | | ].
  - exact X.
  - exact A.
  - exact (IHP1 ⨿ IHP2).
  - exact (IHP1 × IHP2).
Defined.

Definition actmap (P : poly_code) {A B : UU} (f : A → B)
  : type_wild_cat ⟦ act P A, act P B ⟧.
Proof.
  cbn.
  induction P as [X | | | ].
  - exact (λ y, y).
  - exact f.
  - exact (coprodf IHP1 IHP2).
  - exact (dirprodf IHP1 IHP2).
Defined.

Definition poly_homot
           (P : poly_code)
           {X Y : UU}
           {f g : X → Y}
           (p : f ~ g)
  : actmap P f ~ actmap P g.
Proof.
  induction P.
  - exact (λ a, idpath a).
  - exact p.
  - exact (coprodf_path IHP1 IHP2).
  - exact (dirprodf_path IHP1 IHP2).
Defined.

Definition poly_comp
           (P : poly_code)
           {X Y Z : UU}
           (f : X → Y) (g : Y → Z)
  : actmap P g ∘ actmap P f ~ actmap P (g ∘ f)%functions.
Proof.
  induction P as [A | | | ].
  - exact (λ a, idpath a).
  - exact (λ z, idpath (g(f z))).
  - intro x.
    refine (!coprodf_comp _ _ _ _ x @ _).
    exact (coprodf_path IHP1 IHP2 x).
  - intro x.
    refine (!dirprodf_comp _ _ _ _ x @ _).
    exact (dirprodf_path IHP1 IHP2 x).
Defined.

(* The wild functor *)
Definition poly_type (P : poly_code)
  : wild_functor type_wild_cat type_wild_cat.
Proof.
  use make_wild_functor.
  - exact (act P).
  - exact (λ a b f, actmap P f).
  - cbn. intros a b f g θ.
    induction P as [X | | | ].
    + exact (λ x, idpath x).
    + exact θ.
    + exact (coprodf_path IHP1 IHP2).
    + exact (dirprodf_path IHP1 IHP2).
  - cbn. intros a.
    induction P as [X | | | ].
    + use make_invertible_2cell.
      * exact (λ x, idpath x).
      * exact (λ x, idpath x).
    + use make_invertible_2cell.
      * exact (λ x, idpath x).
      * exact (λ x, idpath x).
    + pose (cell_from_invertible_2cell IHP1) as IHP1c.
      pose (cell_from_invertible_2cell IHP2) as IHP2c.
      use make_invertible_2cell.
      * exact (λ x, !coprodf_id x @ coprodf_path IHP1c IHP2c x).
      * exact (λ x, !coprodf_path IHP1c IHP2c x @ coprodf_id x).
    + pose (cell_from_invertible_2cell IHP1) as IHP1c.
      pose (cell_from_invertible_2cell IHP2) as IHP2c.
      use make_invertible_2cell.
      * exact (λ x, !dirprodf_id x @ dirprodf_path IHP1c IHP2c x).
      * exact (λ x, !dirprodf_path IHP1c IHP2c x @ dirprodf_id x).
  - cbn. intros a b c f g.
    induction P as [X | | | ].
     + use make_invertible_2cell.
      * exact (λ x, idpath x).
      * exact (λ x, idpath x).
    + use make_invertible_2cell.
      * exact (λ x, idpath (g (f x))).
      * exact (λ x, idpath (g (f x))).
    + pose (cell_from_invertible_2cell IHP1) as IHP1c.
      pose (cell_from_invertible_2cell IHP2) as IHP2c.
      use make_invertible_2cell.
      * exact (λ x, !coprodf_comp _ _ _ _ x @ coprodf_path IHP1c IHP2c x).
      * exact (λ x, !coprodf_path IHP1c IHP2c x @ coprodf_comp _ _ _ _ x).
    + pose (cell_from_invertible_2cell IHP1) as IHP1c.
      pose (cell_from_invertible_2cell IHP2) as IHP2c.
      use make_invertible_2cell.
      * exact (λ x, !dirprodf_comp _ _ _ _ x @ dirprodf_path IHP1c IHP2c x).
      * exact (λ x, !dirprodf_path IHP1c IHP2c x @ dirprodf_comp _ _ _ _ x).
Defined.

Notation "⦃ P ⦄" := (poly_type P).
