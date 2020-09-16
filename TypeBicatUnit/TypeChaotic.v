(* The bicategory of types, created using chaotic bicategories *)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.

Definition type_chaotic_precat : precategory.
Proof.
  use make_precategory.
  - use make_precategory_data.
    + use make_precategory_ob_mor.
      * exact Type.
      * intros X Y.
        exact (X → Y).
    + exact (λ X x, x).
    + cbn. intros X Y Z f g x.
      exact (g (f x)).
  - repeat split.
Defined.

Definition type_chaotic_bicat : bicat := chaotic_bicat type_chaotic_precat.

Lemma chaotic_invertible_2cell
      {a b : type_chaotic_bicat}
      {f g : a --> b}
      {θ : f ==> g}
  : is_invertible_2cell θ.
Proof.
  use tpair.  
  - exact tt.
  - split; exact (idpath tt).
Qed.
   

Lemma chaotic_invertible_2cell0 {a b : type_chaotic_bicat} {f g : a --> b}
  : invertible_2cell f g.
Proof.
  use tpair.  
  - exact tt.
  - use tpair.
    + exact tt.
    + split; exact (idpath tt).
Qed.


(* pointtypes using chaotic displayed bicategories *)
Definition pointtypes_disp : disp_bicat type_chaotic_bicat.
Proof.
  apply disp_cell_unit_bicat.
  - use tpair.
    + use make_disp_cat_ob_mor.
      * exact (λ X, X).
      * exact (λ X Y x y f, f x = y).
    + use tpair.
      * exact (λ X x, idpath x).
      * exact (λ X Y Z f g x y z p q, maponpaths g p @ q).
Defined.

Definition pointtypes : bicat := total_bicat pointtypes_disp.

(* pointtypes using chaotic displayed bicategories *)
Definition endtypes_disp : disp_bicat type_chaotic_bicat.
Proof.
  apply disp_cell_unit_bicat.
  - use tpair.
    + use make_disp_cat_ob_mor.
      * exact (λ X, X → X).
      * exact (λ X Y s r f, ∏ x, f (s x) = r (f x)).
    + use tpair.
      * exact (λ X s x, idpath (s x)).
      * exact (λ X Y Z f g s r t p q x, maponpaths g (p x) @ q (f x)).
Defined.

Definition endtypes : bicat := total_bicat endtypes_disp.
