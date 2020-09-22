(* Adding points to the bicategory of types, functions and equality *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Require Import Integers.Prebicategories.DispPrebicat.
Require Import Integers.TypePrebicat.type_prebicat.

Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.



(* Pointtypes as displayed prebicategory *)
Definition pointtypes_disp_data : disp_prebicat_data type_prebicat.
Proof.
  use tpair.
  - use tpair.
    + use tpair.
      * use make_disp_cat_ob_mor.
        -- exact (λ X, X).
        -- exact (λ X Y x y f, f x = y).
      * use tpair.
        -- exact (λ X x, idpath x).
        -- exact (λ X Y Z f g x y z ff gg, maponpaths g ff @ gg).
    + exact (λ X Y f g p x y ff gg, maponpaths (λ h, h x) p @ gg = ff).
  - cbn.
    repeat split; cbn.
    + exact (λ X Y f x y p, !pathscomp0rid _ @ maponpaths_2 _ (!maponpathsidfun p) _).
    + exact (λ X Y f x y p, pathscomp0rid _ @ maponpathsidfun p).
    + exact (λ X Y Z W f g h x y z w p q r, maponpaths_2 _ (!maponpathscomp g h p) _ @ path_assoc _ _ _ @ (maponpaths_2 _  (!maponpathscomp0 h _ _) _)).
    + exact (λ X Y Z W f g h x y z w p q r, maponpaths_2 _ (maponpathscomp0 _ _ _) _ @ !path_assoc _ _ _ @ maponpaths_2 _ (maponpathscomp g h p) _).
    + intros X Y f g h p q x y ff gg hh pp qq.
      refine (_ @ _ @ _ @ _).
      * apply maponpaths_2.
        exact (maponpathscomp0 (λ h0 : X → Y, h0 x) p q).
      * exact (!path_assoc _ _ _).
      * apply maponpaths.
        exact qq.
      * exact pp.
    + intros X Y Z f g h p x y z ff gg hh pp.
      refine (_ @ _ @ _ @ _ @ _).
      * apply maponpaths_2.
        exact (maponpathscomp (λ k : Y → Z, (k ∘ f)%functions) (λ h0 : X → Z, h0 x) p).
      * apply path_assoc.
      * apply maponpaths_2.
        exact (!homotsec_natural (happly p) ff).
      * exact (!path_assoc _ _ _).
      * apply maponpaths.
        exact pp.
    + intros X Y Z f g h p x y z ff gg hh pp.
      etrans.
      { apply path_assoc. }
      apply maponpaths_2.
      refine (_ @ !(_ @ _ @ _)).
      * apply maponpaths_2.
        exact (maponpathscomp (λ k, _) (λ k, k x) p).
      * apply maponpaths.
        exact (!pp).
      * exact (maponpathscomp0 h _ gg).
      * apply maponpaths_2.
        exact (maponpathscomp (λ k, k x) h p).
Defined.

Definition pointtypes_disp : disp_prebicat type_prebicat.
Proof.
  use tpair.
  - exact pointtypes_disp_data.
  - unfold disp_prebicat_laws.
    repeat split.
    + intros X Y f g p x y ff gg pp. cbn in * |-.
      induction p.
      refine (!(_ @ _ @ _)).
      * apply maponpaths_2.
        unfold id2_left.
Abort.
