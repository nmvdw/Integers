Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.Type.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import Integers.disp_precat.
Require Import Integers.total_precat.

Local Open Scope cat.
Local Open Scope mor_disp.

(**
We define a displayed precategory on types, which adds a point.
We do this in 2 steps: first we define the data and then we prove the axioms.
 *)
Definition disp_point_data
  : disp_cat_data type_precat.
Proof.
  use tpair.
  - use make_disp_cat_ob_mor.
    + exact (λ X, X).
    + exact (λ X Y x y f, f x = y).
  - split.
    + exact (λ X x, idpath _).
    + exact (λ X Y Z f g x y z p q, maponpaths g p @ q).
Defined.

Definition disp_point_axioms
  : disp_precat_axioms disp_point_data.
Proof.
  simple refine (_ ,, _ ,, _).
  - cbn ; unfold idfun.
    intros X Y f x y p.
    apply idpath.
  - cbn ; unfold idfun.
    intros X Y f x y p.
    exact (pathscomp0rid _ @ maponpathsidfun _).
  - cbn ; unfold idfun.
    intros W X Y Z f g h w x y z p q r.
    refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    refine (_ @ !(maponpathscomp0 h _ q)).
    apply maponpaths_2.
    refine (!_).
    exact (maponpathscomp g h p).
Qed.

Definition disp_point : disp_precat type_precat
  := disp_point_data ,, disp_point_axioms.

(**
Similarly, we define a displayed precategory which adds an endomorphism to the structure.
 *)
Definition disp_end_data
  : disp_cat_data type_precat.
Proof.
  use tpair.
  - use make_disp_cat_ob_mor.
    + exact (λ X, X → X).
    + exact (λ X Y hX hY f, ∏ (x : X), hY(f x) = f(hX x)). (* f(hX x) = hY(f x) *)
  - split.
    + exact (λ X f x, idpath _).
    + exact (λ X Y Z f g hX hY hZ p q x, q (f x) @ maponpaths g (p x)).
Defined.

Definition disp_end_axioms
  : disp_precat_axioms disp_end_data.
Proof.
  simple refine (_ ,, _ ,, _).
  - cbn ; unfold idfun.
    intros X Y f hX hY p.
    use funextsec ; intro x.
    exact (pathscomp0rid (p x) @ idpath (p x)).
  - cbn ; unfold idfun.
    intros X Y f hX hY p.
    use funextsec ; intro x.
    exact (maponpathsidfun (p x)).
  - cbn.
    intros W X Y Z f g h hW hX hY hZ p q r.
    use funextsec ; intro x.
    refine (!_ @ !_ @ !_).
    + apply path_assoc.
    + apply maponpaths.
      apply maponpaths.
      exact ( maponpathscomp g h (p x)).
    + apply maponpaths.
      exact (maponpathscomp0 h (q (f x)) (maponpaths g (p x))).
Qed.

Definition disp_end : disp_precat type_precat
  := disp_end_data ,, disp_end_axioms.

(**
Example: The precategories `TYPE_point` and `TYPE_end` are the total precategories of their disp_ counterparts
 *)
Definition TYPE_point : precategory := total_precategory disp_point.

Definition TYPE_end : precategory := total_precategory disp_end.


(**
We can create the displayed precategory which adds a point and an endomorphism as the product of `disp_end` and `disp_type`.
 *)
Definition disp_point_end : disp_precat type_precat
  := dirprod_disp_precat disp_point disp_end.

Definition TYPE_point_end : precategory := total_precategory disp_point_end.

