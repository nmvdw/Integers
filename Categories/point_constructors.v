(*
 - The displayed precategory `disp_point` that adds points to types.
 - The displayed precategory `disp_end` that adds endomorphisms to types.
 - The total precategory `TYPE_point` of pointed types.
 - The total precategory `TYPE_end` of types with endomorphisms.
 - The total precategory `TYPE_point_end` of both, using the direct product of `disp_point` and `disp_end`.
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.Type.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import Integers.Categories.disp_precat.
Require Import Integers.Categories.total_precat.

Local Open Scope cat.
Local Open Scope mor_disp.

(** Displayed precategory which adds a point. *)
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

(** Displayed precategory which adds an endomorphism. **)
Definition disp_end_data
  : disp_cat_data type_precat.
Proof.
  use tpair.
  - use make_disp_cat_ob_mor.
    + exact (λ X, X → X).
    + exact (λ X Y hX hY f, ∏ (x : X),  f(hX x) = hY(f x)).
  - split.
    + exact (λ X f x, idpath _).
    + exact (λ X Y Z f g hX hY hZ p q x, maponpaths g (p x) @ q (f x)).
Defined.

Definition disp_end_axioms
  : disp_precat_axioms disp_end_data.
Proof.
  simple refine (_ ,, _ ,, _).
  - cbn ; unfold idfun.
    intros X Y f hX hY p.
    use funextsec ; intro x.
    exact (idpath (p x)).
  - cbn ; unfold idfun.
    intros X Y f hX hY p.
    use funextsec ; intro x.
    exact (pathscomp0rid _ @ maponpathsidfun (p x)).
  - cbn.
    intros W X Y Z f g h hW hX hY hZ p q r.
    use funextsec ; intro x.
    refine (_ @ _ @ _).
    + apply maponpaths_2.
      exact (!maponpathscomp g h (p x)).
    + apply path_assoc.
    + apply maponpaths_2.
      exact (!maponpathscomp0 h (maponpaths g (p x)) (q (f x))).
Qed.

Definition disp_end : disp_precat type_precat
  := disp_end_data ,, disp_end_axioms.

(** Total precategories from these displayed precategories. *)
Definition TYPE_point : precategory := total_precategory disp_point.

Definition TYPE_end : precategory := total_precategory disp_end.

(* Example: combining these *)
Definition disp_point_end : disp_precat type_precat
  := dirprod_disp_precat disp_point disp_end.

Definition TYPE_point_end : precategory := total_precategory disp_point_end.
