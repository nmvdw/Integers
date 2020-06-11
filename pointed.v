Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.Type.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

(**
The scope `cat` allows one to write `x --> y` for the morphisms from `x` to `y`.
In addition, you can write `f · g` for the composition (compositional order).
The identity morphism is denoted by `identity`.
 *)
Local Open Scope cat.

(**
The scope `mor_disp` contains notation for displayed categories.
It introduces the notation `xx -->[ f ] yy` for displayed morphisms over `f` from `xx` to `yy`.
The displayed identity is denoted by `id_disp`.
 *)
Local Open Scope mor_disp.

(**
The precategory `type_precat` has types as objects and functions as morphisms and it is defined already in UniMath.
We will use this category in the remainder of the formalization.
To illustrate the definition of a precategory, we repeat how this category is defined.
 *)
Definition TYPE_data : precategory_data.
Proof.
  use make_precategory_data.
  - use make_precategory_ob_mor.
    + exact Type.
    + exact (λ X Y, X → Y).
  - exact (λ X x, x).
  - exact (λ X Y Z f g x, g(f x)).
Defined.

Definition TYPE_is_precategory
  : is_precategory TYPE_data.
Proof.
  use make_is_precategory.
  - exact (λ X Y f, idpath _).
  - exact (λ X Y f, idpath _).
  - exact (λ W X Y Z f g h, idpath _).
  - exact (λ W X Y Z f g h, idpath _).
Defined.

Definition TYPE : precategory.
Proof.
  use make_precategory.
  - exact TYPE_data.
  - exact TYPE_is_precategory.
Defined.

(**
Next we look at displayed precategories.
Note that for these, we don't want the displayed morphisms to be a set.
The definition is copied from UniMath (from `disp_cat_axioms`).

Note the type of
- `transportb : ∏ (X : UU) (P : X → UU) (x x' : X), x = x' → P x' → P x`
- `transportf : ∏ (X : UU) (P : X → UU) (x x' : X), x = x' → P x → P x'`
`transportf` corresponds to `transport` in the HoTT book.
`transportb P p x` is an abbreviation for `transportf P (!p) x`.
 *)
Definition disp_precat_axioms
           {C : precategory}
           (D : disp_cat_data C)
  : UU
:= (∏ x y (f : x --> y) (xx : D x) yy (ff : xx -->[f] yy),
     id_disp _ ;; ff
     =
     transportb _ (id_left _) ff)
   × (∏ x y (f : x --> y) (xx : D x) yy (ff : xx -->[f] yy),
     ff ;; id_disp _
     =
     transportb _ (id_right _) ff)
   × (∏ x y z w f g h (xx : D x) (yy : D y) (zz : D z) (ww : D w)
        (ff : xx -->[f] yy) (gg : yy -->[g] zz) (hh : zz -->[h] ww),
     ff ;; (gg ;; hh)
     =
     transportb _ (assoc _ _ _) ((ff ;; gg) ;; hh)).

Definition disp_precat
           (C : precategory)
  := ∑ (D : disp_cat_data C), disp_precat_axioms D.

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
Defined.

Definition disp_point
  : disp_precat type_precat.
Proof.
  use tpair.
  - exact disp_point_data.
  - exact disp_point_axioms.
Defined.

(**
Similarly, we define a displayed precategory which adds an endomorphism to the structure.
 *)
Definition disp_end_data
  : disp_cat_data type_precat.
Proof.
  use tpair.
  - use make_disp_cat_ob_mor.
    + exact (λ X, X → X).
    + exact (λ X Y hX hY f, ∏ (x : X), f(hX x) = hY(f x)).
  - split.
    + exact (λ X f x, idpath _).
    + exact (λ X Y Z f g hX hY hZ p q x, maponpaths g (p x) @ q _).
Defined.

Definition disp_end_axioms
  : disp_precat_axioms disp_end_data.
Proof.
  simple refine (_ ,, _ ,, _).
  - cbn ; unfold idfun.
    intros X Y f hX hY p.
    apply idpath.
  - cbn ; unfold idfun.
    intros X Y f hX hY p.
    use funextsec ; intro x.
    exact (pathscomp0rid _ @ maponpathsidfun _).
  - cbn ; unfold idfun.
    intros W X Y Z f g h hW hX hY hZ p q r.
    use funextsec ; intro x.
    refine (path_assoc _ _ _ @ _).
    apply maponpaths_2.
    refine (_ @ !(maponpathscomp0 h _ _)).
    apply maponpaths_2.
    refine (!_).
    exact (maponpathscomp g h _).
Defined.

Definition disp_end
  : disp_precat type_precat.
Proof.
  use tpair.
  - exact disp_end_data.
  - exact disp_end_axioms.
Defined.
