Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.Type.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.


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


(**
Some more auxiliary definitions for displayed precategories.
Copied from 'DisplayedCats/Core.v', but adapted to work with our definition of categories with non-set homs. *)
Definition disp_cat_data_from_disp_precat {C} (D : disp_precat C)
 := pr1 D : disp_cat_data C.
Coercion disp_cat_data_from_disp_precat : disp_precat >-> disp_cat_data.

Definition id_left_disp {C} {D : disp_precat C}
  {x y} {f : x --> y} {xx : D x} {yy} {ff : xx -->[f] yy}
: id_disp _ ;; ff = transportb _ (id_left _) ff
:= pr1 (pr2 D) _ _ _ _ _ _.


Definition id_right_disp {C} {D : disp_precat C}
  {x y} {f : x --> y} {xx : D x} {yy} {ff : xx -->[f] yy}
  : ff ;; id_disp _ = transportb _ (id_right _) ff
:= pr1 (pr2 (pr2 D)) _ _ _ _ _ _.

Definition assoc_disp {C} {D : disp_precat C}
  {x y z w} {f} {g} {h} {xx : D x} {yy : D y} {zz : D z} {ww : D w}
  {ff : xx -->[f] yy} {gg : yy -->[g] zz} {hh : zz -->[h] ww}
: ff ;; (gg ;; hh) = transportb _ (assoc _ _ _) ((ff ;; gg) ;; hh)
 := pr2 (pr2 (pr2 D)) _ _ _ _ _ _ _ _ _ _ _ _ _ _.

(**
Definitions of total precategories, again taken from the definition of total categories of 'DisplayedCats/Core.v' and adapted.
 *)
Definition total_precategory_ob_mor {C : precategory_data} (D : disp_cat_data C)
: precategory_ob_mor.
Proof.
  use make_precategory_ob_mor.
  - exact (∑ x:C, D x).
  - intros xx yy.
    exact (∑ (f : pr1 xx --> pr1 yy), pr2 xx -->[f] pr2 yy).
Defined.

Definition total_precategory_id_comp {C : precategory_data} (D : disp_cat_data C)
  : precategory_id_comp (total_category_ob_mor D).
Proof.
  apply tpair.
  - simpl. intros c. exists (identity _). apply id_disp.
  - intros xx yy zz ff gg. simpl.
    exists (pr1 ff · pr1 gg).
    exact (pr2 ff ;; pr2 gg).
Defined.

Definition total_precategory_data {C : precategory_data} (D : disp_cat_data C) : precategory_data.
Proof.
  use make_precategory_data.
  - exact (total_category_ob_mor D).
  - exact (pr1 (total_category_id_comp D)).
  - exact (pr2 (total_category_id_comp D)).
Defined.

Lemma total_precategory_is_precat {C : precategory} (D : disp_precat C) :
  is_precategory (total_precategory_data D).
Proof.
  apply is_precategory_one_assoc_to_two.
  repeat apply tpair; simpl.
  - intros xx yy ff; cbn.
    use total2_paths_f; simpl.
    + apply id_left.
    + eapply pathscomp0.
      * apply maponpaths.
        exact id_left_disp.
      * apply transportfbinv.
  - intros xx yy ff; cbn.
    use total2_paths_f; simpl.
    + apply id_right.
    + eapply pathscomp0.
      * apply maponpaths.
        exact id_right_disp.
      * apply transportfbinv.
  - intros xx yy zz ww ff gg hh.
    use total2_paths_f; simpl.
    + apply assoc.
    + eapply pathscomp0.
      * apply maponpaths.
        exact assoc_disp.
      * apply transportfbinv.
Qed.

Definition total_precategory {C : precategory} (D : disp_precat C) : precategory :=
  (total_precategory_data D ,, total_precategory_is_precat D).

(**
Example: The precategories `TYPE_point` and `TYPE_end` are the total precategories of their disp_ counterparts
 *)
Definition TYPE_point : precategory := total_precategory disp_point.

Definition TYPE_end : precategory := total_precategory disp_end.

(**
Direct products of displayed precategories.
Copied from 'DisplayedCats/Constructions.v'
 *)
Definition dirprod_disp_precat_axioms {C : precategory} (D1 D2 : disp_precat C)
  : disp_precat_axioms (dirprod_disp_cat_data (pr1 D1) (pr1 D2)).
Proof.
  repeat apply make_dirprod.
  - intros.
    apply dirprod_paths; use (id_left_disp @ !_).
    + apply pr1_transportf.
    + apply pr2_transportf.
  - intros.
    apply dirprod_paths; use (id_right_disp @ !_).
    + apply pr1_transportf.
    + apply pr2_transportf.
  - intros. apply dirprod_paths; use (assoc_disp @ !_).
    + use pr1_transportf.
    + apply pr2_transportf.
Defined.


Definition dirprod_disp_precat {C : precategory} (D1 D2 : disp_precat C) : disp_precat C.
Proof.
  use tpair.
  - exact (dirprod_disp_cat_data (pr1 D1) (pr1 D2)).
  - exact (dirprod_disp_precat_axioms D1 D2).
Defined.

(**
We can create the displayed precategory which adds a point and an endomorphism as the product of `disp_end` and `disp_type`.
 *)
Definition disp_point_end : disp_precat type_precat
  := dirprod_disp_precat disp_point disp_end.

Definition TYPE_point_end : precategory := total_precategory disp_point_end.

(** ℤb **)
(**
We first define a precategory of types with an added point and three added endomorphisms. (succ, pred₁, pred₂)
Given a type X, it will add the type (X × (X → X)) × (X → X) × (X → X)
 *)
Definition disp3 : disp_precat type_precat.
Proof.
  apply dirprod_disp_precat.
  - exact disp_point_end.
  - exact (dirprod_disp_precat disp_end disp_end).
Defined.

Definition TYPE3 : precategory := total_precategory disp3.

(** WIP
Then, we add the first coherency, by defining:
1) For each object (X, x, s, p₁, p₂) : TYPE3, the type

                 (z : X) → p₁(s(z)) = z

2) For each morphism  (f, _, p, α, _) : (X, x, s, p₁X, p₂X) → (Y, y, r, p₁Y, p₂Y)  and each  ε : (z : X) → p₁X(s(z)) = z  and  η : (z : Y) → p₁Y(r(z)) = z, we have the type

     (z : X) → η(f(z)) = ap_p₁B(p⁻¹(z)) · α⁻¹(s(z)) · ap_f(ε(z))

Conform Definition 10 of 'The Integers as Higher Inductive Type'.
 *)
Definition disp_sec_data : disp_cat_data TYPE3.
Proof.
  use tpair.
  - use make_disp_cat_ob_mor.
    + cbn.
      intro XX.
      exact (∏ z : (pr1 XX), pr122 XX (pr212 XX z) = z).  (*  (p1(s(z)) = z) *)
    + cbn. intros XX YY ε η ff.
      apply (∏ z : (pr1 XX), η (pr1 ff z) = (maponpaths (pr122 YY) (!(pr212 ff z))) @ (!(pr122 ff (pr212 XX z))) @ (maponpaths (pr1 ff) (ε z))).
  - split.
    + cbn.
      intros XX ε z.
      unfold idfun.
      refine (!_).
      apply maponpathsidfun.
    + cbn. intros XX YY ZZ ff gg ε η θ fff ggg z.
      refine (_ @ _ @ _ @ _ @ _ @ _).
      * apply ggg.
      * (*use (_ @ _ @ (!maponpaths (maponpaths (pr1 gg)) (ggg (pr1 ff z)))).*)
