Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.categories.Type.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.

Require Import Integers.disp_precat.
Require Import Integers.total_precat.
Require Import Integers.point_constructors.

Local Open Scope cat.
Local Open Scope mor_disp.

(** ℤb **)
(**
We first define a precategory of types with an added point and three added endomorphisms. (succ, pred₁, pred₂)
Given a type X, it will add the type (X × (X → X)) × (X → X) × (X → X)
 *)
Definition disp3 : disp_precat type_precat
  := dirprod_disp_precat disp_point_end (dirprod_disp_precat disp_end disp_end).

Definition TYPE3 : precategory := total_precategory disp3.
(* TYPE3 == (∑ x : UU, (x × (x → x)) × (x → x) × (x → x)) *)

(*
Definition disp_cat_data_from_disp_precat {C} (D : disp_precat C)
  := pr1 D : disp_cat_data C.
Coercion disp_cat_data_from_disp_precat : disp_precat >-> disp_cat_data.
*)


Definition type3 (X3 : TYPE3) : UU := pr1 X3.
Definition point {X3 : TYPE3} : type3 X3 := pr112 X3.
Definition s {X3 : TYPE3} : type3 X3 → type3 X3 := pr212 X3.
Definition p₁ {X3 : TYPE3} : type3 X3 → type3 X3 := pr122 X3.
Definition p₂ {X3 : TYPE3} : type3 X3 → type3 X3 := pr222 X3.


Definition f {X3 Y3 : TYPE3} {f3 : TYPE3 ⟦ X3, Y3 ⟧} : type3 X3 → type3 Y3 := pr1 f3.
Definition ff {X3 Y3 : TYPE3} {f3 : TYPE3 ⟦ X3, Y3 ⟧} : f point = point := pr112 f3.
Definition p {X3 Y3 : TYPE3} {f3 : TYPE3 ⟦ X3, Y3 ⟧} :
  ∏ z : type3 X3, s (f  z) = f (s z) :=  pr212 f3.
Definition α {X3 Y3 : TYPE3} {f3 : TYPE3 ⟦ X3, Y3 ⟧} :
  ∏ z : type3 X3, p₁ (f z) = f (p₁ z) :=  pr122 f3.
Definition β {X3 Y3 : TYPE3} {f3 : TYPE3 ⟦ X3, Y3 ⟧} :
  ∏ z : type3 X3, p₂ (f z) = f (p₂ z) :=  pr222 f3.


(**
Then, we add the first coherency, by defining:
1) For each object (X, x, s, p₁, p₂) : TYPE3, the type

                 (z : X) → p₁(s(z)) = z

2) For each morphism  (f, _, p, α, _) : (X, x, s, p₁X, p₂X) → (Y, y, r, p₁Y, p₂Y)  and each  ε : (z : X) → p₁X(s(z)) = z  and  η : (z : Y) → p₁Y(r(z)) = z, we have the type

     (z : X) → η(f(z)) = ap_p₁B(p⁻¹(z)) · α⁻¹(s(z)) · ap_f(ε(z))

Conform Definition 10 of 'The Integers as Higher Inductive Type'.
 *)
Definition disp_sec_ob_mor : disp_cat_ob_mor TYPE3.
Proof.
  use make_disp_cat_ob_mor.
  - cbn.
    intro X3.
    exact (∏ z : type3 X3, p₁ (s z) = z).
  - intros X3 Y3 ε η fff. cbn in ε, η.
    exact (∏ z : type3 X3, η (@f _ _ fff z) = maponpaths p₁ (p z) @ α (s z) @ maponpaths f (ε z)).
Defined.

(*
Definition disp_sec_comp: ∏ (x y z : TYPE3) (f0 : TYPE3 ⟦ x, y ⟧) (g : TYPE3 ⟦ y, z ⟧)
 (xx : disp_sec_ob_mor x) (yy : disp_sec_ob_mor y) (zz : disp_sec_ob_mor z),
                          xx -->[ f0] yy → yy -->[ g] zz → xx -->[ f0 · g] zz.
Proof.
  cbn.
intros.*)




Definition disp_sec_id_comp : disp_cat_id_comp TYPE3 disp_sec_ob_mor.
Proof.
  split.
  - cbn.
    intros X3 ε z.
    unfold idfun.
    refine (!_).
    apply maponpathsidfun.
  - cbn.
    intros X3 Y3 Z3 ff gg ε η θ fff ggg z.
    refine (_ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _ @ _).
    + apply (ggg _).
    + apply maponpaths.
      apply maponpaths.
      apply maponpaths.
      apply (fff z).
    + apply maponpaths.
      apply maponpaths.
      apply maponpathscomp0.
    + apply maponpaths.
      apply path_assoc.
    + apply maponpaths.
      apply maponpaths_2.
      apply maponpaths.
      apply maponpathscomp.
    + apply maponpaths.
      apply maponpaths_2.
      apply (! homotsec_natural (pr122 gg) _).
    + apply maponpaths.
      apply maponpaths_2.
      apply maponpaths_2.
      apply (! maponpathscomp _ _ _).
    + apply maponpaths.
      apply (! path_assoc _ _ _).
    + apply maponpaths.
      apply maponpaths.
      apply maponpaths.
      apply maponpathscomp0.
    + apply path_assoc.
    + apply maponpaths_2.
      apply (! maponpathscomp0 _ _ _).
    + apply maponpaths.
      apply path_assoc.
    + apply maponpaths.
      apply maponpaths.
      apply maponpathscomp.
Defined.



Check disp_sec_id_comp.

Definition disp_sec_data : disp_cat_data TYPE3
  := disp_sec_ob_mor ,, disp_sec_id_comp.

Print disp_sec_id_comp.


Definition disp_sec_axioms
  : disp_precat_axioms disp_sec_data.
Proof.
  simple refine (_ ,, _ ,, _).
  - cbn.
    intros X3 Y3 ff ε η ps.
    unfold idfun.
    use funextsec.
    intro z.
Abort.

