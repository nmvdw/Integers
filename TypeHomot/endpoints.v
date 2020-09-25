
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import sem.signature.hit_signature.

Require Import Integers.Prebicategories.DispPrebicat.
Require Import Integers.Prebicategories.PseudoFunctor.
Require Import Integers.Prebicategories.PseudoTransformation.
Require Import Integers.Prebicategories.Composition.
Require Import Integers.Prebicategories.Projection.
Require Import Integers.Prebicategories.Algebra.
Require Import Integers.TypeHomot.type_homot.
Require Import Integers.TypeHomot.polynomials.

Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.

Check act.
Check actmap.


Definition endpoint_type_ob
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X : UU}
           (c : act A X → X)
  : act P X → act Q X.
Proof.
  induction e as [ | | | | | | | P T t | | ].
  - exact (λ x, x).
  - exact (λ x, IHe2 (IHe1 x)).
  - exact inl.
  - exact inr.
  - exact pr1.
  - exact pr2.
  - exact (λ x, IHe1 x,, IHe2 x).
  - exact (λ x, t).
  - exact f.
  - exact c.
Defined.
  
Definition endpoint_type_mor
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X Y : UU}
           {cX : act A X → X}
           {cY : act A Y → Y}
           {f : X → Y}
           (ef : ((λ x, f (cX x)) ~ (λ x, cY (poly_map A f x))))
           (x : act P X)
  : actmap Q f (endpoint_type_ob e cX x)
    =
    endpoint_type_ob e cY (actmap P f x).
Proof.
  induction e as [ | | | | | | | P T t | | ].
  - exact (idpath _).
  - exact (IHe2 (endpoint_type_ob e1 cX x)
                @ maponpaths (endpoint_type_ob e2 cY) (IHe1 x)).
  - exact (idpath (inl (actmap P f x))).
  - exact (idpath (inr (actmap Q f x))).
  - exact (idpath (pr1 (actmap (P * Q) f x))).
  - exact (idpath (pr2 (actmap (P * Q) f x))).
  - exact (pathsdirprod (IHe1 x) (IHe2 x)).
  - exact (idpath t).
  - exact (idpath (f0 x)).
  - exact (ef x).
Defined.
    
Definition endpoint_type_data
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : pseudotrans_data
      (comp_pseudofunctor (⦃ P ⦄) (pr1_pseudofunctor (disp_alg_prebicat (⦃ A ⦄))))
      (comp_pseudofunctor (⦃ Q ⦄) (pr1_pseudofunctor (disp_alg_prebicat (⦃ A ⦄)))).
Proof.
  use make_pseudotrans_data.
  - cbn.  exact (λ X, endpoint_type_ob e (pr2 X)).
  - cbn. intros X Y f.
    use make_invertible_2cell.
    + exact (λ x, endpoint_type_mor e (pr12 f) x).
    + exact type_prebicat_invertible_2cell.
Defined.

(*
Definition endpoint_type_laws
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : pseudotrans_laws (endpoint_type_data e).
*)
