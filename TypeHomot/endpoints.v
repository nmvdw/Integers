
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import sem.signature.hit_signature.
Require Import sem.prelude.basics.

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
  - cbn. exact (λ X, endpoint_type_ob e (pr2 X)).
  - cbn. intros X Y f.
    use make_invertible_2cell.
    + exact (λ x, endpoint_type_mor e (pr12 f) x).
    + exact type_prebicat_invertible_2cell.
Defined.


Definition endpoint_type_natural
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X Y : UU}
           {cX : poly_act A X → X}
           {cY : poly_act A Y → Y}
           {f g : X → Y}
           {ef : ((λ x, f (cX x)) ~ (λ x, cY (actmap A f x)))}
           {eg : ((λ x, g (cX x)) ~ (λ x, cY (actmap A g x)))}
           {αp : f ~ g}
           (αh : (λ x : act A X, αp (cX x) @ eg x)
                 =
                 (λ x : act A X, ef x @ maponpaths cY (poly_homot A αp x)))
           (x : act P X)
  : poly_homot Q αp (endpoint_type_ob e cX x)
               @ endpoint_type_mor e eg x
    =
    endpoint_type_mor e ef x
                      @ maponpaths (endpoint_type_ob e cY) (poly_homot P αp x).
Proof.
  induction e as [ | | | | | | | P T t | | ].
  - exact (pathscomp0rid _ @ !(maponpathsidfun _)).
  - exact (path_assoc _ _ _
                      @ maponpaths (λ z, z @ _) (IHe2 (endpoint_type_ob e1 cX x))
                      @ !(path_assoc _ _ _)
                      @ maponpaths
                      (λ z, _ @ z)
                      (!(maponpathscomp0 _ _ _)
                        @ maponpaths (maponpaths (endpoint_type_ob e2 cY)) (IHe1 x)
                        @ maponpathscomp0 _ _ _
                        @ maponpaths (λ z, _ @ z) (maponpathscomp _ _ _))
                      @ path_assoc _ _ _).
  - exact (pathscomp0rid _).
  - exact (pathscomp0rid _).
  - exact (pathscomp0rid _ @ !(maponpaths_pr1_pathsdirprod _ _)).
  - exact (pathscomp0rid _ @ !(maponpaths_pr2_pathsdirprod _ _)).
  - exact (pathsdirprod_concat _ _ _ _
                               @ paths_pathsdirprod (IHe1 x) (IHe2 x)
                               @ !(pathsdirprod_concat _ _ _ _)
                               @ maponpaths (λ z, _ @ z)
                               (!(maponpaths_prod_path _ _ _))).
  - exact (!(maponpaths_for_constant_function _ _)).
  - exact (idpath (idpath (f0 x))).
  - exact (eqtohomot αh x).
Qed.    

    
Definition endpoint_type_id
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X : UU}
           (c : act A X → X)
           (x : act P X)
  : (poly_id Q X (endpoint_type_ob e c x)
             @ poly_homot Q (λ z, idpath z) (endpoint_type_ob e c x))
      @ endpoint_type_mor e (λ z, maponpaths c (poly_id A X z)) x
    =
    maponpaths (endpoint_type_ob e c)
               (poly_id P X x @ poly_homot P (λ z, idpath z) x).
Proof.
  induction e as [ | | | | | | | P T t | | ].
  - exact (pathscomp0rid _ @ !maponpathsidfun _).
  - exact (path_assoc _ _ _
           @ maponpaths (λ z, z @ _) (IHe2 (endpoint_type_ob e1 c x))
           @ !maponpathscomp0 _ _ _
           @ maponpaths
               (maponpaths (endpoint_type_ob e2 c))
               (IHe1 x)
               @ maponpathscomp _ _ _).
  - exact (pathscomp0rid _ @ !maponpathscomp0 _ _ _).
  - exact (pathscomp0rid _ @ !maponpathscomp0 _ _ _).
  - exact (pathscomp0rid _
           @ !maponpaths_pr1_pathsdirprod _ _
           @ maponpaths (maponpaths pr1) (!pathsdirprod_concat _ _ _ _)).
  - exact (pathscomp0rid _
           @ !maponpaths_pr2_pathsdirprod _ _
           @ maponpaths (maponpaths dirprod_pr2) (!pathsdirprod_concat _ _ _ _)).
  - exact (maponpaths
             (λ z, z @ _)
             (pathsdirprod_concat _ _ _ _)
           @ pathsdirprod_concat _ _ _ _
           @ paths_pathsdirprod (IHe1 x) (IHe2 x)
           @ !maponpaths_prod_path _ _ _).
  - exact (!maponpaths_for_constant_function _ _).
  - exact (idpath (idpath (f x))).
  - exact (maponpaths
             (maponpaths c)
             (!pathscomp0rid _
              @ maponpaths
                  (λ z, _ @ z)
                  (!(eqtohomot
                       (pseudofunctor_id2 ⦃ A ⦄ (λ x : X, x))
                       x)))).
Qed.    

Definition endpoint_type_comp
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X Y Z : total_prebicat (disp_alg_prebicat ⦃ A ⦄)}
           (f : X --> Y)
           (g : Y --> Z)
           (x : act P (pr1 X))
  : (poly_comp Q (pr1 f) (pr1 g) (endpoint_type_ob e (pr2 X) x)
      @ poly_homot Q (λ z, idpath (pr1 g (pr1 f z))) (endpoint_type_ob e (pr2 X) x))
      @ endpoint_type_mor e
      (λ z,
       (((maponpaths (pr1 g) (pr12 f z)
           @ idpath (pr1 g (pr2 Y (actmap A (pr1 f) z))))
           @ (pr12 g) (actmap A (pr1 f) z))
           @ idpath (pr2 Z (actmap A (pr1 g) (actmap A (pr1 f) z))))
           @ maponpaths (pr2 Z) (poly_comp A (pr1 f) (pr1 g) z))
      x
    =
    (((maponpaths
         (actmap Q (pr1 g))
         (endpoint_type_mor e (pr12 f) x)
      @ idpath (actmap Q (pr1 g) (endpoint_type_ob e (pr2 Y) (actmap P (pr1 f) x))))
      @ endpoint_type_mor e (pr12 g) (actmap P (pr1 f) x))
      @ idpath (endpoint_type_ob e (pr2 Z) (actmap P (pr1 g) (actmap P (pr1 f) x))))
      @ maponpaths
         (endpoint_type_ob e (pr2 Z))
         (poly_comp P (pr1 f) (pr1 g) x
                    @ poly_homot P (λ z, idpath (pr1 g (pr1 f z))) x).
Proof.
  refine (!_).
  etrans.
  {
    apply maponpaths_2.
    etrans.
    { apply pathscomp0rid. }
    apply maponpaths_2.
    apply pathscomp0rid.
  }
  etrans.
  {
    apply maponpaths.
    apply maponpaths.
    etrans.
    {
      apply maponpaths.
      apply (eqtohomot (pseudofunctor_id2 ⦃ P ⦄ (λ z, pr1 g (pr1 f z)))).
    }
    apply pathscomp0rid.
  }
  refine (!_).  
  etrans.
  {
    apply maponpaths_2.
    etrans.
    {
      apply maponpaths.
      apply (eqtohomot (pseudofunctor_id2 ⦃ Q ⦄ (λ z, pr1 g (pr1 f z)))).
    }
    apply pathscomp0rid.
  }    
  induction e as [ | | | | | | | P T t | | ].
  - exact (pathscomp0rid _ @ !maponpathsidfun _).
  - assert (poly_comp
              R (pr1 f) (pr1 g)
              (endpoint_type_ob e2 (pr2 X) (endpoint_type_ob e1 (pr2 X) x))
            @ endpoint_type_mor e2
                (λ x0,
                 (((maponpaths (pr1 g) ((pr12 f) x0)
                    @ idpath (pr1 g (pr2 Y (actmap A (pr1 f) x0))))
                    @ (pr12 g) (actmap A (pr1 f) x0))
                    @ idpath (pr2 Z (actmap A (pr1 g) (actmap A (pr1 f) x0))))
            @ maponpaths
                (pr2 Z)
                (poly_comp A (pr1 f) (pr1 g) x0)) (endpoint_type_ob e1 (pr2 X) x)
            @ maponpaths
                (endpoint_type_ob e2 (pr2 Z))
                (endpoint_type_mor
                   e1
                   (λ x0,
                    (((maponpaths (pr1 g) ((pr12 f) x0)
                       @ idpath (pr1 g (pr2 Y (actmap A (pr1 f) x0))))
                       @ (pr12 g) (actmap A (pr1 f) x0))
                       @ idpath _)
                      @ maponpaths (pr2 Z) (poly_comp A (pr1 f) (pr1 g) x0))
                   x)
            =
            (maponpaths
               (poly_map R (pr1 g))
               (endpoint_type_mor
                  e2 (pr12 f)
                  (endpoint_type_ob e1 (pr2 X) x)
            @ maponpaths
                (endpoint_type_ob e2 (pr2 Y))
                (endpoint_type_mor e1 (pr12 f) x))
            @ endpoint_type_mor
                e2 (pr12 g)
                (endpoint_type_ob e1 (pr2 Y) (actmap P (pr1 f) x))
            @ maponpaths
                (endpoint_type_ob e2 (pr2 Z))
                (endpoint_type_mor e1 (pr12 g) (actmap P (pr1 f) x)))
            @ maponpaths
                (λ x0, endpoint_type_ob e2 (pr2 Z) (endpoint_type_ob e1 (pr2 Z) x0))
                (poly_comp P (pr1 f) (pr1 g) x))
      as goal.
    {
      refine (path_assoc _ _ _ @ _).
      etrans.
      {
        apply maponpaths_2.
        apply IHe2.
      }
      clear IHe2.
      refine (!path_assoc _ _ _ @ _ @ path_assoc _ _ _).
      refine (!path_assoc _ _ _ @ _).
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        exact (maponpathscomp0 (actmap R (pr1 g)) _ _ ).
      }
      refine (!path_assoc _ _ _ @ _).
      apply maponpaths.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        { exact (!maponpathscomp0 (endpoint_type_ob e2 (pr2 Z)) _ _). }
        apply maponpaths.
        apply IHe1.
      }
      clear IHe1.
      refine (!_).
      etrans.
      {
        apply maponpaths.
        refine (!path_assoc _ _ _ @ _).
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          exact (!maponpathscomp _ _ _).
        }
        exact (!maponpathscomp0 _ _ _).
      }
      refine (!_).
      etrans.
      {
        apply maponpaths.
        etrans.
        {
          apply maponpaths.
          exact (!path_assoc _ _ _).
        }
        exact (maponpathscomp0 _ _ _).
      }
      refine (path_assoc _ _ _ @ _).
      refine (_ @ !path_assoc _ _ _).
      apply maponpaths_2.
      etrans.
      {
        apply maponpaths.
        apply maponpathscomp.
      }
      refine (!_).
      etrans.
      {
        apply maponpaths_2.
        apply maponpathscomp.
      }
      exact (homotsec_natural'
               (endpoint_type_mor e2 (pr12 g))
               (endpoint_type_mor e1 (pr12 f) x)).
    }
    exact goal.
  - exact (pathscomp0rid _).
  - exact (pathscomp0rid _).        
  - exact (pathscomp0rid _ @ !maponpaths_pr1_pathsdirprod _ _).
  - exact (pathscomp0rid _ @ !maponpaths_pr2_pathsdirprod _ _).
  - refine (!(_ @ _ @ _ @ _ @ _)).
    + refine (maponpaths (λ z, _ @ z) _).
      exact (maponpaths_prod_path _ _ _).
    + refine (maponpaths (λ z, z @ _) _).    
      etrans.
      * refine (maponpaths (λ z, z @ _) _).
        exact (!maponpaths_pathsdirprod _ _ _ _).
      * exact (pathsdirprod_concat _ _ _ _).
    + exact (pathsdirprod_concat _ _ _ _).
    + exact (!paths_pathsdirprod (IHe1 x) (IHe2 x)).
    + exact (!pathsdirprod_concat _ _ _ _).
  - exact (!maponpaths_for_constant_function _ _).
  - exact (idpath _).
  - refine (maponpaths (λ z, z @ maponpaths _ _) _).
    etrans.
    { apply pathscomp0rid. }
    apply maponpaths_2.
    exact (pathscomp0rid _).
Qed.

Definition endpoint_type_laws
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : is_pseudotrans (endpoint_type_data e).
Proof.
  repeat split.
  - intro X.
    apply funextsec.
    exact (endpoint_type_id e (pr2 X)).
  - intros X Y Z f g.
    apply funextsec.
    exact (endpoint_type_comp e f g).
Qed.

Definition endpoint_type
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : pseudotrans
      (comp_pseudofunctor ⦃ P ⦄ (pr1_pseudofunctor (disp_alg_prebicat ⦃ A ⦄)))
      (comp_pseudofunctor ⦃ Q ⦄ (pr1_pseudofunctor (disp_alg_prebicat ⦃ A ⦄)))
  := endpoint_type_data e,, endpoint_type_laws e.
