(*
 - Definition of the pseudofunctor `⦃ P ⦄` from a polynomial code `P`
From 'GrpdHITs/code/algebra/one_types_polynomials.v'
*)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import Integers.signature.

Require Import Integers.Prebicategories.DispPrebicat.
Require Import Integers.Prebicategories.PseudoFunctor.
Require Import Integers.TypeHomot.type_homot.

Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.

(** Preliminary  definitions**)
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

Definition coprodf_path_maponpaths_inl
           {X₁ X₂ Y₁ Y₂ : UU}
           (f : X₁ → X₂)
           (g : Y₁ → Y₂)
           {x₁ x₂ : X₁}
           (p : x₁ = x₂)
  : maponpaths (coprodf f g) (maponpaths inl p) = maponpaths inl (maponpaths f p).
Proof.
  induction p.
  exact (idpath (idpath (inl (f x₁)))).
Defined.

Definition coprodf_path_maponpaths_inr
           {X₁ X₂ Y₁ Y₂ : UU}
           (f : X₁ → X₂)
           (g : Y₁ → Y₂)
           {y₁ y₂ : Y₁}
           (p : y₁ = y₂)
  : maponpaths (coprodf f g) (maponpaths inr p) = maponpaths inr (maponpaths g p).
Proof.
  induction p.
  exact (idpath (idpath (inr (g y₁)))).
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

Definition path_dirprodf_path
           {X₁ X₂ Y₁ Y₂ : UU}
           {f₁ g₁ : X₁ → Y₁}
           {f₂ g₂ : X₂ → Y₂}
           {p₁ q₁ : f₁ ~ g₁}
           {p₂ q₂ : f₂ ~ g₂}
           (s₁ : p₁ ~ q₁) (s₂ : p₂ ~ q₂)
           (x : X₁ × X₂)
  : dirprodf_path p₁ p₂ x = dirprodf_path q₁ q₂ x
  := (maponpaths (λ z, pathsdirprod z _) (s₁ (pr1 x)))
       @ maponpaths (λ z, pathsdirprod _ z) (s₂ (pr2 x)).


Definition pathsdirprod_concat
           {X Y : UU}
           {x₁ x₂ x₃ : X}
           {y₁ y₂ y₃ : Y}
           (p₁ : x₁ = x₂) (p₂ : x₂ = x₃)
           (q₁ : y₁ = y₂) (q₂ : y₂ = y₃)
  : pathsdirprod p₁ q₁ @ pathsdirprod p₂ q₂
    =
    pathsdirprod (p₁ @ p₂) (q₁ @ q₂).
Proof.
  induction p₁, q₁.
  exact (idpath (pathsdirprod p₂ q₂)).
Defined.

Definition dirprodf_path_concat
           {X₁ X₂ Y₁ Y₂ : UU}
           {f₁ g₁ h₁ : X₁ → Y₁}
           {f₂ g₂ h₂ : X₂ → Y₂}
           (p₁ : f₁ ~ g₁) (q₁ : g₁ ~ h₁)
           (p₂ : f₂ ~ g₂) (q₂ : g₂ ~ h₂)
           (x : X₁ × X₂)
  : dirprodf_path p₁ p₂ x @ dirprodf_path q₁ q₂ x
    =
    dirprodf_path (homotcomp p₁ q₁) (homotcomp p₂ q₂) x
  := pathsdirprod_concat  (p₁ (pr1 x)) (q₁ (pr1 x)) (p₂ (pr2 x)) (q₂ (pr2 x)). 

Definition maponpaths_pathsdirprod
           {X₁ X₂ Y₁ Y₂ : UU}
           (φ : X₁ → X₂)
           (χ : Y₁ → Y₂)
           {x₁ x₂ : X₁}
           (p : x₁ = x₂)
           {y₁ y₂ : Y₁}
           (q : y₁ = y₂)
  : pathsdirprod (maponpaths φ p) (maponpaths χ q)
    =
    maponpaths (dirprodf φ χ) (pathsdirprod p q).
Proof.
  induction p, q.
  exact (idpath _).
Defined.  

Definition maponpaths_dirprodf_path
           {X₁ X₂ X₃ Y₁ Y₂ Y₃ : UU}
           (φ : X₂ → X₃)
           (χ : Y₂ → Y₃)
           {f₁ g₁ : X₁ → X₂}
           {f₂ g₂ : Y₁ → Y₂}
           (p₁ : f₁ ~ g₁)
           (p₂ : f₂ ~ g₂)
           (x : X₁ × Y₁)
  : dirprodf_path
      (λ (z : X₁), maponpaths φ (p₁ z))
      (λ (z : Y₁), maponpaths χ (p₂ z))
      x
    =
    maponpaths
      (dirprodf φ χ)
      (dirprodf_path p₁ p₂ x)
  := maponpaths_pathsdirprod φ χ (p₁ (pr1 x)) (p₂ (pr2 x)).

(** Action of polynomials on functions **)
Definition actmap (P : poly_code) {A B : UU} (f : A → B)
  : type_prebicat ⟦ act P A, act P B ⟧.
Proof.
  cbn.
  induction P as [X | | | ].
  - exact (λ y, y).
  - exact f.
  - exact (coprodf IHP1 IHP2).
  - exact (dirprodf IHP1 IHP2).
Defined.

(** `actmap` preserves composition, identity and homotopies **)
Definition poly_comp
           (P : poly_code)
           {A B C : UU}
           (f : A → B) (g : B → C)
  : actmap P g ∘ actmap P f ~ actmap P (g ∘ f)%functions.
Proof.
  induction P as [X | | | ].
  - exact (λ x, idpath x).
  - exact (λ x, idpath (g(f x))).
  - intro x.
    refine (!coprodf_comp _ _ _ _ x @ _).
    exact (coprodf_path IHP1 IHP2 x).
  - intro x.
    refine (!dirprodf_comp _ _ _ _ x @ _).
    exact (dirprodf_path IHP1 IHP2 x).
Defined.

Definition poly_id
           (P : poly_code)
           (A : UU)
  : (λ x : act P A, x) ~ (actmap P (λ x : A, x)).
Proof.
  induction P as [X | | | ].
  - exact (λ x, idpath x).
  - exact (λ x, idpath x).
  - exact (λ x, !coprodf_id x @ coprodf_path IHP1 IHP2 x).
  - exact (λ x, !dirprodf_id x @ dirprodf_path IHP1 IHP2 x).
Defined.

Definition poly_homot
           (P : poly_code)
           {A B : UU}
           {f g : A → B}
           (p : f ~ g)
  : actmap P f ~ actmap P g.
Proof.
  induction P as [X | | |].
  - exact (λ x, idpath x).
  - exact p.
  - exact (coprodf_path IHP1 IHP2).
  - exact (dirprodf_path IHP1 IHP2).
Defined.

(** The pseudofunctor **)
Definition poly_type_data (P : poly_code)
  : pseudofunctor_data type_prebicat type_prebicat.
Proof.
  use make_pseudofunctor_data.
  - exact (act P).
  - exact (λ A B f, actmap P f).
  - exact (λ A B f g, poly_homot P).
  - exact (poly_id P).
  - exact (λ A B C, poly_comp P).
Defined.

Definition poly_type_laws (P : poly_code)
  : pseudofunctor_laws (poly_type_data P).
Proof.
  repeat split; induction P as [X | | | ].
  - exact (λ A B f, idpath _).
  - exact (λ A B f, idpath _).
  - intros X Y f.
    apply funextsec.
    intro x.
    induction x as [x | x].
    + exact (maponpaths (maponpaths inl) (eqtohomot (IHP1 _ _ _) x)).
    + exact (maponpaths (maponpaths inr) (eqtohomot (IHP2 _ _ _) x)).
  - intros A B f.
    apply funextsec.
    exact (λ x, path_dirprodf_path (eqtohomot (IHP1 A B f)) (eqtohomot (IHP2 A B f)) x).
  - exact (λ A B f g h θ γ, idpath _).
  - exact (λ A B f g h θ γ, idpath _).
  - intros A B f g h θ γ.
    apply funextsec.
    intro x.
    induction x as [x | x].
    + exact ((maponpaths (maponpaths inl) (eqtohomot (IHP1 _ _ _ _ _ θ γ) x))
               @ maponpathscomp0 inl _ _).
    + exact ((maponpaths (maponpaths inr) (eqtohomot (IHP2 _ _ _ _ _ θ γ) x))
               @ maponpathscomp0 inr _ _).
  - intros A B f g h θ γ.
    apply funextsec.
    intro x.
    refine (_ @ !(dirprodf_path_concat _ _ _ _ _)).
    apply path_dirprodf_path.
    + exact (eqtohomot (IHP1 _ _ _ _ _ θ γ)).
    + exact (eqtohomot (IHP2 _ _ _ _ _ θ γ)).
  - exact (λ A B C f g h θ, idpath _).
  - intros A B C f g h θ.
    apply funextsec.
    exact (λ x, !pathscomp0rid _).
  - intros A B C f g h θ.
    apply funextsec.
    intro x.
    induction x as [x | x].
    +  exact (!maponpathscomp0 inl _ _
              @ maponpaths (maponpaths inl) (eqtohomot (IHP1 _ _ _ f _ _ θ) x)
              @ maponpathscomp0 inl _ _).
    + exact (!maponpathscomp0 inr _ _
              @ maponpaths (maponpaths inr) (eqtohomot (IHP2 _ _ _ f _ _ θ) x)
              @ maponpathscomp0 inr _ _).
  - intros A B C f g h θ.
    apply funextsec.
    intro x.
    refine (dirprodf_path_concat _ _ _ _ x @ _).
    refine (path_dirprodf_path
              (eqtohomot (IHP1 _ _ _ f _ _ θ))
              (eqtohomot (IHP2 _ _ _ f _ _ θ)) x @ _).
    exact (!dirprodf_path_concat _ _ _ _ x).
  - exact (λ A B C f g h θ, idpath _).
  - intros A B C f g h θ.
    apply funextsec.
    exact (λ x, !pathscomp0rid _).
  - intros A B C f g h θ.
    apply funextsec.
    intro x.
    induction x as [x | x].
    + refine (!maponpathscomp0 inl _ _ @ _).
      refine (_ @ maponpaths (λ p, p @ _) (!(coprodf_path_maponpaths_inl _ _ _))).
      exact (maponpaths (maponpaths inl) (eqtohomot (IHP1 A B C f g h θ) x)
                        @ maponpathscomp0 inl _ _).
    + refine (!maponpathscomp0 inr _ _ @ _).
      refine (_ @ maponpaths (λ p, p @ _) (!(coprodf_path_maponpaths_inr _ _ _))).
      exact (maponpaths (maponpaths inr) (eqtohomot (IHP2 A B C f g h θ) x)
                        @ maponpathscomp0 inr _ _).
  - intros A B C f g h θ.
    apply funextsec.
    intro x.
    refine (dirprodf_path_concat _ _ _ _ x @ _).
    refine (path_dirprodf_path
              (eqtohomot (IHP1 A B C f g h θ))
              (eqtohomot (IHP2 A B C f g h θ))
              x @ !_).
    refine (maponpaths (λ z, z @ _) (!_) @ _).
    + exact (maponpaths_dirprodf_path _ _ _ _ x).
    + exact (dirprodf_path_concat _ _ _ _ x).
  - exact (λ A B f, idpath _).
  - exact (λ A B f, idpath _).
  - intros A B f.
    apply funextsec.
    intro x.
    induction x as [x | x].
    + exact (maponpaths (maponpaths inl) (eqtohomot (IHP1 A B f) x)
               @ maponpathscomp0 inl _ _
               @ maponpaths (λ p, p @ _) (maponpathscomp0 inl _ _)
               @ maponpaths (λ p, (p @ _) @ _) (!coprodf_path_maponpaths_inl _ _ _)).
    + exact (maponpaths (maponpaths inr) (eqtohomot (IHP2 A B f) x)
               @ maponpathscomp0 inr _ _
               @ maponpaths (λ p, p @ _) (maponpathscomp0 inr _ _)
               @ maponpaths (λ p, (p @ _) @ _) (!(coprodf_path_maponpaths_inr _ _ _))).
  - intros A B f.
    apply funextsec.
    intro x.
    refine (path_dirprodf_path (eqtohomot (IHP1 A B f)) (eqtohomot (IHP2 A B f)) x @ _).
    refine (!(dirprodf_path_concat _ _ _ _ x) @ _).
    refine (maponpaths (λ z, z @ _) _).
    refine (!(dirprodf_path_concat _ _ _ _ x) @ _).
    refine (maponpaths (λ z, z @ _) _).
    exact (maponpaths_dirprodf_path _ _ _ _ x).
  - exact (λ A B f, idpath _).
  - exact (λ A B f, idpath _).
  - intros A B f.
    apply funextsec.
    intro x.
    induction x as [x | x].
    + exact (maponpaths (maponpaths inl) (eqtohomot (IHP1 A B f) x)
               @ maponpathscomp0 inl _ _
               @ maponpaths (λ p, p @ _) (maponpathscomp0 inl _ _)).
    + exact (maponpaths (maponpaths inr) (eqtohomot (IHP2 A B f) x)
               @ maponpathscomp0 inr _ _
               @ maponpaths (λ p, p @ _) (maponpathscomp0 inr _ _)).
  - intros A B f.
    apply funextsec.
    intro x.
    refine (path_dirprodf_path (eqtohomot (IHP1 A B f)) (eqtohomot (IHP2 A B f)) x @ _).
    refine (!dirprodf_path_concat _ _ _ _ x @ _).
    refine (maponpaths (λ z, z @ _) _).
    exact (!dirprodf_path_concat _ _ _ _ x).
  - exact (λ A B C D f g h, idpath _).
  - exact (λ A B C D f g h, idpath _).
  - intros A B C D f g h.
    apply funextsec.
    intro x.
    induction x as [x | x].
    + refine (maponpaths (λ p, p @ _) (!(maponpathscomp0 inl _ _))
                @ !(maponpathscomp0 inl _ _)
                @ maponpaths (maponpaths inl) (eqtohomot (IHP1 A B C D f g h) x)
                @ maponpathscomp0 inl _ _
                @ maponpaths (λ p, p @ _) (! _)).
      exact (coprodf_path_maponpaths_inl _ _ (poly_comp P1 f g x)).
    + refine (maponpaths (λ p, p @ _) (!(maponpathscomp0 inr _ _))
                @ !(maponpathscomp0 inr _ _)
                @ maponpaths (maponpaths inr) (eqtohomot (IHP2 A B C D f g h) x)
                @ maponpathscomp0 inr _ _
                @ maponpaths (λ p, p @ _) (! _)).
      exact (coprodf_path_maponpaths_inr _ _ (poly_comp P2 f g x)).
  - intros A B C D f g h.
    apply funextsec.
    intro x.
    symmetry.
    refine (maponpaths (λ p, p @ _) (!_) @ _).
    { exact (maponpaths_dirprodf_path _ _ _ _ x). }
    refine (dirprodf_path_concat _ _ _ _ x @ _).
    refine (!path_dirprodf_path
                (eqtohomot (IHP1 A B C D f g h))
                (eqtohomot (IHP2 A B C D f g h))
                x @ _).
    refine (!dirprodf_path_concat _ _ _ _ x @ _).
    refine (maponpaths (λ z, z @ _) _).
    exact (!dirprodf_path_concat _ _ _ _ x).
Qed.

Definition poly_type (P : poly_code)
  : pseudofunctor type_prebicat type_prebicat.
Proof.
  use make_pseudofunctor.
  - exact (poly_type_data P).
  - exact (poly_type_laws P).
  - split.
    + exact (λ A, type_prebicat_invertible_2cell).
    + exact (λ A B C f g, type_prebicat_invertible_2cell).
Defined.

Notation "⦃ P ⦄" := (poly_type P).
