(* The prebicategory of types, functions and homotopy *)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.
Require Import UniMath.Bicategories.DisplayedBicats.Examples.DisplayedCatToBicat.

Require Import Integers.Prebicategories.DispPrebicat.

Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.

Definition type_prebicat_data : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact Type.
  - exact (λ X Y, X → Y).
  - exact (λ A B f g, f ~ g).
  - exact idfun.
  - exact (λ A B Z, funcomp).
  - exact (λ A B f, homotrefl f).
  - exact (λ A B f g h θ γ, homotcomp θ γ).
  - exact (λ A B C f g h θ, funhomotsec f θ).
  - exact (λ A B C f g h θ, homotfun θ h).
  - exact (λ A B f x, idpath (f x)).
  - exact (λ A B f x, idpath (f x)).
  - exact (λ A B f x, idpath (f x)).
  - exact (λ A B f x, idpath (f x)).
  - exact (λ A B C D f g h x, idpath (h (g (f x)))).
  - exact (λ A B C D f g h x, idpath (h (g (f x)))).
Defined.

Definition type_prebicat_laws : prebicat_laws type_prebicat_data.
Proof.
  repeat (use tpair).
  - exact (λ A B f g θ, idpath θ).
  - intros A B f g θ.
    apply funextsec.
    exact (λ x, pathscomp0rid (θ x)).
  - intros A B f g h k θ γ τ.
    apply funextsec.
    exact (λ x, path_assoc (θ x) (γ x) (τ x)).
  - exact (λ A B C f g, idpath _).
  - exact (λ A B C f g, idpath _).
  - intros A B C f g h k θ γ.
    apply funextsec.
    exact (λ x, idpath (θ (f x) @ γ (f x))).
  - intros A B C f g h k θ γ.
    apply funextsec.
    exact (λ x, !maponpathscomp0 k (θ x) (γ x)).
  - intros A B f g θ.
    apply funextsec.
    exact (λ x, pathscomp0rid (θ x)).
  - intros A B f g θ.
    apply funextsec.
    exact (λ x, pathscomp0rid _ @ maponpathsidfun _).
  - intros A B C D f g h i θ.
    apply funextsec.
    exact (λ x, pathscomp0rid (θ (g (f x)))).
  - intros A B C D f g h i θ.
    apply funextsec.
    exact (λ x, pathscomp0rid _).
  - intros A B C D f g h i θ.
    apply funextsec.    
    exact (λ x, maponpathscomp h _ _ @ ! pathscomp0rid _).
  - intros A B C f g h i θ γ.
    apply funextsec.
    exact (λ x, homotsec_natural γ (θ x)).
  - exact (λ A B f, idpath _).
  - exact (λ A B f, idpath _).
  - exact (λ A B f, idpath _).
  - exact (λ A B f, idpath _).
  - exact (λ A B C D f g h, idpath _).
  - exact (λ A B C D f g h, idpath _).
  - exact (λ A B C f g, idpath _).
  - exact (λ A B C D E f g h i, idpath _).
Qed.

Definition type_prebicat : prebicat
  := type_prebicat_data,, type_prebicat_laws.

Definition type_prebicat_invertible_2cell
      {A B : type_prebicat}
      {f g : A --> B}
      {θ : f ==> g}
  : is_invertible_2cell θ
  := invhomot θ,, funextsec _ _ _ (λ x, pathsinv0r (θ x)),, funextsec _ _ _ (λ x, pathsinv0l (θ x)).

