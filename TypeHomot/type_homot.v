(* The bicategory of types, functions and homotopy *)
(* Based on UniMath/Bicategories/Examples/OneTypes.v *)
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
  - exact (λ X Y f g, f ~ g).
  - exact idfun.
  - exact (λ X Y Z, funcomp).
  - exact (λ X Y f, homotrefl f).
  - exact (λ X Y f g h p q, homotcomp p q).
  - exact (λ X Y Z f g h p, funhomotsec f p).
  - exact (λ X Y Z f g h p, homotfun p h).
  - exact (λ X Y f x, idpath (f x)).
  - exact (λ X Y f x, idpath (f x)).
  - exact (λ X Y f x, idpath (f x)).
  - exact (λ X Y f x, idpath (f x)).
  - exact (λ X Y Z W f g h x, idpath (h (g (f x)))).
  - exact (λ X Y Z W f g h x, idpath (h (g (f x)))).
Defined.

Definition funcomphomot {A B C : UU} {f g : A → B} (l : B → C) (p : f = g)
  : (l ∘ f)%functions ~ (l ∘ g)%functions
  := (λ x, maponpaths l (eqtohomot p x)).

Definition funcomppath {A B C : UU} {f g : A → B} (l : B → C) (p : f = g)
  : (l ∘ f)%functions = (l ∘ g)%functions
  := funextsec _ _ _ (funcomphomot l p).

Definition funcomphomot2 {X Y : UU} (Z : UU) {f g : X → Y} (p : f = g)
  : (λ l : Y → Z, (l ∘ f)%functions) ~ (λ l : Y → Z, (l ∘ g)%functions)
  := λ l, funcomppath l p.
  

Definition type_prebicat_laws : prebicat_laws type_prebicat_data.
Proof.
  repeat (use tpair).
  - exact (λ X Y f g p, idpath p).
  - intros X Y f g p.
    apply funextsec.
    exact (λ x, pathscomp0rid (p x)).
  - intros X Y f g h k p q r.
    apply funextsec.
    exact (λ x, path_assoc (p x) (q x) (r x)).
  - exact (λ X Y Z f g, idpath _).
  - exact (λ X Y Z f g, idpath _).
  - intros X Y Z f g h k p q.
    apply funextsec.
    exact (λ x, idpath _).
  - intros X Y Z f g h k p q.
    apply funextsec.
    exact (λ x, !maponpathscomp0 k (p x) (q x)).
  - intros X Y f g p.
    apply funextsec.
    exact (λ x, pathscomp0rid (p x)).
  - intros X Y f g p.
    apply funextsec.
    exact (λ x, pathscomp0rid _ @ maponpathsidfun _).
  - intros X Y Z W f g h k p.
    apply funextsec.
    exact (λ x, pathscomp0rid (p (g (f x)))).
  - intros X Y Z W f g h k p.
    apply funextsec.
    exact (λ x, pathscomp0rid _).
  - intros X Y Z W f g h k p.
    apply funextsec.    
    exact (λ x, maponpathscomp h _ _ @ ! pathscomp0rid _).
  - intros X Y Z f g h k p q.
    apply funextsec.
    exact (λ x, homotsec_natural q (p x)).
  - exact (λ X Y f, idpath _).
  - exact (λ X Y f, idpath _).
  - exact (λ X Y f, idpath _).
  - exact (λ X Y f, idpath _).
  - exact (λ X Y Z W f g h, idpath _).
  - exact (λ X Y Z W f g h, idpath _).
  - exact (λ X Y Z f g, idpath _).
  - exact (λ X Y Z W V f g h k, idpath _).
Qed.

Definition type_prebicat : prebicat
  := type_prebicat_data,, type_prebicat_laws.

Definition type_prebicat_invertible_2cell
      {a b : type_prebicat}
      {f g : a --> b}
      {θ : f ==> g}
  : is_invertible_2cell θ
  := invhomot θ,, funextsec _ _ _ (λ x, pathsinv0r (θ x)),, funextsec _ _ _ (λ x, pathsinv0l (θ x)).

