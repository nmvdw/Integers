(* The bicategory of types, functions and equality *)
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

Definition happly {A : UU} {B : A → UU} {f g : ∏ x : A, B x} (p : f = g)
  : f ~ g
  := λ x, maponpaths (λ k : ∏ y : A, B y, k x) p.

Definition happly2 {A B : UU} {f g : A → B} (p : f = g)
  : f ~ g
  := λ x, maponpaths (λ k : A → B, k x) p.

Definition type_prebicat_data : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact Type.
  - exact (λ X Y, X → Y).
  - exact (λ X Y f g, f = g).
  - exact idfun.
  - exact (λ X Y Z, funcomp).
  - exact (λ X Y f, idpath f).
  - exact (λ X Y f g h p q, p @ q).
  - apply (λ X Y Z f g h p, maponpaths (λ k : Y → Z, _) p).
  - apply (λ X Y Z f g h p, maponpaths (λ k : X → Y, _) p).
  - exact (λ X Y f, idpath f).
  - exact (λ X Y f, idpath f).
  - exact (λ X Y f, idpath f).
  - exact (λ X Y f, idpath f).
  - exact (λ X Y Z W f g h, idpath _).
  - exact (λ X Y Z W f g h, idpath _).
Defined.

Definition type_prebicat_laws : prebicat_laws type_prebicat_data.
Proof.
  repeat split.
  - exact (λ X Y f g p, pathscomp0rid p).
  - exact (λ X Y f g h k p q r, path_assoc p q r).
  - exact (λ X Y Z f g h k p q, !maponpathscomp0 _  p q).
  - exact (λ X Y Z f g h k p q, !maponpathscomp0 (λ x, _) p q).
  - intros X Y f g p.
    induction p.
    exact (idpath (idpath f)).
  - intros X Y f g p.
    induction p.
    exact (idpath (idpath f)).
  - intros X Y Z W f g h k p.
    induction p.
    exact (idpath (idpath (h ∘ g ∘ f))).
  - intros X Y Z W f g h k p.
    induction p.
    exact (idpath (idpath (k ∘ g ∘ f))).
  - intros X Y Z W f g h k p.
    induction p.
    exact (idpath (idpath (k ∘ h ∘ f))).
  - cbn. intros X Y Z f g h k p q.
    induction p. induction q.
    exact (idpath (idpath ((h ∘ f)%functions))).
Qed.

Definition type_prebicat : prebicat
  := type_prebicat_data,, type_prebicat_laws.

Definition type_prebicat_invertible_2cell
      {a b : type_prebicat}
      {f g : a --> b}
      {θ : f ==> g}
  : is_invertible_2cell θ
  := !θ,, pathsinv0r θ,, pathsinv0l θ.
