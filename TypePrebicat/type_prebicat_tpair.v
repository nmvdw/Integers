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
  - exact (λ X Y f g p, pathscomp0rid p).
  - exact (λ X Y f g h k p q r, path_assoc p q r).
  - exact (λ X Y Z f g, idpath _).
  - exact (λ X Y Z f g, idpath _).
  - exact (λ X Y Z f g h k p q, !maponpathscomp0 _ p q).
  - exact (λ X Y Z f g h k p q, !maponpathscomp0 _ p q).
  - exact (λ X Y f g p, pathscomp0rid _ @ maponpathsidfun p).
  - exact (λ X Y f g p, pathscomp0rid _ @ maponpathsidfun p).
  - intros X Y Z W f g h k p.
    refine (_ @ _).
    + exact (pathscomp0rid _).
    + exact (maponpathscomp (λ l, (l ∘ g)%functions) (λ l, (l ∘ f)%functions) p).
  - intros X Y Z W f g h k p.
    refine (_ @ _ @ _).
    + exact (pathscomp0rid _).
    + exact (@maponpathscomp _ (Y → W) _ g h _ _ p).
    + exact (!@maponpathscomp _ _ (X → W) g h _ (λ l, (k ∘ l)%functions) p).
  - intros X Y Z W f g h k p.
    refine (_ @ _).
    + exact (@maponpathscomp _ _ (X → W) f g _ (λ l, _) p).
    + exact (!pathscomp0rid _).
  - intros X Y Z f g h k p q.

    (*
    (*    Check (λ l : Y → Z, maponpaths (λ m : X → Y, (l ∘ m)%functions)).*)
    Check (λ l, funcomphomot2 Z p l).
    Check (@homotsec_natural).
    Check (@homotsec_natural (Y → Z) (X → Z) (λ l : Y → Z, (l ∘ f)%functions) (λ l : Y → Z, (l ∘ g)%functions) (λ l, funcomphomot2 Z p l) h k q).
*)


    
    induction p.
    exact (!pathscomp0rid _).
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
  := !θ,, pathsinv0r θ,, pathsinv0l θ.
