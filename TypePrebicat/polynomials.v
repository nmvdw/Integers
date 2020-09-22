(* The bicategory of types, functions and equality *)
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


Require Import Integers.TypePrebicat.type_prebicat_tpair.

Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.

(** Preliminary **)

(* For coproduct *)
Definition coprodf_path
           {X1 X2 Y1 Y2 : UU}
           {f1 g1 : X1 → Y1}
           {f2 g2 : X2 → Y2}
           (p1 : f1 = g1)
           (p2 : f2 = g2)
           (x : X1 ⨿ X2)
  : coprodf f1 f2 x = coprodf g1 g2 x.
Proof.
  induction x as [x | x].
  - exact (maponpaths inl (eqtohomot p1 x)).
  - exact (maponpaths inr (eqtohomot p2 x)).
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


(* For product *)
Definition dirprodf_path
           {X1 X2 Y1 Y2 : UU}
           {f1 g1 : X1 → Y1}
           {f2 g2 : X2 → Y2}
           (p1 : f1 = g1)
           (p2 : f2 = g2)
           (x : X1 × X2)
  : dirprodf f1 f2 x = dirprodf g1 g2 x
  := pathsdirprod (eqtohomot p1 (pr1 x)) (eqtohomot p2 (pr2 x)).


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

    
(* Polynomial acts on universe *)
Definition act (P : poly_code) (A : UU) : UU.
Proof.
  induction P as [X | | | ].
  - exact X.
  - exact A.
  - exact (IHP1 ⨿ IHP2).
  - exact (IHP1 × IHP2).
Defined.

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


(* The pseudofunctor *)
Definition poly_type_data (P : poly_code)
  : pseudofunctor_data type_prebicat type_prebicat.
Proof.
  use make_pseudofunctor_data.
  - exact (act P).
  - exact (λ A B f, actmap P f).
  - cbn. intros A B f g p.
    induction P as [X | | | ].
    + exact (idpath _).
    + exact p.
    + exact (funextsec _ _ _ (coprodf_path IHP1 IHP2)).
    + exact (funextsec _ _ _ (dirprodf_path IHP1 IHP2)).
  - cbn. intros A.
    induction P as [X | | | ].
    + exact (idpath _).
    + exact (idpath _).
    + apply funextsec.
      exact (λ x, !coprodf_id x @ coprodf_path IHP1 IHP2 x).
    + apply funextsec.
      exact (λ x, !dirprodf_id x @ dirprodf_path IHP1 IHP2 x).
  - cbn. intros A B C f g.
    induction P as [X | | | ].
    + exact (idpath _).
    + exact (idpath _).
    + apply funextsec.
      exact (λ x, !coprodf_comp _ _ _ _ x @ coprodf_path IHP1 IHP2 x).
    + apply funextsec.
      exact (λ x, !dirprodf_comp _ _ _ _ x @ dirprodf_path IHP1 IHP2 x).
Defined.

Definition poly_type_laws (P : poly_code)
  : pseudofunctor_laws (poly_type_data P).
Proof.
  repeat split; induction P as [X | | | ].
  - exact (λ A B f, idpath _).
  - exact (λ A B f, idpath _).
  - intros A B f. unfold pseudofunctor_id2_law in IHP1, IHP2.
    Check (F₁ (poly_type_data P1) f).
    Check (IHP1 A B f).

    (* We have to give paths between paths between functions, so we can't do funextsec *)
    (* If we would have had paths between homotopies, we could do funextsec,
       because homotopies are dependent functions *)
Abort.
