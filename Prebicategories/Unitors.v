(* 
 - Lemmas concerning the left and right unitors of prebicategories.
From 'UniMath/Bicategories/Core/Unitors.v' *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.Core.Examples.OpMorBicat.
Require Import UniMath.Bicategories.Core.Examples.OpCellBicat.
Local Open Scope bicategory_scope.
Local Open Scope cat.

Require Import Integers.Prebicategories.Invertible_2cells.

Section unitors.

Context {C : prebicat}.

Lemma runitor_rwhisker_rwhisker {a b c d: C} (f : C⟦a, b⟧)
      (g : C⟦b, c⟧) (h : C⟦c, d⟧)
  : (rassociator f g (identity c) ▹ h) • ((f ◃ runitor g) ▹ h) =
    runitor (f · g) ▹ h.
Proof.
  apply pathsinv0.
  etrans.
  { apply pathsinv0. apply lunitor_lwhisker. }

  apply (vcomp_rcancel (rassociator _ _ _ )).
  { apply is_invertible_2cell_rassociator. }

  etrans.
  { apply vassocl. }
  etrans.
  { apply maponpaths.
    apply pathsinv0, lwhisker_lwhisker_rassociator.
  }

  apply pathsinv0.
  etrans. { apply vassocl. }
  etrans.
  { apply maponpaths.
    apply pathsinv0, rwhisker_lwhisker_rassociator.
  }

  etrans.
  { do 3 apply maponpaths.
    apply pathsinv0.
    apply lunitor_lwhisker.
  }

  etrans.
  { do 2 apply maponpaths.
    apply pathsinv0, lwhisker_vcomp.
  }

  etrans. { apply vassocr. }
  etrans. { apply vassocr. }

  apply pathsinv0.
  etrans. { apply vassocr. }
  apply maponpaths_2.

  use inv_cell_eq.
  - use is_invertible_2cell_vcomp.
    + apply is_invertible_2cell_rassociator.
    + apply is_invertible_2cell_rassociator.
  - use is_invertible_2cell_vcomp.
    + use is_invertible_2cell_vcomp.
      * apply is_invertible_2cell_rwhisker.
        apply is_invertible_2cell_rassociator.
      * apply is_invertible_2cell_rassociator.
    + apply is_invertible_2cell_lwhisker.
      apply is_invertible_2cell_rassociator.
  - cbn.
    apply pathsinv0.
    etrans. apply vassocr.
    apply lassociator_lassociator.
Qed.

Lemma rwhisker_id_inj {a b : C} (f g : C⟦a, b⟧)
      (x y : f  ==> g)
  : x ▹ identity b = y ▹ identity b → x = y.
Proof.
  intro H.
  apply (vcomp_lcancel (runitor _)).
  - apply is_invertible_2cell_runitor.
  - etrans. apply pathsinv0, vcomp_runitor.
    etrans. 2: apply vcomp_runitor.
    apply maponpaths_2. apply H.
Qed.

Lemma lwhisker_id_inj {a b : C} (f g : C⟦a, b⟧)
      (x y : f  ==> g)
  : identity a ◃ x = identity a ◃ y → x = y.
Proof.
  intro H.
  apply (vcomp_lcancel (lunitor _)).
  - apply is_invertible_2cell_lunitor.
  - etrans. apply pathsinv0, vcomp_lunitor.
    etrans. 2: apply vcomp_lunitor.
    apply maponpaths_2. apply H.
Qed.

(** α · (1 ⊗ ρ) = ρ *)
Lemma runitor_triangle {a b c: C} (f : C⟦a, b⟧) (g : C⟦b, c⟧)
  : rassociator f g (identity c) • (f ◃ runitor g) = runitor (f · g).
Proof.
  apply rwhisker_id_inj.
  etrans. 2: apply runitor_rwhisker_rwhisker.
  apply pathsinv0, rwhisker_vcomp.
Qed.

(* ρ = ρ ⊗ 1 *)
Lemma runitor_is_runitor_rwhisker (a : C)
  : runitor (identity a · identity a) = runitor (identity a) ▹ (identity a).
Proof.
  apply (vcomp_rcancel (runitor _ )).
  - apply is_invertible_2cell_runitor.
  - apply pathsinv0. apply vcomp_runitor .
Qed.

(* λ = 1 ⊗ λ *)
Lemma lunitor_is_lunitor_lwhisker (a : C)
  : lunitor (identity a · identity a) = identity a ◃ lunitor (identity a).
Proof.
  apply (vcomp_rcancel (lunitor _ )).
  - apply is_invertible_2cell_lunitor.
  - apply pathsinv0. apply vcomp_lunitor .
Qed.

(*  1 ⊗ ρ = 1 ⊗ λ *)
Lemma lwhisker_runitor_lunitor (a : C)
  : identity a  ◃ runitor (identity a) = identity a ◃ lunitor (identity a).
Proof.
  apply (vcomp_lcancel (rassociator _ _ _ )).
  - apply is_invertible_2cell_rassociator.
  - rewrite runitor_triangle.
    rewrite lunitor_lwhisker.
    apply runitor_is_runitor_rwhisker.
Qed.

Lemma runitor_lunitor_identity (a : C)
  : runitor (identity a) = lunitor (identity a).
Proof.
  apply (vcomp_lcancel (lunitor _ )).
  { apply is_invertible_2cell_lunitor. }
  etrans. { apply pathsinv0. apply vcomp_lunitor. }
  etrans. { apply maponpaths_2. apply lwhisker_runitor_lunitor. }
  apply maponpaths_2. apply (!lunitor_is_lunitor_lwhisker _).
Qed.

Lemma lunitor_runitor_identity (a : C)
  : lunitor (identity a) = runitor (identity a).
Proof.
  apply (! runitor_lunitor_identity _ ).
Qed.

End unitors.


(** Examples of laws derived by reversing morphisms or cells.  **)
Definition rinvunitor_triangle (C : prebicat) (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧)
  : (f ◃ rinvunitor g) • lassociator f g (identity c) = rinvunitor (f · g)
  := runitor_triangle (C := op2_prebicat C) f g.

Definition lunitor_triangle (C : prebicat) (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧)
  : lassociator (identity a) f g • (lunitor f ▹ g) = lunitor (f · g)
  := runitor_triangle (C := op1_prebicat C) g f.

