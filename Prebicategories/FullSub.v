(** Fullsubprebicategories of a **)
(* Copied from UniMath/Bicategories/DisplayedBicats/Examples/FullSub.v *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
(*Require Import UniMath.CategoryTheory.Core.Functors.*)

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

(*Require Import Integers.Prebicategories.TypePrebicat.*)
Require Import Integers.Prebicategories.DispPrebicat. Import DispPrebicat.Notations.
(*Require Import Integers.Prebicategories.Invertible_2cells.
Require Import Integers.Prebicategories.PseudoFunctor.*)
(*Import PseudoFunctor.Notations.*)

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.

(* From  UniMath/Bicategories/DisplayedBicats/Examples/DisplayedCatToBicat.v *)
Definition is_chaotic
           {C : prebicat}
           (D : disp_prebicat C)
  : UU
  := ∏ (a b : C) (f g : a --> b) (α : f ==> g)
       (aa : D a) (bb : D b) (ff : aa -->[ f ] bb) (gg : aa -->[ g ] bb),
     iscontr (ff ==>[ α ] gg).

Definition isaprop_is_chaotic
           {C : prebicat}
           (D : disp_prebicat C)
  : isaprop (is_chaotic D).
Proof.
  repeat (apply impred ; intro).
  exact (isapropiscontr _).
Qed.

Section Disp_Prebicat_Cells_Unit.
  Context {C : prebicat} (D : disp_cat_data C).

  Definition disp_prebicat_cells_unit
    : disp_prebicat_1_id_comp_cells C
    := D ,, λ a b f g α aa bb ff gg, unit.

  Definition disp_prebicat_cells_unit_ops
    : disp_prebicat_ops' disp_prebicat_cells_unit.
  Proof.
    repeat use tpair; cbn; intros; exact tt.
  Defined.

  Definition disp_prebicat_cells_unit_data : disp_prebicat_data C
    := _ ,, disp_prebicat_cells_unit_ops.

  Lemma disp_prebicat_cells_unit_laws
    : disp_prebicat_laws disp_prebicat_cells_unit_data.
  Proof.
    repeat use tpair; red; intros; apply (proofirrelevance _ isapropunit).
  Qed.

  Definition disp_cell_unit_prebicat : disp_prebicat C
    := _ ,, disp_prebicat_cells_unit_laws.
End Disp_Prebicat_Cells_Unit.

(* From  UniMath/Bicategories/DisplayedBicats/Examples/FullSub.v *)
Section FullSubPrebicat.
  Variable (C : prebicat)
           (P : C → UU).

  Definition disp_fullsubprebicat : disp_prebicat C
    := disp_cell_unit_prebicat (disp_full_sub_data C P).

  Definition fullsubprebicat : prebicat := total_prebicat disp_fullsubprebicat.
End FullSubPrebicat.
