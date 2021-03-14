(** 
 - Discrete displayed prebicategories
 - Full subprebicategories
We use the fact that can construct full subpreBIcategories from full subpreCATegories of prebicategories by adding `unit` as 2-cells.
From 'UniMath/Bicategories/DisplayedBicats/Examples/DisplayedCatToBicat.v' and 'FullSub.v' *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.Prebicategories.DispPrebicat. Import DispPrebicat.Notations.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.

(** Discrete displayed prebicategories **)
(* Given a displayed preCATegory, construct a displayed preBIcategory by using unit as 2-cells *)
(* From 'UniMath/Bicategories/DisplayedBicats/Examples/DisplayedCatToBicat.v' *)
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

(** Full subprebicategories **)
(* Construct the full subpreBIcategory from the full subCATegory *)
(* From 'UniMath/Bicategories/DisplayedBicats/Examples/FullSub.v' *)
Section FullSubPrebicat.
  Variable (C : prebicat)
           (P : C → UU).

  Definition disp_fullsubprebicat : disp_prebicat C
    := disp_cell_unit_prebicat (disp_full_sub_data C P).

  Definition fullsubprebicat : prebicat := total_prebicat disp_fullsubprebicat.
End FullSubPrebicat.
