(** Displayed prebicategory over the prebicategory `type_prebicat` of types with `unit` as 2-cells, adding points **)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.Bicategories.TypePrebicat.
Require Import Integers.Bicategories.DispPrebicat.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.

Definition pointtypes_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells type_prebicat.
Proof.
  use tpair.
  - use tpair.
    + use tpair.
      * intro X.
        exact X.
      * intros X Y x y f.
        exact (f x = y).
    + use tpair; cbn.
      * intros X x.
        exact (idpath x).
      * intros X Y Z f g x y z ff gg.
        exact (maponpaths g ff @ gg).
  - intro X.
    cbn.
    intros Y f g θ x y ff gg.
    exact unit.
Defined.

Definition pointtypes_disp_prebicat_ops
  : disp_prebicat_ops' pointtypes_disp_prebicat_1_id_comp_cells.
Proof.
  repeat split; exact tt.
Qed.

Definition pointtypes_prebicat : disp_prebicat type_prebicat.
Proof.
  use tpair.
  - exists pointtypes_disp_prebicat_1_id_comp_cells.
    exact pointtypes_disp_prebicat_ops.
  - abstract (repeat split; repeat intro; apply isapropunit).
Defined.

Definition pointtypes : prebicat := total_prebicat pointtypes_prebicat.
