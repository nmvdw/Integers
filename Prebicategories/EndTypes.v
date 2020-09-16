(** Displayed prebicategory over the prebicategory `type_prebicat` of types with `unit` as 2-cells, adding endomorphisms **)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.Prebicategories.TypePrebicat.
Require Import Integers.Prebicategories.DispPrebicat.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.

Definition endtypes_disp_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells type_prebicat.
Proof.
  use tpair.
  - use tpair.
    + use tpair.
      * intro X.
        exact (X → X).
      * intros X Y s r f.
        exact (∏ x, f (s x) = r (f x)).
    + use tpair; cbn.
      * intros X s x.
        exact (idpath (s x)).
      * intros X Y Z f g s r t p q x.
        exact (maponpaths g (p x) @ q (f x)).
  - intro X.
    cbn.
    intros Y f g θ s r p q.
    exact unit.
Defined.

Definition endtypes_disp_prebicat_ops
  : disp_prebicat_ops' endtypes_disp_prebicat_1_id_comp_cells.
Proof.
  repeat split; exact tt.
Qed.

Definition endtypes_prebicat : disp_prebicat type_prebicat.
Proof.
  use tpair.
  - exists endtypes_disp_prebicat_1_id_comp_cells.
    exact endtypes_disp_prebicat_ops.
  - abstract (repeat split; repeat intro; apply isapropunit).
Defined.

Definition endtypes : prebicat := total_prebicat endtypes_prebicat.
