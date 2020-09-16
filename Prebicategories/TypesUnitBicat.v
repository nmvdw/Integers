(* The bicategory `type_bicat` of types, functions and unit.
2-cells are unit and thus sets, so we can use existing bicategory theory. *)

(* Displayed bicategory `pointtypes` over `type_bicat`, that adds points with unit as 2-cells.
Displayed bicategory `endtypes` over `type_bicat`, that adds endomorphisms with unit as 2-cells.
*)


Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.


Local Open Scope cat.
Local Open Scope bicategory_scope.
Local Open Scope mor_disp_scope.

(* type_bicat *)
Definition type_unit_bicat_data : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact Type.
  - intros X Y.
    exact (X → Y).
  - intros X Y f g.
    exact unit.
  - intros X x.
    exact x.
  - cbn. intros X Y Z f g x.
    exact (g (f x)).
  - intros. exact tt.
  - intros. exact tt.
  - intros. exact tt.
  - intros. exact tt.
  - intros. exact tt.
  - intros. exact tt.
  - intros. exact tt.
  - intros. exact tt.
  - intros. exact tt.
  - intros. exact tt.
Defined.

Definition type_unit_bicat_laws : prebicat_laws type_unit_bicat_data.
Proof.
  repeat (use tpair); cbn.
  - intros X Y f g x.
    induction x.
    exact (idpath tt).
  - intros X Y f g x.
    induction x.
    exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
  - intros. exact (idpath tt).
Qed.

Definition type_unit_prebicat : prebicat := type_unit_bicat_data ,, type_unit_bicat_laws.

Definition type_unit_bicat_cells : isaset_cells type_unit_prebicat
  := λ X Y f g, isasetunit.

Definition type_unit_bicat : bicat
  := type_unit_prebicat ,, type_unit_bicat_cells.

(* pointtypes *)
Definition pointtypes_disp_1 : disp_prebicat_1_id_comp_cells type_unit_bicat.
Proof.
  use tpair.
  - use tpair.
    + use tpair.
      * intro X.
        exact X.
      * intros X Y x y f.
        exact (f x = y).
    + use tpair.
      * cbn. intros X x.
        exact (idpath x).
      * cbn. intros X Y Z f g x y z p q.
        exact (maponpaths g p @ q).
  - unfold disp_2cell_struct.
    cbn. intros X Y f g t x y p q.
    exact unit.
Defined.

Definition pointtypes_disp_ops : disp_prebicat_ops pointtypes_disp_1.
Proof.
  repeat split; exact tt.
Qed.

Definition pointtypes_disp : disp_bicat type_unit_bicat.
Proof.
  use tpair.
  - use tpair.
    + exists pointtypes_disp_1.
      exact pointtypes_disp_ops.
    + abstract (repeat split; repeat intro; apply isapropunit).
  - intro X. cbn. intros Y f g t x y p q.
    exact isasetunit.
Defined.

Definition pointtypes : bicat := total_bicat pointtypes_disp.

(* endtypes *)
Definition endtypes_disp_1 : disp_prebicat_1_id_comp_cells type_unit_bicat.
Proof.
  use tpair.
  - use tpair.
    + use tpair.
      * intro X.
        exact (X → X).
      * intros X Y s r f.
        exact (∏ x, f (s x) = r (f x)).
    + use tpair.
      * cbn. intros X s x.
        exact (idpath (s x)).
      * cbn. intros X Y Z f g s r t p q x.
        exact (maponpaths g (p x) @ q (f x)).
  - unfold disp_2cell_struct.
    cbn. intros X Y f g t s r p q.
    exact unit.
Defined.

Definition endtypes_disp_ops : disp_prebicat_ops endtypes_disp_1.
Proof.
  repeat split; exact tt.
Qed.

Definition endtypes_disp : disp_bicat type_unit_bicat.
Proof.
  use tpair.
  - use tpair.
    + exists endtypes_disp_1.
      exact endtypes_disp_ops.
    + abstract (repeat split; repeat intro; apply isapropunit).
  - intro X. cbn. intros Y f g t x y p q.
    exact isasetunit.
Defined.

Definition endtypes : bicat := total_bicat endtypes_disp.

