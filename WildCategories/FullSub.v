(** Full sub-wild categories of a wild category**)
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
Require Import Integers.WildCategories.WildCat.
Require Import Integers.WildCategories.DispWildCat. Import DispWildCat.Notations.
(*Require Import Integers.Prebicategories.Invertible_2cells.
Require Import Integers.Prebicategories.PseudoFunctor.*)
(*Import PseudoFunctor.Notations.*)

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.

Definition is_chaotic {C : wild_cat} (D : disp_wild_cat C) : UU
  := ∏ {a b : C} {f g : a --> b} (θ : f ==> g)
       {aa : D a} {bb : D b} (ff : aa -->[ f ] bb) (gg : aa -->[ g ] bb),
     iscontr (ff ==>[ θ ] gg).

Definition isaprop_is_chaotic {C : wild_cat} (D : disp_wild_cat C)
  : isaprop (is_chaotic D).
Proof.
  repeat (apply impred; intro).
  exact (isapropiscontr _).
Qed.

Section DispWildCatCellsUnit.
  Context {C : wild_cat} (D : disp_wild_cat C).

  Definition disp_cells_unit_data : disp_wild_cat_1_id_comp_cells C.
  Proof.
    exists D.
    exact (λ a b f g θ aa bb ff gg, unit).
  Defined.

  Definition disp_cells_unit : disp_wild_cat C.
  Proof.
    use tpair.
    - exact disp_cells_unit_data.
    - repeat split.
  Defined.
End DispWildCatCellsUnit.
