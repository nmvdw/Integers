Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import Integers.Bicategories.DispPrebicat. Import DispPrebicat.Notations.
Require Import Integers.Bicategories.DispProd.
Require Import Integers.Bicategories.TypePrebicat.
Require Import Integers.Bicategories.PointTypes.
Require Import Integers.Bicategories.EndTypes.

Local Open Scope cat.
Local Open Scope mor_disp_scope.
Local Open Scope bicategory_scope.

Definition disp3 : disp_prebicat type_prebicat
:= disp_dirprod_prebicat (disp_dirprod_prebicat pointtypes_prebicat endtypes_prebicat) (disp_dirprod_prebicat endtypes_prebicat endtypes_prebicat).

Definition TYPE3 : prebicat := total_prebicat disp3.
