(* Definitions of:
- The prebicategory of types, functions and unit: `type_prebicat_unit`
- The pregicategory of types, functions and homotopies: `type_prebicat`
*)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Local Open Scope cat.
Local Open Scope bicategory_scope.

(* The prebicategory with unit as 2-cells*)
Definition type_prebicat_unit_data : prebicat_data.
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

Definition type_prebicat_unit_laws : prebicat_laws type_prebicat_unit_data.
Proof.
  repeat (use tpair); cbn.
  - intros X Y f g x.
    induction x.
    apply idpath.
  - intros.
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

Definition type_prebicat_unit : prebicat.
Proof.
  unfold prebicat.
  exists type_prebicat_unit_data.
  exact type_prebicat_unit_laws.
Defined.


(** The prebicategory with ~ as 2-cells **)
Definition type_prebicat_data : prebicat_data.
Proof.
  use build_prebicat_data.
  - exact Type.
  - intros X Y.
    exact (X → Y).
  - intros X Y f g.
    exact (f ~ g).
  - intros X x.
    exact x.
  - intros X Y Z f g x.
    exact (g (f x)).
  - cbn. intros X Y f.
    exact (homotrefl f).
  - cbn. intros X Y f g h θ γ.
    exact (homotcomp θ γ).
  - cbn. intros X Y Z f g h θ.
    exact (funhomotsec f θ).
  - cbn. intros X Y Z f g h θ.
    exact (homotfun θ h).
  - cbn. intros X Y f x.
    exact (idpath (f x)).
  - cbn. intros X Y f x.
    exact (idpath (f x)).
  - cbn. intros X Y f x.
    exact (idpath (f x)).
  - cbn. intros X Y f x.
    exact (idpath (f x)).
  - cbn. intros W X Y Z f g h x.
    exact (idpath (h (g (f x)))).
  - cbn. intros W X Y Z f g h x.
    exact (idpath (h (g (f x)))).
Defined.

Definition type_prebicat_laws : prebicat_laws type_prebicat_data.
Proof.
  repeat (use tpair); cbn.
  - intros X Y f g θ.
    exact (idpath θ).
  - intros X Y f g θ.
    apply funextsec.
    intro x.
    apply pathscomp0rid.
  - intros X Y f g h k θ γ τ.
    apply funextsec.
    intro x.
    apply path_assoc.
  - intros X Y Z f g.
    apply idpath.
  - intros X Y Z f g.
    apply idpath.
  - intros X Y Z f g h i θ γ.
    apply funextsec.
    intro x.
    apply idpath.
  - intros X Y Z f g h i θ γ.
    apply funextsec.
    intro x.
    unfold homotcomp, homotfun.
    apply (! maponpathscomp0 _ _ _ ).
  - intros X Y f g θ.
    apply funextsec.
    intro x.
    apply pathscomp0rid.
  - intros X Y f g θ.
    apply funextsec.
    intro x.
    unfold homotcomp, homotfun.
    simpl.
    etrans.
    + apply pathscomp0rid.
    + apply maponpathsidfun.
  - intros X Y Z W f g h i θ.
    apply funextsec.
    intro x.
    unfold homotcomp, homotfun.
    apply pathscomp0rid.
  - intros X Y Z W f g h i θ.
    apply funextsec.
    intro x.
    apply pathscomp0rid.
  - intros X Y Z f W g h i θ.
    apply funextsec.
    intro x.
    unfold homotcomp, homotfun.
    simpl.
    etrans.
    + apply maponpathscomp.
    + apply (!pathscomp0rid _ ).
  - intros X Y Z f g h i θ γ.
    apply funextsec.
    intro x.
    unfold homotcomp, homotfun, funhomotsec.
    induction (θ x).
    apply (! pathscomp0rid _).
  - intros X Y f. apply idpath.
  - intros X Y f. apply idpath.
  - intros X Y f. apply idpath.
  - intros X Y f. apply idpath.
  - intros X Y Z W f g h.
    apply idpath.
  - intros X Y Z W f g h.
    apply idpath.
  - intros X Y Z f g.
    apply idpath.
  - intros X Y Z W V f g h i.
    apply idpath.
Qed.

Definition type_prebicat : prebicat.
Proof.
  exists type_prebicat_data.
  exact type_prebicat_laws.
Defined.
