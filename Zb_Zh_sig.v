(** We define a signature for Zb and Zh **)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

(*Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Examples.OneTypes.*)

Require Import sem.prelude.all.
Require Import sem.signature.hit_signature.
Require Import sem.signature.hit.

(*Require Import sem.algebra.one_types_polynomials.
Require Import sem.algebra.one_types_endpoints.
Require Import sem.algebra.one_types_homotopies.
Require Import sem.displayed_algebras.displayed_algebra.
Require Import sem.displayed_algebras.globe_over_lem.
 *)

Definition Zb_point_constr : poly_code
  := (C unit_one_type + I) + (I + I).

Inductive Zb_paths : UU :=
| sec : Zb_paths
| ret : Zb_paths.

Inductive Zb_homots : UU := .

Definition Zb_signature : hit_signature.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
  - exact Zb_point_constr.
  - exact Zb_paths.
  - intro j; induction j.
    + exact I.
    + exact I.
  - intro j; induction j.
    + exact (comp (comp (ι₁ _ _) (comp (ι₂ _ _) constr)) (comp (ι₂ _ _) (comp (ι₁ _ _) constr))).
    + exact (comp (comp (ι₂ _ _) (comp (ι₁ _ _) constr)) (comp (ι₂ _ _) (comp (ι₂ _ _) constr))).
  - intro j; induction j.
    + exact (id_e _ _).
    + exact (id_e _ _).
  - exact Zb_homots.
  - intro j; induction j.
  - intro j; induction j.
  - intro j; induction j.
  - intro j; induction j.
  - intro j; induction j.
  - intro j; induction j.
  - intro j; induction j.
  - intro j; induction j.
Defined.


Definition Zh_point_constr : poly_code
  := C unit_one_type + (I + I).

Inductive Zh_paths : UU :=
| sech : Zh_paths
| reth : Zh_paths.

Inductive Zh_homots : UU :=
| coh : Zh_homots.

Definition Zh_signature : hit_signature.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
  - exact Zh_point_constr.
  - exact Zh_paths.
  - intro j; induction j.
    + exact I.
    + exact I.
  - intro j; induction j.
    + exact (comp (comp (comp (ι₂ _ _) (ι₂ _ _)) constr) (comp (comp (ι₁ _ _) (ι₂ _ _)) constr)).
    + exact (comp (comp (comp (ι₁ _ _) (ι₂ _ _)) constr) (comp (comp (ι₂ _ _) (ι₂ _ _)) constr)).
  - intro j; induction j.
    + exact (id_e _ _).
    + exact (id_e _ _).
  - exact Zh_homots.
  - exact (λ _, I).
  - exact (λ _, C unit_one_type).
  - exact (λ _, @c _ _ unit_one_type tt).
  - exact (λ _, @c _ _ unit_one_type tt).
  - exact (λ _, comp (comp (comp (comp (comp (ι₁ _ _) (ι₂ _ _)) constr) (comp (comp (ι₂ _ _) (ι₂ _ _)) constr)) (comp (ι₁ _ _) (ι₂ _ _))) constr).
  - exact (λ _, comp (comp (ι₁ _ _) (ι₂ _ _)) constr).
  - intro j.
    refine (trans_e (inv_e (comp_assoc _ _ _)) _).
    refine (trans_e (inv_e (comp_assoc _ _ _)) _).
    refine (trans_e (path_constr sech (comp (comp (ι₁ _ _) (ι₂ _ _)) constr)) _).
    apply comp_id_r.
  - intro j.
    apply ap_constr.
    refine (trans_e (inv_e (comp_id_l _)) _).
    refine (trans_e (comp_assoc _ _ _) _).
    refine (trans_e (comp_assoc _ _ _) _).
    refine (trans_e (path_inr _ (path_inl _ (path_constr reth (id_e _ _)))) _).
    refine (trans_e (inv_e (comp_assoc _ _ _)) _).
    refine (trans_e (inv_e (comp_assoc _ _ _)) _).
    refine (trans_e (comp_id_l _) _).
    apply comp_id_l.
Defined.
