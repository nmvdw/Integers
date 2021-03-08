(** We define a signature for Zb and for Zh **)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

(*Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.*)
Require Import UniMath.Bicategories.Core.Examples.OneTypes.

Require Import sem.prelude.all.
Require Import sem.signature.hit_signature.
Require Import sem.signature.hit.

(*Require Import sem.algebra.one_types_polynomials.
Require Import sem.algebra.one_types_endpoints.
Require Import sem.algebra.one_types_homotopies.
Require Import sem.displayed_algebras.displayed_algebra.
Require Import sem.displayed_algebras.globe_over_lem.
 *)


(** Zb **)
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


(** Zh  **)

Definition Zh_point_constr : poly_code
  := C unit_one_type + (I + I).

Inductive Zh_paths : UU :=
| sech : Zh_paths
| reth : Zh_paths.

Definition Zh_paths_args (j : Zh_paths) : poly_code := I.

Definition succ
  : endpoint Zh_point_constr I I
  := comp (comp (ι₁ _ _) (ι₂ _ _)) constr.

Definition pred
  : endpoint Zh_point_constr I I
  := comp (comp (ι₂ _ _) (ι₂ _ _)) constr.

Definition Zh_paths_lhs (j : Zh_paths) : endpoint Zh_point_constr (Zh_paths_args j) I.
Proof.
  induction j.
  - exact (comp pred succ).
  - exact (comp succ pred).
Defined.

Definition Zh_paths_rhs (j : Zh_paths) : endpoint Zh_point_constr (Zh_paths_args j) I
  := id_e _ _.
  
Inductive Zh_homots : UU :=
| coh : Zh_homots.

Definition Zh_homots_point_arg (j : Zh_homots) : poly_code := I.

Definition Zh_homots_point_left_endpoint (j : Zh_homots)
  : endpoint Zh_point_constr (Zh_homots_point_arg j) I
  := comp (comp succ pred) succ.

Definition Zh_homots_point_right_endpoint (j : Zh_homots)
           : endpoint Zh_point_constr (Zh_homots_point_arg j) I
  := succ.

Definition Zh_homots_point_lhs
           (j : Zh_homots)
  : homot_endpoint
      Zh_paths_lhs
      Zh_paths_rhs
      (c (Zh_homots_point_arg j) (tt : unit_one_type))
      (c (Zh_homots_point_arg j) (tt : unit_one_type))
      (Zh_homots_point_left_endpoint j)
      (Zh_homots_point_right_endpoint j)
  := trans_e
       (trans_e
          (inv_e (comp_assoc _ _ _))
          (path_constr sech succ))
       (comp_id_r _).
  
Definition Zh_homots_point_rhs
           (i : Zh_homots)
  : homot_endpoint
      Zh_paths_lhs
      Zh_paths_rhs
      (c (Zh_homots_point_arg i) (tt : unit_one_type))
      (c (Zh_homots_point_arg i) (tt : unit_one_type))
      (Zh_homots_point_left_endpoint i)
      (Zh_homots_point_right_endpoint i)
  := trans_e
       (ap_e succ (trans_e
                     (inv_e (comp_id_l _))
                     (path_constr reth (id_e _ _))))
       (trans_e
          (inv_e (comp_assoc _ _ _))
          (trans_e
             (comp_id_l _)
             (comp_id_l _))).
  
Definition Zh_signature : hit_signature.
Proof.
  simple refine (_ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _ ,, _  ,, _ ,, _ ,, _ ,, _).
  - exact Zh_point_constr.
  - exact Zh_paths.
  - exact Zh_paths_args.
  - exact Zh_paths_lhs.
  - exact Zh_paths_rhs.
  - exact Zh_homots.
  - exact Zh_homots_point_arg.
  - exact (λ _, C unit_one_type).
  - exact (λ _, @c _ _ unit_one_type tt).
  - exact (λ _, @c _ _ unit_one_type tt).
  - exact Zh_homots_point_left_endpoint.
  - exact Zh_homots_point_right_endpoint.
  - exact Zh_homots_point_lhs.
  - exact Zh_homots_point_rhs.
Defined.

