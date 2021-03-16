(*
 - Signature for ℤb
 - Signature for ℤh
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import Integers.signature.
Require Import Integers.Algebra.homotopies.

(** Signature for ℤb **)
Definition Zb_point_constr : poly_code
  := (C unit + Id) + (Id + Id).

Definition succb
  : endpoint Zb_point_constr Id Id
  := comp (comp (ι₂ _ _) (ι₁ _ _)) constr.

Definition pred₁
  : endpoint Zb_point_constr Id Id
  := comp (comp (ι₁ _ _) (ι₂ _ _)) constr.

Definition pred₂
  : endpoint Zb_point_constr Id Id
  := comp (comp (ι₂ _ _) (ι₂ _ _)) constr.

Inductive Zb_paths : UU :=
| sec : Zb_paths
| ret : Zb_paths.

Inductive Zb_homots : UU := .

Definition Zb_signature : hit_signature.
Proof.
  repeat simple refine (_ ,, _).
  - exact Zb_point_constr.
  - exact Zb_paths.
  - intro j; induction j.
    + exact Id.
    + exact Id.
  - intro j; induction j.
    + exact (comp succb pred₁).
    + exact (comp pred₂ succb).
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

(* Now `hit_algebra_type Zb_signature` is the ℤb-algebra prebicategory. *)


(** Signature for ℤh  **)
Definition Zh_point_constr : poly_code
  := C unit + (Id + Id).

Inductive Zh_paths : UU :=
| sech : Zh_paths
| reth : Zh_paths.

Definition Zh_paths_args (j : Zh_paths) : poly_code := Id.

Definition succ
  : endpoint Zh_point_constr Id Id
  := comp (comp (ι₁ _ _) (ι₂ _ _)) constr.

Definition pred
  : endpoint Zh_point_constr Id Id
  := comp (comp (ι₂ _ _) (ι₂ _ _)) constr.

Definition Zh_paths_lhs (j : Zh_paths) : endpoint Zh_point_constr (Zh_paths_args j) Id.
Proof.
  induction j.
  - exact (comp succ pred).
  - exact (comp pred succ).
Defined.

Definition Zh_paths_rhs (j : Zh_paths) : endpoint Zh_point_constr (Zh_paths_args j) Id
  := id_e _ _.
  
Inductive Zh_homots : UU :=
| coh : Zh_homots.

Definition Zh_homots_point_arg (j : Zh_homots) : poly_code := Id.

Definition Zh_homots_point_left_endpoint (j : Zh_homots)
  : endpoint Zh_point_constr (Zh_homots_point_arg j) Id
  := comp (comp succ pred) succ.

Definition Zh_homots_point_right_endpoint (j : Zh_homots)
           : endpoint Zh_point_constr (Zh_homots_point_arg j) Id
  := succ.

Definition Zh_homots_point_lhs
           (i : Zh_homots)
  : homot_endpoint
      Zh_paths_lhs
      Zh_paths_rhs
      (c (Zh_homots_point_arg i) tt)
      (c (Zh_homots_point_arg i) tt)
      (Zh_homots_point_left_endpoint i)
      (Zh_homots_point_right_endpoint i)
  := trans_e
       (ap_e succ (trans_e
                     (inv_e (comp_id_l _))
                     (path_constr sech (id_e _ _))))
       (trans_e
          (inv_e (comp_assoc _ _ _))
          (trans_e
             (comp_id_l _)
             (comp_id_l _))).

Definition Zh_homots_point_rhs
           (j : Zh_homots)
  : homot_endpoint
      Zh_paths_lhs
      Zh_paths_rhs
      (c (Zh_homots_point_arg j) tt)
      (c (Zh_homots_point_arg j) tt)
      (Zh_homots_point_left_endpoint j)
      (Zh_homots_point_right_endpoint j)
  := trans_e
       (trans_e
          (inv_e (comp_assoc _ _ _))
          (path_constr reth succ))
       (comp_id_r _).

Definition Zh_signature : hit_signature.
Proof.
  repeat simple refine (_ ,, _).
  - exact Zh_point_constr.
  - exact Zh_paths.
  - exact Zh_paths_args.
  - exact Zh_paths_lhs.
  - exact Zh_paths_rhs.
  - exact Zh_homots.
  - exact Zh_homots_point_arg.
  - exact (λ _, C unit).
  - exact (λ _, c Id tt).
  - exact (λ _, c Id tt).
  - exact Zh_homots_point_left_endpoint.
  - exact Zh_homots_point_right_endpoint.
  - exact Zh_homots_point_lhs.
  - exact Zh_homots_point_rhs.
Defined.

(* Now `hit_algebra_type Zh_signature` is the ℤh-algebra prebicategory. *)
