(*
 - Polynomial codes
 - Action of polynomials on the universe
 - Path endpoints
 - Interpretation of path endpoints as functions
 - Homotopy endpoint type
 - Interpretation of homotopy endpoints as paths
 - Signature for higher inductive types
From 'GrpdHITs/code/signature/hit_signature.v'
*)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

(** Type of polynomials **)
Inductive poly_code : UU :=
| C : UU → poly_code
| Id : poly_code
| plus : poly_code → poly_code → poly_code
| times : poly_code → poly_code → poly_code.

Notation "P + Q" := (plus P Q).
Notation "P * Q" := (times P Q).

(** Action of polynomials on the universe *)
Definition act
           (P : poly_code)
           (A : UU)
  : UU.
Proof.
  induction P as [X | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact X.
  - exact A.
  - exact (IHP₁ ⨿ IHP₂).
  - exact (IHP₁ × IHP₂).
Defined.

(** Type of endpoints **)
Inductive endpoint (A : poly_code) : poly_code → poly_code → UU :=
(** endpoints for identity and composition *)
| id_e : ∏ (P : poly_code), endpoint A P P
| comp : ∏ (P Q R : poly_code), endpoint A P Q → endpoint A Q R → endpoint A P R
(** endpoints for sums *)
| ι₁ : ∏ (P Q : poly_code), endpoint A P (P + Q)
| ι₂ : ∏ (P Q : poly_code), endpoint A Q (P + Q)
(** endpoints for products *)
| π₁ : ∏ (P Q : poly_code), endpoint A (P * Q) P
| π₂ : ∏ (P Q : poly_code), endpoint A (P * Q) Q
| pair : ∏ (P Q R : poly_code),
    endpoint A P Q -> endpoint A P R → endpoint A P (Q * R)
(** endpoints for constant *)
| c : ∏ (P : poly_code) (X : UU), X → endpoint A P (C X)
| fmap : ∏ {X Y : UU} (f : X → Y), endpoint A (C X) (C Y)
(** constructor *)
| constr : endpoint A A Id.

Arguments id {_} _.
Arguments comp {A} {P} {Q} {R} _ _.
Arguments ι₁ {_} P Q.
Arguments ι₂ {_} P Q.
Arguments π₁ {_} P Q.
Arguments π₂ {_} P Q.
Arguments pair {A} {P} {Q} {R} _ _.
Arguments c {_} P {_} _.
Arguments fmap {_} {X Y} f.
Arguments constr {_}.

(** Endpoints induce functions **)
Definition sem_endpoint_UU
           {A P Q : poly_code}
           (e : endpoint A P Q)
           {X : UU}
           (c : act A X → X)
  : act P X → act Q X.
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q
                  | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂
                  | P T t | C₁ C₂ f | ].
  - (* Identity *)
    exact (λ x, x).
  - (* Composition *)
    exact (λ x, IHe₂ (IHe₁ x)).
  - (* Left inclusion *)
    exact inl.
  - (* Right inclusion *)
    exact inr.
  - (* Left projection *)
    exact pr1.
  - (* Right projection *)
    exact pr2.
  - (* Pairing *)
    exact (λ x, IHe₁ x ,, IHe₂ x).
  - (* Constant *)
    exact (λ _, t).
  - (* Constant map *)
    exact f.
  - (* Constructor *)
    exact c.
Defined.

(**
Homotopy endpoints
Here:
- `A` is arguments of point constructor
- `I` is index for path constructors
- `S` is arguments for path constructors
- `l` and `r` are the left and right endpoint of the path constructors
- `R` is the point argument
- `T` is the path argument target
 *)
Inductive homot_endpoint
          {A : poly_code}
          {I : UU}
          {S : I → poly_code}
          (l : ∏ (j : I), endpoint A (S j) Id)
          (r : ∏ (j : I), endpoint A (S j) Id)
          {R : poly_code}
          {T : poly_code}
          (a b : endpoint A R T)
  : ∏ {W : poly_code},
    endpoint A R W → endpoint A R W → UU
  :=
  (** operations on 2-cells *)
  | refl_e : ∏ (P : poly_code)
               (e : endpoint A R P),
             homot_endpoint l r a b e e
  | inv_e : ∏ (P : poly_code)
              (e₁ e₂ : endpoint A R P),
            homot_endpoint l r a b e₁ e₂
            →
            homot_endpoint l r a b e₂ e₁
  | trans_e : ∏ (P : poly_code)
                (e₁ e₂ e₃ : endpoint A R P),
              homot_endpoint l r a b e₁ e₂
              →
              homot_endpoint l r a b e₂ e₃
              →
              homot_endpoint l r a b e₁ e₃
  | ap_e : ∏ (P₁ P₂ : poly_code)
             (e₁ e₂ : endpoint A R P₁)
             (e : endpoint A P₁ P₂),
           homot_endpoint
             l r a b
             e₁ e₂
           →
           homot_endpoint
             l r a b
             (comp e₁ e) (comp e₂ e)
  (** Associator and unitors *)
  | comp_assoc : ∏ (P₁ P₂ P₃ : poly_code)
                   (e₁ : endpoint A R P₁)
                   (e₂ : endpoint A P₁ P₂)
                   (e₃ : endpoint A P₂ P₃),
                 homot_endpoint
                   l r a b
                   (comp e₁ (comp e₂ e₃))
                   (comp (comp e₁ e₂) e₃)
  | comp_id_l : ∏ (P : poly_code)
                  (e : endpoint A R P),
                homot_endpoint
                  l r a b
                  (comp (id_e _ _) e)
                  e
  | comp_id_r : ∏ (P : poly_code)
                  (e : endpoint A R P),
                homot_endpoint
                  l r a b
                  (comp e (id_e _ _))
                  e
  (** Beta rules for product *)
  | pair_π₁ : ∏ (P₁ P₂ : poly_code)
                (e₁ : endpoint A R P₁)
                (e₂ : endpoint A R P₂),
              homot_endpoint
                l r a b
                (comp (pair e₁ e₂) (π₁ _ _))
                e₁
  | pair_π₂ : ∏ (P₁ P₂ : poly_code)
                (e₁ : endpoint A R P₁)
                (e₂ : endpoint A R P₂),
              homot_endpoint
                l r a b
                (comp (pair e₁ e₂) (π₂ _ _))
                e₂
  | path_pair : ∏ (P₁ P₂ : poly_code)
                  (e₁ e₂ : endpoint A R P₁)
                  (e₃ e₄ : endpoint A R P₂),
                homot_endpoint l r a b e₁ e₂
                →
                homot_endpoint l r a b e₃ e₄
                →
                homot_endpoint
                  l r a b
                  (pair e₁ e₃) (pair e₂ e₄)
  (** In categories, this one follows from uniqueness *) 
  | comp_pair : ∏ {P₁ P₂ P₃ : poly_code}
                  (e₁ : endpoint A R P₁)
                  (e₂ : endpoint A P₁ P₂)
                  (e₃ : endpoint A P₁ P₃),
                homot_endpoint
                  l r
                  a b
                  (comp e₁ (pair e₂ e₃))
                  (pair (comp e₁ e₂) (comp e₁ e₃))
  (** Rules for constant *)
  | comp_constant : ∏ (X : UU)
                      (x : X)
                      (P : poly_code)
                      (e : endpoint A R P),
                    homot_endpoint
                      l r a b
                      (comp e (c P x)) (c R x)
  (** Path constructor and path argument *)                
  | path_constr : ∏ (j : I)
                    (e : endpoint A R (S j)),
                  homot_endpoint
                    l r a b
                    (comp e (l j))
                    (comp e (r j))
  | path_arg : homot_endpoint l r a b a b.


Arguments refl_e {_ _ _ _ _ _ _ _ _ _}.
Arguments inv_e {_ _ _ _ _ _ _ _ _ _ _ _} _.
Arguments trans_e {_ _ _ _ _ _ _ _ _ _ _ _ _} _ _.
Arguments ap_e {_ _ _ _ _ _ _ _ _ _ _ _ _} _ _.
Arguments comp_assoc {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _.
Arguments comp_id_l {_ _ _ _ _ _ _ _ _ _} _.
Arguments comp_id_r {_ _ _ _ _ _ _ _ _ _} _.
Arguments pair_π₁ {_ _ _ _ _ _ _ _ _ _ _} _ _.
Arguments pair_π₂ {_ _ _ _ _ _ _ _ _ _ _} _ _.
Arguments path_pair {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _.
Arguments comp_pair {_ _ _ _ _ _ _ _ _ _ _ _} _ _ _.
Arguments comp_constant {_ _ _ _ _ _ _ _ _ _} _ {_} _.
Arguments path_constr {_ _ _ _ _ _ _ _ _} _ _.
Arguments path_arg {_ _ _ _ _ _ _ _ _}.

(** Interpretation of homotopy endpoints as paths **)
Definition sem_homot_endpoint_UU
           {A : poly_code}
           {I : UU}
           {S : I → poly_code}
           {l : ∏ (j : I), endpoint A (S j) Id}
           {r : ∏ (j : I), endpoint A (S j) Id}
           {R : poly_code}
           {T : poly_code}
           {a b : endpoint A R T}
           {W : poly_code}
           {s t : endpoint A R W}
           (h : homot_endpoint l r a b s t)
           (X : UU)
           (c : act A X → X)
           (pX : ∏ (i : I),
                 sem_endpoint_UU (l i) c
                 ~
                 sem_endpoint_UU (r i) c)
           (z : act R X)
           (p_arg : sem_endpoint_UU a c z = sem_endpoint_UU b c z)
  : sem_endpoint_UU s c z = sem_endpoint_UU t c z.
Proof.
  induction h as [P e | P e₁ e₂ p IHp | P e₁ e₂ e₃ p₁ IHP₁ p₂ IHP₂
                  | T₁ T₂ e₁ e₂ e₃ h IHh
                  | R₁ R₂ P e₁ e₂ e₃ | P e | P e
                  | P₁ P₂ e₁ e₂ | P₁ P₂ e₁ e₂
                  | T₁ T₂ e₁ e₂ e₃ e₄ p₁ IHp₁ p₂ IHp₂
                  | P₁ P₂ P₃ e₁ e₂ e₃
                  | Z x P e | j e | ].
  - (** identity path *)
    exact (idpath _).
  - (** inverse path *)
    exact (!IHp).
  - (** concatenation of paths *)
    exact (IHP₁ @ IHP₂).
  - (** ap on paths *)
    exact (maponpaths (sem_endpoint_UU e₃ c) IHh).
  - (** associator *)
    apply idpath.
  - (** left unitor *)
    apply idpath.
  - (** right unitor *)
    apply idpath.
  - (** first projection *)
    apply idpath.
  - (** second projection *)
    apply idpath.
  - (** pairing *)
    exact (pathsdirprod IHp₁ IHp₂).
  - (** composition before pair *)
    apply idpath.
  - (** composition with constant *)
    apply idpath.
  - (** path constructor *)
    exact (pX j _).
  - (** path argument *)
    exact p_arg.
Defined.

(**
The definition of a HIT signature for HITs of the shape:
Inductive H :=
| c : A H → H
| p : ∏ (j : I) (x : S j H), l j x = r j x
| s : ∏ (j : J) (x : R j H) (w : a j x = b j x), p j x w = q j x w
where we have    p j x w, q j x w : s j x = t j x
 *)
Definition hit_signature
  : UU
  := ∑ (A : poly_code),
     ∑ (I : UU),
     ∑ (S : I → poly_code),
     ∑ (l r : ∏ (j : I), endpoint A (S j) Id),
     ∑ (J : UU),
     ∑ (R : J → poly_code),
     ∑ (T : J → poly_code),
     ∑ (a b : ∏ (j : J), endpoint A (R j) (T j)),
     ∑ (s t : ∏ (j : J), endpoint A (R j) Id),
     (∏ (j : J), homot_endpoint l r (a j) (b j) (s j) (t j))
     ×
     (∏ (j : J), homot_endpoint l r (a j) (b j) (s j) (t j)).

(** Projections of HIT signature *)
Section Projections.
  Variable (Σ : hit_signature).
  
  Definition point_constr
    : poly_code
    := pr1 Σ.

  Definition path_label
    : UU
    := pr12 Σ.

  Definition path_source
    : path_label → poly_code
    := pr122 Σ.

  Definition path_left
    : ∏ (j : path_label), endpoint point_constr (path_source j) Id
    := pr1 (pr222 Σ).

  Definition path_right
    : ∏ (j : path_label), endpoint point_constr (path_source j) Id
    := pr12 (pr222 Σ).

  Definition homot_label
    : UU
    := pr122 (pr222 Σ).

  Definition homot_point_arg
    : homot_label → poly_code
    := pr1 (pr222 (pr222 Σ)).

  Definition homot_path_arg_target
    : homot_label → poly_code
    := pr12 (pr222 (pr222 Σ)).

  Definition homot_path_arg_left
    : ∏ (j : homot_label),
      endpoint
        point_constr
        (homot_point_arg j)
        (homot_path_arg_target j)
    := pr122 (pr222 (pr222 Σ)).

  Definition homot_path_arg_right
    : ∏ (j : homot_label),
      endpoint
        point_constr
        (homot_point_arg j)
        (homot_path_arg_target j)
    := pr1 (pr222 (pr222 (pr222 Σ))).

  Definition homot_left_endpoint
    : ∏ (j : homot_label),
      endpoint
        point_constr
        (homot_point_arg j)
        Id
    := pr12 (pr222 (pr222 (pr222 Σ))).

  Definition homot_right_endpoint
    : ∏ (j : homot_label),
      endpoint
        point_constr
        (homot_point_arg j)
        Id
    := pr122 (pr222 (pr222 (pr222 Σ))).

  Definition homot_left_path
    : ∏ (j : homot_label),
      homot_endpoint
        path_left path_right
        (homot_path_arg_left j)
        (homot_path_arg_right j)
        (homot_left_endpoint j)
        (homot_right_endpoint j)
    := pr1 (pr222 (pr222 (pr222 (pr222 Σ)))).

  Definition homot_right_path
    : ∏ (j : homot_label),
      homot_endpoint
        path_left path_right
        (homot_path_arg_left j)
        (homot_path_arg_right j)
        (homot_left_endpoint j)
        (homot_right_endpoint j)
    := pr2 (pr222 (pr222 (pr222 (pr222 Σ)))).
End Projections.
