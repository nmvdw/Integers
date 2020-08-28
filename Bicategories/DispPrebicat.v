(** Displayed prebicategories are displayed bicategories over prebicategories, with general types (not sets) as displayed 2-cells **)
(** Copied from UniMath/Bicategories/DisplayedBicats/DispBicat.v **)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

Section disp_prebicat.

Context {C : prebicat}. (* <- This is the main difference with the original file *)

Local Notation "f' ==>[ x ] g'" := (disp_2cells x f' g') (at level 60).
Local Notation "f' <==[ x ] g'" := (disp_2cells x g' f') (at level 60, only parsing).

Definition disp_prebicat_ops' (D : disp_prebicat_1_id_comp_cells C) : UU
  :=   (∏ (a b : C) (f : C⟦a,b⟧) (x : D a) (y : D b) (f' : x -->[f] y),
        f' ==>[id2 _] f')
     × (∏ (a b : C) (f : C⟦a,b⟧) (x : D a) (y : D b) (f' : x -->[f] y),
        id_disp x ;; f' ==>[lunitor _] f')
     × (∏ (a b : C) (f : C⟦a,b⟧) (x : D a) (y : D b) (f' : x -->[f] y),
        f' ;; id_disp y ==>[runitor _] f')
     × (∏ (a b : C) (f : C⟦a,b⟧) (x : D a) (y : D b) (f' : x -->[f] y),
        id_disp x ;; f' <==[linvunitor _] f')
     × (∏ (a b : C) (f : C⟦a,b⟧) (x : D a) (y : D b) (f' : x -->[f] y),
        f' ;; id_disp y <==[rinvunitor _] f')
     × (∏ (a b c d : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧) (h : C⟦c,d⟧)
          (w : D a) (x : D b) (y : D c) (z : D d)
          (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z),
        (ff ;; gg) ;; hh ==>[rassociator _ _ _] ff ;; (gg ;; hh))
     × (∏ (a b c d : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧) (h : C⟦c,d⟧)
          (w : D a) (x : D b) (y : D c) (z : D d)
          (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z),
        ff ;; (gg ;; hh) ==>[lassociator _ _ _] (ff ;; gg) ;; hh)
     × (∏ (a b : C) (f g h : C⟦a,b⟧) (r : f ==> g) (s : g ==> h)
          (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y) (hh : x -->[h] y),
        ff ==>[r] gg  →  gg ==>[s] hh  →  ff ==>[r • s] hh)
     × (∏ (a b c : C) (f : C⟦a,b⟧) (g1 g2 : C⟦b,c⟧)
          (r : g1 ==> g2) (x : D a) (y : D b) (z : D c)
          (ff : x -->[f] y) (gg1 : y -->[g1] z) (gg2 : y -->[g2] z),
        gg1 ==>[r] gg2  →  ff ;; gg1  ==>[f ◃ r] ff ;; gg2)
     × (∏ (a b c : C) (f1 f2 : C⟦a,b⟧) (g : C⟦b,c⟧)
          (r : f1 ==> f2) (x : D a) (y : D b) (z : D c)
          (ff1 : x -->[f1] y) (ff2 : x -->[f2] y) (gg : y -->[g] z),
        ff1 ==>[r] ff2 → ff1 ;; gg ==>[r ▹ g] ff2 ;; gg).

Definition disp_prebicat_data : UU
  := ∑ D : disp_prebicat_1_id_comp_cells C, disp_prebicat_ops' D.

Coercion disp_prebicat_ob_mor_cells_1_id_comp_from_disp_prebicat_data
         (D : disp_prebicat_data)
  : disp_prebicat_1_id_comp_cells C
  := pr1 D.

Coercion disp_prebicat_ops_from_disp_prebicat_data (D : disp_prebicat_data)
  : disp_prebicat_ops' D
  := pr2 D.

(* ----------------------------------------------------------------------------------- *)
(** ** Data projections                                                                *)
(* ----------------------------------------------------------------------------------- *)

Section disp_prebicat_ops_projections.

Context {D : disp_prebicat_data}.

Definition disp_id2 {a b : C} {f : C⟦a,b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : f' ==>[id2 _] f'
  := pr1 (pr2 D) a b f x y f'.

Definition disp_lunitor {a b : C} {f : C⟦a,b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : id_disp x ;; f' ==>[lunitor _] f'
  := pr1 (pr2 (pr2 D)) a b f x y f'.

Definition disp_runitor {a b : C} {f : C⟦a,b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : f' ;; id_disp y ==>[runitor _] f'
  := pr1 (pr2 (pr2 (pr2 D))) _ _ f _ _ f'.

Definition disp_linvunitor
           {a b : C} {f : C⟦a,b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : id_disp x ;; f' <==[linvunitor _] f'
  := pr1 (pr2 (pr2 (pr2 (pr2 D)))) _ _ f _ _ f'.

Definition disp_rinvunitor
           {a b : C} {f : C⟦a,b⟧} {x : D a} {y : D b} (f' : x -->[f] y)
  : f' ;; id_disp y <==[rinvunitor _] f'
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 D))))) _ _ f _ _ f'.

Definition disp_rassociator
           {a b c d : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧} {h : C⟦c,d⟧}
       {w : D a} {x : D b} {y : D c} {z : D d}
       (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z)
  : (ff ;; gg) ;; hh ==>[rassociator _ _ _] ff ;; (gg ;; hh)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))) _ _ _ _ _ _ _ w _ _ _ ff gg hh.

Definition disp_lassociator
           {a b c d : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧} {h : C⟦c,d⟧}
           {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z)
  : ff ;; (gg ;; hh) ==>[lassociator _ _ _] (ff ;; gg) ;; hh
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))) _ _ _ _ _ _ _ w _ _ _ ff gg hh.

Definition disp_vcomp2
           {a b : C} {f g h : C⟦a,b⟧}
           {r : f ==> g} {s : g ==> h}
           {x : D a} {y : D b}
           {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y}
  : ff ==>[r] gg  →  gg ==>[s] hh  →  ff ==>[r • s] hh
  := λ rr ss,  pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))
                   _ _ _ _ _ _ _ _ _ _ _ _ rr ss.

Definition disp_lwhisker
           {a b c : C} {f : C⟦a,b⟧} {g1 g2 : C⟦b,c⟧}
           {r : g1 ==> g2}
           {x : D a} {y : D b} {z : D c}
           (ff : x -->[f] y) {gg1 : y -->[g1] z} {gg2 : y -->[g2] z}
  : gg1 ==>[r] gg2  →  ff ;; gg1  ==>[f ◃ r] ff ;; gg2
  := λ rr, pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))
               _ _ _ _ _ _ _ _ _ _ _ _ _ rr.

Definition disp_rwhisker
           {a b c : C} {f1 f2 : C⟦a,b⟧} {g : C⟦b,c⟧}
           {r : f1 ==> f2}
           {x : D a} {y : D b} {z : D c}
           {ff1 : x -->[f1] y} {ff2 : x -->[f2] y} (gg : y -->[g] z)
  : ff1 ==>[r] ff2 → ff1 ;; gg ==>[r ▹ g] ff2 ;; gg
  := λ rr, pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))
               _ _ _ _ _ _ _ _ _ _ _ _ _ rr.

End disp_prebicat_ops_projections.

Local Notation "rr •• ss" := (disp_vcomp2 rr ss) (at level 60).
Local Notation "ff ◃◃ rr" := (disp_lwhisker ff rr) (at level 60).
Local Notation "rr ▹▹ gg" := (disp_rwhisker gg rr) (at level 60).

Section disp_prebicat_laws.

Context (D : disp_prebicat_data).

Definition disp_id2_left_law : UU
  := ∏ (a b : C) (f g : C⟦a,b⟧) (η : f ==> g)
       (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
       (ηη : ff ==>[η] gg),
     disp_id2 _ •• ηη = transportb (λ α, _ ==>[α] _) (id2_left _) ηη.

Definition disp_id2_right_law : UU
  := ∏ (a b : C) (f g : C⟦a,b⟧) (η : f ==> g)
       (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
       (ηη : ff ==>[η] gg),
     ηη •• disp_id2 _ = transportb (λ α, _ ==>[α] _) (id2_right _) ηη.

Definition disp_vassocr_law : UU
  := ∏ (a b : C) (f g h k : C⟦a,b⟧) (η : f ==> g) (φ : g ==> h) (ψ : h ==> k)
       (x : D a) (y : D b)
       (ff : x -->[f] y) (gg : x -->[g] y) (hh : x -->[h] y) (kk : x -->[k] y)
       (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh) (ψψ : hh ==>[ψ] kk),
     ηη •• (φφ •• ψψ) =
     transportb (λ α, _ ==>[α] _) (vassocr _ _ _) ((ηη •• φφ) •• ψψ).

Definition disp_lwhisker_id2_law : UU
  := ∏ (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧)
       (x : D a) (y : D b) (z : D c) (ff : x -->[f] y) (gg : y -->[g] z),
     ff ◃◃ disp_id2 gg =
     transportb (λ α, _ ==>[α] _) (lwhisker_id2 _ _) (disp_id2 (ff ;; gg)).

Definition disp_id2_rwhisker_law : UU
  := ∏ (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧)
       (x : D a) (y : D b) (z : D c) (ff : x -->[f] y) (gg : y -->[g] z),
     disp_id2 ff ▹▹ gg =
     transportb (λ α, _ ==>[α] _) (id2_rwhisker _ _) (disp_id2 (ff ;; gg)).

Definition disp_lwhisker_vcomp_law : UU
  := ∏ (a b c : C) (f : C⟦a,b⟧) (g h i : C⟦b,c⟧)
      (η : g ==> h) (φ : h ==> i)
      (x : D a) (y : D b) (z : D c) (ff : x -->[f] y)
      (gg : y -->[g] z) (hh : y -->[h] z) (ii : y -->[i] z)
      (ηη : gg ==>[η] hh) (φφ : hh ==>[φ] ii),
     (ff ◃◃ ηη) •• (ff ◃◃ φφ) =
     transportb (λ α, _ ==>[α] _) (lwhisker_vcomp _ _ _) (ff ◃◃ (ηη •• φφ)).

Definition disp_rwhisker_vcomp_law : UU
  := ∏ (a b c : C) (f g h : C⟦a,b⟧) (i : C⟦b,c⟧) (η : f ==> g) (φ : g ==> h)
       (x : D a) (y : D b) (z : D c)
       (ff : x -->[f] y) (gg : x -->[g] y) (hh : x -->[h] y)
       (ii : y -->[i] z)
       (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh),
     (ηη ▹▹ ii) •• (φφ ▹▹ ii) =
     transportb (λ α, _ ==>[α] _) (rwhisker_vcomp _ _ _) ((ηη •• φφ) ▹▹ ii).

Definition disp_vcomp_lunitor_law : UU
  := ∏ (a b : C) (f g : C⟦a,b⟧) (η : f ==> g)
       (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
       (ηη : ff ==>[η] gg),
     (id_disp _ ◃◃ ηη) •• disp_lunitor gg =
     transportb (λ α, _ ==>[α] _) (vcomp_lunitor _ _ _) (disp_lunitor ff •• ηη).

Definition disp_vcomp_runitor_law : UU
  := ∏ (a b : C) (f g : C⟦a,b⟧) (η : f ==> g)
       (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y)
       (ηη : ff ==>[η] gg),
     (ηη ▹▹ id_disp _) •• disp_runitor gg =
     transportb (λ α, _ ==>[α] _) (vcomp_runitor _ _ _) (disp_runitor ff •• ηη).

Definition disp_lwhisker_lwhisker_law : UU
  := ∏ (a b c d : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧) (h i : c --> d) (η : h ==> i)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z) (ii : y -->[i] z)
       (ηη : hh ==>[η] ii),
     ff ◃◃ (gg ◃◃ ηη) •• disp_lassociator _ _ _ =
     transportb (λ α, _ ==>[α] _) (lwhisker_lwhisker _ _ _)
                (disp_lassociator _ _ _ •• (ff ;; gg ◃◃ ηη)).

Definition disp_rwhisker_lwhisker_law : UU
  := ∏ (a b c d : C) (f : C⟦a,b⟧) (g h : C⟦b,c⟧) (i : c --> d) (η : g ==> h)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : x -->[g] y) (hh : x -->[h] y) (ii : y -->[i] z)
       (ηη : gg ==>[η] hh),
     (ff ◃◃ (ηη ▹▹ ii)) •• disp_lassociator _ _ _ =
     transportb (λ α, _ ==>[α] _) (rwhisker_lwhisker _ _ _)
                (disp_lassociator _ _ _ •• ((ff ◃◃ ηη) ▹▹ ii)).

Definition disp_rwhisker_rwhisker_law : UU
  := ∏ (a b c d : C) (f g : C⟦a,b⟧) (h : C⟦b,c⟧) (i : c --> d) (η : f ==> g)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : w -->[g] x) (hh : x -->[h] y) (ii : y -->[i] z)
       (ηη : ff ==>[η] gg),
     disp_lassociator _ _ _ •• ((ηη ▹▹ hh) ▹▹ ii) =
     transportb (λ α, _ ==>[α] _) (rwhisker_rwhisker _ _ _)
                ((ηη ▹▹ hh ;; ii) •• disp_lassociator _ _ _).

Definition disp_vcomp_whisker_law : UU
  := ∏ (a b c : C) (f g : C⟦a,b⟧) (h i : C⟦b,c⟧)
       (η : f ==> g) (φ : h ==> i)
       (x : D a) (y : D b) (z : D c)
       (ff : x -->[f] y) (gg : x -->[g] y)
       (hh : y -->[h] z) (ii : y -->[i] z)
       (ηη : ff ==>[η] gg) (φφ : hh ==>[φ] ii),
     (ηη ▹▹ hh) •• (gg ◃◃ φφ) =
     transportb (λ α, _ ==>[α] _) (vcomp_whisker _ _) ((ff ◃◃ φφ) •• (ηη ▹▹ ii)).

Definition disp_lunitor_linvunitor_law : UU
  := ∏ (a b : C) (f : C⟦a,b⟧)
       (x : D a) (y : D b) (ff : x -->[f] y),
     disp_lunitor ff •• disp_linvunitor _ =
     transportb (λ α, _ ==>[α] _) (lunitor_linvunitor _) (disp_id2 (id_disp _ ;; ff)).

Definition disp_linvunitor_lunitor_law : UU
  := ∏ (a b : C) (f : C⟦a,b⟧)
       (x : D a) (y : D b) (ff : x -->[f] y),
     disp_linvunitor ff •• disp_lunitor _ =
     transportb (λ α, _ ==>[α] _) (linvunitor_lunitor _) (disp_id2 _).

Definition disp_runitor_rinvunitor_law : UU
  := ∏ (a b : C) (f : C⟦a,b⟧)
       (x : D a) (y : D b) (ff : x -->[f] y),
     disp_runitor ff •• disp_rinvunitor _ =
     transportb (λ α, _ ==>[α] _) (runitor_rinvunitor _) (disp_id2 _).

Definition disp_rinvunitor_runitor_law : UU
  := ∏ (a b : C) (f : C⟦a,b⟧)
       (x : D a) (y : D b) (ff : x -->[f] y),
     disp_rinvunitor ff •• disp_runitor _ =
     transportb (λ α, _ ==>[α] _) (rinvunitor_runitor _) (disp_id2 _).

Definition disp_lassociator_rassociator_law : UU
  := ∏ (a b c d : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧) (h : c --> d)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : x -->[g] y)
       (hh : y -->[h] z),
     disp_lassociator ff gg hh •• disp_rassociator _ _ _ =
     transportb (λ α, _ ==>[α] _) (lassociator_rassociator _ _ _ ) (disp_id2  _).

Definition disp_rassociator_lassociator_law : UU
  := ∏ (a b c d : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧) (h : c --> d)
       (w : D a) (x : D b) (y : D c) (z : D d)
       (ff : w -->[f] x) (gg : x -->[g] y)
       (hh : y -->[h] z),
     disp_rassociator ff gg hh •• disp_lassociator _ _ _ =
     transportb (λ α, _ ==>[α] _) (rassociator_lassociator _ _ _ ) (disp_id2 _).

Definition disp_runitor_rwhisker_law : UU
  := ∏ (a b c : C) (f : C⟦a,b⟧) (g : C⟦b,c⟧)
       (x : D a) (y : D b) (z : D c)
       (ff : x -->[f] y) (gg : y -->[g] z),
     disp_lassociator _ _ _ •• (disp_runitor ff ▹▹ gg) =
     transportb (λ α, _ ==>[α] _) (runitor_rwhisker _ _) (ff ◃◃ disp_lunitor gg).

Definition disp_lassociator_lassociator_law : UU
  := ∏ (a b c d e: C) (f : C⟦a,b⟧) (g : C⟦b,c⟧) (h : c --> d) (i : C⟦d,e⟧)
       (v : D a) (w : D b) (x : D c) (y : D d) (z : D e)
       (ff : v -->[f] w) (gg : w -->[g] x)
       (hh : x -->[h] y) (ii : y -->[i] z),

     (ff ◃◃ disp_lassociator gg hh ii) •• disp_lassociator _ _ _ ••
     (disp_lassociator _ _ _ ▹▹ ii) =
     transportb (λ α, _ ==>[α] _) (lassociator_lassociator _ _ _ _)
                (disp_lassociator ff gg _ •• disp_lassociator _ _ _).

(* ----------------------------------------------------------------------------------- *)
(** ** Laws                                                                            *)
(* ----------------------------------------------------------------------------------- *)

Definition disp_prebicat_laws : UU
  :=   disp_id2_left_law
     × disp_id2_right_law
     × disp_vassocr_law
     × disp_lwhisker_id2_law
     × disp_id2_rwhisker_law
     × disp_lwhisker_vcomp_law
     × disp_rwhisker_vcomp_law
     × disp_vcomp_lunitor_law
     × disp_vcomp_runitor_law
     × disp_lwhisker_lwhisker_law
     × disp_rwhisker_lwhisker_law
     × disp_rwhisker_rwhisker_law
     × disp_vcomp_whisker_law
     × disp_lunitor_linvunitor_law
     × disp_linvunitor_lunitor_law
     × disp_runitor_rinvunitor_law
     × disp_rinvunitor_runitor_law
     × disp_lassociator_rassociator_law
     × disp_rassociator_lassociator_law
     × disp_runitor_rwhisker_law
     × disp_lassociator_lassociator_law.

End disp_prebicat_laws.


(* ----------------------------------------------------------------------------------- *)
(** Laws projections                                                                   *)
(* ----------------------------------------------------------------------------------- *)

Definition disp_prebicat : UU
  := ∑ D : disp_prebicat_data, disp_prebicat_laws D.

Coercion disp_prebicat_data_from_disp_prebicat (D : disp_prebicat)
  : disp_prebicat_data
  := pr1 D.

Section disp_prebicat_law_projections.

Context {D : disp_prebicat}.

Definition disp_id2_left {a b : C} {f g : C⟦a,b⟧} {η : f ==> g}
           {x : D a} {y : D b} {ff : x -->[f] y} {gg : x -->[g] y}
           (ηη : ff ==>[η] gg)
  : disp_id2 _ •• ηη = transportb (λ α, _ ==>[α] _) (id2_left _) ηη
  := pr1 (pr2 D) _ _ _ _ _ x y ff gg ηη.

Definition disp_id2_right {a b : C} {f g : C⟦a,b⟧} {η : f ==> g}
           {x : D a} {y : D b} {ff : x -->[f] y} {gg : x -->[g] y}
           (ηη : ff ==>[η] gg)
  : ηη •• disp_id2 _ = transportb (λ α, _ ==>[α] _) (id2_right _) ηη
  := pr1 (pr2 (pr2 D)) _ _ _ _ _ _ _ _ _ ηη.

Definition disp_vassocr {a b : C} {f g h k : C⟦a,b⟧}
           {η : f ==> g} {φ : g ==> h} {ψ : h ==> k}
           {x : D a} {y : D b}
           {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y} {kk : x -->[k] y}
           (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh) (ψψ : hh ==>[ψ] kk)
  : ηη •• (φφ •• ψψ) =
    transportb (λ α, _ ==>[α] _) (vassocr _ _ _) ((ηη •• φφ) •• ψψ)
  := pr1 (pr2 (pr2 (pr2 D))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ηη φφ ψψ .

Definition disp_vassocr' {a b : C} {f g h k : C⟦a,b⟧}
           {η : f ==> g} {φ : g ==> h} {ψ : h ==> k}
           {x : D a} {y : D b}
           {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y} {kk : x -->[k] y}
           (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh) (ψψ : hh ==>[ψ] kk)
  : transportf (λ α, _ ==>[α] _) (vassocr _ _ _) (ηη •• (φφ •• ψψ)) =
    ((ηη •• φφ) •• ψψ).
Proof.
  use (transportf_transpose_left (P := λ x' : f ==> k, ff ==>[x'] kk)).
  apply disp_vassocr.
Defined.

Definition disp_lwhisker_id2 {a b c : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧}
           {x : D a} {y : D b} {z : D c} (ff : x -->[f] y) (gg : y -->[g] z)
  : ff ◃◃ disp_id2 gg =
    transportb (λ α, _ ==>[α] _) (lwhisker_id2 _ _) (disp_id2 (ff ;; gg))
  := pr1 (pr2 (pr2 (pr2 (pr2 D)))) _ _ _ _ _ _ _ _ ff gg.

Definition disp_id2_rwhisker {a b c : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧}
           {x : D a} {y : D b} {z : D c}
           (ff : x -->[f] y) (gg : y -->[g] z)
  : disp_id2 ff ▹▹ gg =
    transportb (λ α, _ ==>[α] _) (id2_rwhisker _ _) (disp_id2 (ff ;; gg))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 D))))) _ _ _ _ _ _ _ _ ff gg.

Definition disp_lwhisker_vcomp {a b c : C} {f : C⟦a,b⟧} {g h i : C⟦b,c⟧}
           {η : g ==> h} {φ : h ==> i}
           {x : D a} {y : D b} {z : D c} {ff : x -->[f] y}
           {gg : y -->[g] z} {hh : y -->[h] z} {ii : y -->[i] z}
           (ηη : gg ==>[η] hh) (φφ : hh ==>[φ] ii)
  : (ff ◃◃ ηη) •• (ff ◃◃ φφ) =
    transportb (λ α, _ ==>[α] _) (lwhisker_vcomp _ _ _) (ff ◃◃ (ηη •• φφ))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ηη φφ.

Definition disp_rwhisker_vcomp {a b c : C} {f g h : C⟦a,b⟧} {i : C⟦b,c⟧}
           {η : f ==> g} {φ : g ==> h}
           {x : D a} {y : D b} {z : D c}
           {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y} {ii : y -->[i] z}
           (ηη : ff ==>[η] gg) (φφ : gg ==>[φ] hh)
  : (ηη ▹▹ ii) •• (φφ ▹▹ ii) =
    transportb (λ α, _ ==>[α] _) (rwhisker_vcomp _ _ _) ((ηη •• φφ) ▹▹ ii)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))
         _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ηη φφ.

Definition disp_vcomp_lunitor {a b : C} {f g : C⟦a,b⟧} {η : f ==> g}
           {x : D a} {y : D b} {ff : x -->[f] y} {gg : x -->[g] y}
           (ηη : ff ==>[η] gg)
  : (id_disp _ ◃◃ ηη) •• disp_lunitor gg =
    transportb (λ α, _ ==>[α] _) (vcomp_lunitor _ _ _) (disp_lunitor ff •• ηη)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))) _ _ _ _ _ _ _ _ _  ηη.

Definition disp_vcomp_runitor {a b : C} {f g : C⟦a,b⟧} {η : f ==> g}
           {x : D a} {y : D b} {ff : x -->[f] y} {gg : x -->[g] y}
           (ηη : ff ==>[η] gg)
  : (ηη ▹▹ id_disp _) •• disp_runitor gg =
    transportb (λ α, _ ==>[α] _) (vcomp_runitor _ _ _) (disp_runitor ff •• ηη)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))) _ _ _ _ _ _ _ _ _  ηη.

Definition disp_lwhisker_lwhisker {a b c d : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧}
           {h i : c --> d} {η : h ==> i}
           {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) (gg : x -->[g] y) {hh : y -->[h] z} {ii : y -->[i] z}
           (ηη : hh ==>[η] ii)
  : ff ◃◃ (gg ◃◃ ηη) •• disp_lassociator _ _ _ =
    transportb (λ α, _ ==>[α] _) (lwhisker_lwhisker _ _ _)
               (disp_lassociator _ _ _ •• (ff ;; gg ◃◃ ηη))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))
         _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ ηη.

Definition disp_rwhisker_lwhisker {a b c d : C} {f : C⟦a,b⟧} {g h : C⟦b,c⟧}
           {i : c --> d} {η : g ==> h}
           {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) {gg : x -->[g] y} {hh : x -->[h] y} (ii : y -->[i] z)
           (ηη : gg ==>[η] hh)
  : (ff ◃◃ (ηη ▹▹ ii)) •• disp_lassociator _ _ _ =
    transportb (λ α, _ ==>[α] _) (rwhisker_lwhisker _ _ _)
               (disp_lassociator _ _ _ •• ((ff ◃◃ ηη) ▹▹ ii))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))))
         _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ ηη.

Definition disp_rwhisker_rwhisker {a b c d : C} {f g : C⟦a,b⟧} {h : C⟦b,c⟧}
           (i : c --> d) (η : f ==> g)
           {w : D a} {x : D b} {y : D c} {z : D d}
           {ff : w -->[f] x} {gg : w -->[g] x} (hh : x -->[h] y) (ii : y -->[i] z)
           (ηη : ff ==>[η] gg)
  : disp_lassociator _ _ _ •• ((ηη ▹▹ hh) ▹▹ ii) =
    transportb (λ α, _ ==>[α] _) (rwhisker_rwhisker _ _ _)
               ((ηη ▹▹ hh ;; ii) •• disp_lassociator _ _ _)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))
         _ _ _ _ _ _ _ _ _  _ _ _ _ _ _ _ _ ηη.

Definition disp_vcomp_whisker {a b c : C} {f g : C⟦a,b⟧} {h i : C⟦b,c⟧}
           (η : f ==> g) (φ : h ==> i)
           (x : D a) (y : D b) (z : D c)
           (ff : x -->[f] y) (gg : x -->[g] y) (hh : y -->[h] z) (ii : y -->[i] z)
           (ηη : ff ==>[η] gg) (φφ : hh ==>[φ] ii)
  : (ηη ▹▹ hh) •• (gg ◃◃ φφ) =
    transportb (λ α, _ ==>[α] _) (vcomp_whisker _ _) ((ff ◃◃ φφ) •• (ηη ▹▹ ii))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))))))
         _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ηη φφ.

Definition disp_lunitor_linvunitor {a b : C} {f : C⟦a,b⟧}
           {x : D a} {y : D b} (ff : x -->[f] y)
  : disp_lunitor ff •• disp_linvunitor _ =
    transportb (λ α, _ ==>[α] _) (lunitor_linvunitor _) (disp_id2 (id_disp _ ;; ff))
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))))
         _ _ _ _ _ ff.

Definition disp_linvunitor_lunitor {a b : C} {f : C⟦a,b⟧}
           {x : D a} {y : D b} (ff : x -->[f] y)
  : disp_linvunitor ff •• disp_lunitor _ =
    transportb (λ α, _ ==>[α] _) (linvunitor_lunitor _) (disp_id2 _)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))))) _ _ _ _ _ ff.

Definition disp_runitor_rinvunitor {a b : C} {f : C⟦a,b⟧}
           {x : D a} {y : D b} (ff : x -->[f] y)
  : disp_runitor ff •• disp_rinvunitor _ =
    transportb (λ α, _ ==>[α] _) (runitor_rinvunitor _) (disp_id2 _)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))))))))) _ _ _ _ _ ff.

Definition disp_rinvunitor_runitor {a b : C} {f : C⟦a,b⟧}
           {x : D a} {y : D b} (ff : x -->[f] y)
  : disp_rinvunitor ff •• disp_runitor _ =
    transportb (λ α, _ ==>[α] _) (rinvunitor_runitor _) (disp_id2 _)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))))))) _ _ _ _ _ ff.

Definition disp_lassociator_rassociator {a b c d : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧}
           {h : c --> d} {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z)
  : disp_lassociator ff gg hh •• disp_rassociator _ _ _ =
    transportb (λ α, _ ==>[α] _) (lassociator_rassociator _ _ _ ) (disp_id2  _)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))))))))
         _ _ _ _ _ _ _ _ _ _ _ ff gg hh.

Definition disp_rassociator_lassociator
           {a b c d : C} (f : C⟦a,b⟧) {g : C⟦b,c⟧} {h : c --> d}
           {w : D a} {x : D b} {y : D c} {z : D d}
           (ff : w -->[f] x) (gg : x -->[g] y)
           (hh : y -->[h] z)
  : disp_rassociator ff gg hh •• disp_lassociator _ _ _ =
    transportb (λ α, _ ==>[α] _) (rassociator_lassociator _ _ _ ) (disp_id2 _)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))))))))))))
         _ _ _ _ _ _ _ _ _ _ _ ff gg hh.

Definition disp_runitor_rwhisker {a b c : C} {f : C⟦a,b⟧} {g : C⟦b,c⟧}
           {x : D a} {y : D b} {z : D c} (ff : x -->[f] y) (gg : y -->[g] z)
  : disp_lassociator _ _ _ •• (disp_runitor ff ▹▹ gg) =
    transportb (λ α, _ ==>[α] _) (runitor_rwhisker _ _) (ff ◃◃ disp_lunitor gg)
  := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))))))))))
         _ _ _ _ _ _ _ _ ff gg.

Definition disp_lassociator_lassociator {a b c d e: C} {f : C⟦a,b⟧} {g : C⟦b,c⟧}
           {h : c --> d} {i : C⟦d,e⟧}
           {v : D a} {w : D b} {x : D c} {y : D d} {z : D e}
           (ff : v -->[f] w) (gg : w -->[g] x) (hh : x -->[h] y) (ii : y -->[i] z)
  : (ff ◃◃ disp_lassociator gg hh ii) •• disp_lassociator _ _ _ ••
    (disp_lassociator _ _ _ ▹▹ ii) =
    transportb (λ α, _ ==>[α] _) (lassociator_lassociator _ _ _ _)
               (disp_lassociator ff gg _ •• disp_lassociator _ _ _)
  := pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2
            (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))))))))))))))
         _ _ _ _ _ _ _ _ _ _ _ _ _ _ ff gg hh ii.

End disp_prebicat_law_projections.



(* ----------------------------------------------------------------------------------- *)
(** ** Total bicategory of a displayed bicategory                                      *)
(* ----------------------------------------------------------------------------------- *)

Section total_prebicat.

Variable D : disp_prebicat.

Definition total_prebicat_1_data : precategory_data
  := total_category_ob_mor D ,, total_category_id_comp D.


Definition total_prebicat_cell_struct : prebicat_2cell_struct (total_category_ob_mor D)
  := λ a b f g, ∑ η : pr1 f ==> pr1 g, pr2 f ==>[η] pr2 g.

Definition total_prebicat_1_id_comp_cells : prebicat_1_id_comp_cells
  := (total_prebicat_1_data,, total_prebicat_cell_struct).


Definition total_prebicat_2_id_comp_struct
  : prebicat_2_id_comp_struct total_prebicat_1_id_comp_cells.
Proof.
  repeat split; cbn; unfold total_prebicat_cell_struct.
  - intros. exists (id2 _). exact (disp_id2 _).
  - intros. exists (lunitor _). exact (disp_lunitor _).
  - intros. exists (runitor _). exact (disp_runitor _).
  - intros. exists (linvunitor _). exact (disp_linvunitor _).
  - intros. exists (rinvunitor _). exact (disp_rinvunitor _).
  - intros. exists (rassociator _ _ _).
    exact (disp_rassociator _ _ _).
  - intros. exists (lassociator _ _ _).
    exact (disp_lassociator _ _ _).
  - intros a b f g h r s. exists (pr1 r • pr1 s).
    exact (pr2 r •• pr2 s).
  - intros a b d f g1 g2 r. exists (pr1 f ◃ pr1 r).
    exact (pr2 f ◃◃ pr2 r).
  - intros a b c f1 f2 g r. exists (pr1 r ▹ pr1 g).
    exact (pr2 r ▹▹ pr2 g).
Defined.

Definition total_prebicat_data : prebicat_data
  := _ ,, total_prebicat_2_id_comp_struct.

Lemma total_prebicat_laws : prebicat_laws total_prebicat_data.
Proof.
  repeat split; intros.
  - use total2_paths_b.
    + apply id2_left.
    + apply disp_id2_left.
  - use total2_paths_b.
    + apply id2_right.
    + apply disp_id2_right.
  - use total2_paths_b.
    + apply vassocr.
    + apply disp_vassocr.
  - use total2_paths_b.
    + apply lwhisker_id2.
    + apply disp_lwhisker_id2.
  - use total2_paths_b.
    + apply id2_rwhisker.
    + apply disp_id2_rwhisker.
  - use total2_paths_b.
    + apply lwhisker_vcomp.
    + apply disp_lwhisker_vcomp.
  - use total2_paths_b.
    + apply rwhisker_vcomp.
    + apply disp_rwhisker_vcomp.
  - use total2_paths_b.
    + apply vcomp_lunitor.
    + apply disp_vcomp_lunitor.
  - use total2_paths_b.
    + apply vcomp_runitor.
    + apply disp_vcomp_runitor.
  - use total2_paths_b.
    + apply lwhisker_lwhisker.
    + apply disp_lwhisker_lwhisker.
  - use total2_paths_b.
    + apply rwhisker_lwhisker.
    + apply disp_rwhisker_lwhisker.
  - use total2_paths_b.
    + apply rwhisker_rwhisker.
    + apply disp_rwhisker_rwhisker.
  - use total2_paths_b.
    + apply vcomp_whisker.
    + apply disp_vcomp_whisker.
  - use total2_paths_b.
    + apply lunitor_linvunitor.
    + apply disp_lunitor_linvunitor.
  - use total2_paths_b.
    + apply linvunitor_lunitor.
    + apply disp_linvunitor_lunitor.
  - use total2_paths_b.
    + apply runitor_rinvunitor.
    + apply disp_runitor_rinvunitor.
  - use total2_paths_b.
    + apply rinvunitor_runitor.
    + apply disp_rinvunitor_runitor.
  - use total2_paths_b.
    + apply lassociator_rassociator.
    + apply disp_lassociator_rassociator.
  - use total2_paths_b.
    + apply rassociator_lassociator.
    + apply disp_rassociator_lassociator.
  - use total2_paths_b.
    + apply runitor_rwhisker.
    + apply disp_runitor_rwhisker.
  - use total2_paths_b.
    + apply lassociator_lassociator.
    + apply disp_lassociator_lassociator.
Defined.

Definition total_prebicat : prebicat := _ ,, total_prebicat_laws.

End total_prebicat.

End disp_prebicat.

Arguments disp_prebicat_1_id_comp_cells _ : clear implicits.
Arguments disp_prebicat_data _ : clear implicits.
Arguments disp_prebicat _ : clear implicits.
Arguments disp_bicat _ : clear implicits.


Module Notations.

Export Bicat.Notations.

Notation "f' ==>[ x ] g'" := (disp_2cells x f' g') (at level 60).
Notation "f' <==[ x ] g'" := (disp_2cells x g' f') (at level 60, only parsing).
Notation "rr •• ss" := (disp_vcomp2 rr ss) (at level 60).
Notation "ff ◃◃ rr" := (disp_lwhisker ff rr) (at level 60).
Notation "rr ▹▹ gg" := (disp_rwhisker gg rr) (at level 60).

End Notations.
