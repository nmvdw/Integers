(*
 - Displayed Wild categories
From 'UniMath/Bicategories/DisplayedBicats/DispBicat.v'
*)

Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.DisplayedBicats.DispBicat.

Require Import WildCategories.WildCat.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(* Transport of displayed cells *)
Notation disp_wild_cat_1_id_comp_cells := disp_prebicat_1_id_comp_cells.


(* Operations *)
Section disp_wild_cat.
  Context {C : wild_cat}.
  
  Local Notation "f' ==>[ x ] g'" := (disp_2cells x f' g') (at level 60).
  Local Notation "f' <==[ x ] g'" := (disp_2cells x g' f') (at level 60, only parsing).

  Definition disp_wild_cat_ops (D : disp_wild_cat_1_id_comp_cells C) : UU
  :=   (∏ (a b : C) (f : a --> b) (x : D a) (y : D b) (f' : x -->[f] y),
        f' ==>[id2 _] f')
     × (∏ (a b : C) (f : a --> b) (x : D a) (y : D b) (f' : x -->[f] y),
        id_disp x ;; f' ==>[lunitor _] f')
     × (∏ (a b : C) (f : a --> b) (x : D a) (y : D b) (f' : x -->[f] y),
        f' ;; id_disp y ==>[runitor _] f')
     × (∏ (a b : C) (f : a --> b) (x : D a) (y : D b) (f' : x -->[f] y),
        id_disp x ;; f' <==[linvunitor _] f')
     × (∏ (a b : C) (f : a --> b) (x : D a) (y : D b) (f' : x -->[f] y),
        f' ;; id_disp y <==[rinvunitor _] f')
     × (∏ (a b c d : C) (f : a --> b) (g : b --> c) (h : c --> d)
          (w : D a) (x : D b) (y : D c) (z : D d)
          (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z),
        (ff ;; gg) ;; hh ==>[rassociator _ _ _] ff ;; (gg ;; hh))
     × (∏ (a b c d : C) (f : a --> b) (g : b --> c) (h : c --> d)
          (w : D a) (x : D b) (y : D c) (z : D d)
          (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z),
        ff ;; (gg ;; hh) ==>[lassociator _ _ _] (ff ;; gg) ;; hh)
     × (∏ (a b : C) (f g h : a --> b) (r : f ==> g) (s : g ==> h)
          (x : D a) (y : D b) (ff : x -->[f] y) (gg : x -->[g] y) (hh : x -->[h] y),
        ff ==>[r] gg  →  gg ==>[s] hh  →  ff ==>[r • s] hh)
     × (∏ (a b c : C) (f : a --> b) (g1 g2 : b --> c)
          (r : g1 ==> g2) (x : D a) (y : D b) (z : D c)
          (ff : x -->[f] y) (gg1 : y -->[g1] z) (gg2 : y -->[g2] z),
        gg1 ==>[r] gg2  →  ff ;; gg1  ==>[f ◃ r] ff ;; gg2)
     × (∏ (a b c : C) (f1 f2 : a --> b) (g : b --> c)
          (r : f1 ==> f2) (x : D a) (y : D b) (z : D c)
          (ff1 : x -->[f1] y) (ff2 : x -->[f2] y) (gg : y -->[g] z),
        ff1 ==>[r] ff2 → ff1 ;; gg ==>[r ▹ g] ff2 ;; gg).

  Definition disp_wild_cat : UU
    := ∑ D : disp_wild_cat_1_id_comp_cells C, disp_wild_cat_ops D.

  Coercion disp_wild_cat_ob_mor_cells_1_id_comp_from_disp_wild_cat_data
           (D : disp_wild_cat)
    : disp_wild_cat_1_id_comp_cells C
    := pr1 D.

  Coercion disp_wild_cat_ops_from_disp_wild_cat_data (D : disp_wild_cat)
    : disp_wild_cat_ops D
    := pr2 D.

  (* Data projections *)
  Section disp_wild_cat_ops_projections.
    Context {D : disp_wild_cat}.

    Definition disp_id2 {a b : C} {f : a --> b} {x : D a} {y : D b} (f' : x -->[f] y)
      : f' ==>[id2 _] f'
      := pr1 (pr2 D) a b f x y f'.
    
    Definition disp_lunitor {a b : C} {f : a --> b} {x : D a} {y : D b} (f' : x -->[f] y)
      : id_disp x ;; f' ==>[lunitor _] f'
      := pr1 (pr2 (pr2 D)) a b f x y f'.
    
    Definition disp_runitor {a b : C} {f : a --> b} {x : D a} {y : D b} (f' : x -->[f] y)
      : f' ;; id_disp y ==>[runitor _] f'
      := pr1 (pr2 (pr2 (pr2 D))) _ _ f _ _ f'.

    Definition disp_linvunitor
               {a b : C} {f : a --> b} {x : D a} {y : D b} (f' : x -->[f] y)
      : id_disp x ;; f' <==[linvunitor _] f'
      := pr1 (pr2 (pr2 (pr2 (pr2 D)))) _ _ f _ _ f'.

    Definition disp_rinvunitor
               {a b : C} {f : a --> b} {x : D a} {y : D b} (f' : x -->[f] y)
      : f' ;; id_disp y <==[rinvunitor _] f'
      := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 D))))) _ _ f _ _ f'.
    
    Definition disp_rassociator
               {a b c d : C} {f : a --> b} {g : b --> c} {h : c --> d}
               {w : D a} {x : D b} {y : D c} {z : D d}
               (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z)
      : (ff ;; gg) ;; hh ==>[rassociator _ _ _] ff ;; (gg ;; hh)
      := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))) _ _ _ _ _ _ _ w _ _ _ ff gg hh.
    
    Definition disp_lassociator
               {a b c d : C} {f : a --> b} {g : b --> c} {h : c --> d}
               {w : D a} {x : D b} {y : D c} {z : D d}
               (ff : w -->[f] x) (gg : x -->[g] y) (hh : y -->[h] z)
      : ff ;; (gg ;; hh) ==>[lassociator _ _ _] (ff ;; gg) ;; hh
      := pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))) _ _ _ _ _ _ _ w _ _ _ ff gg hh.

    Definition disp_vcomp2
               {a b : C} {f g h : a --> b}
               {r : f ==> g} {s : g ==> h}
               {x : D a} {y : D b}
               {ff : x -->[f] y} {gg : x -->[g] y} {hh : x -->[h] y}
      : ff ==>[r] gg  →  gg ==>[s] hh  →  ff ==>[r • s] hh
      := λ rr ss,  pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D))))))))
                       _ _ _ _ _ _ _ _ _ _ _ _ rr ss.

    Definition disp_lwhisker
               {a b c : C} {f : a --> b} {g1 g2 : b --> c}
               {r : g1 ==> g2}
               {x : D a} {y : D b} {z : D c}
               (ff : x -->[f] y) {gg1 : y -->[g1] z} {gg2 : y -->[g2] z}
      : gg1 ==>[r] gg2  →  ff ;; gg1  ==>[f ◃ r] ff ;; gg2
      := λ rr, pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))
                   _ _ _ _ _ _ _ _ _ _ _ _ _ rr.

    Definition disp_rwhisker
               {a b c : C} {f1 f2 : a --> b} {g : b --> c}
               {r : f1 ==> f2}
               {x : D a} {y : D b} {z : D c}
               {ff1 : x -->[f1] y} {ff2 : x -->[f2] y} (gg : y -->[g] z)
      : ff1 ==>[r] ff2 → ff1 ;; gg ==>[r ▹ g] ff2 ;; gg
      := λ rr, pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 D)))))))))
                   _ _ _ _ _ _ _ _ _ _ _ _ _ rr.
    
  End disp_wild_cat_ops_projections.

  Local Notation "rr •• ss" := (disp_vcomp2 rr ss) (at level 60).
  Local Notation "ff ◃◃ rr" := (disp_lwhisker ff rr) (at level 60).
  Local Notation "rr ▹▹ gg" := (disp_rwhisker gg rr) (at level 60).

  (* Total wild categories *)

  Section total_wild_cat.
    Variable D : disp_wild_cat.

    Definition total_wild_cat_1_data : precategory_data
      := total_category_ob_mor D ,, total_category_id_comp D.

    Definition total_wild_cat_cell_struct : wild_cat_2cell_struct (total_category_ob_mor D)
      := λ a b f g, ∑ η : pr1 f ==> pr1 g, pr2 f ==>[η] pr2 g.

    Definition total_wild_cat_1_id_comp_cells : wild_cat_1_id_comp_cells
      := (total_wild_cat_1_data,, total_wild_cat_cell_struct).

    Definition total_wild_cat_2_id_comp_struct
      : wild_cat_2_id_comp_struct total_wild_cat_1_id_comp_cells.
    Proof.
      repeat split; cbn; unfold total_wild_cat_cell_struct.
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

    Definition total_wild_cat : wild_cat
      := _ ,, total_wild_cat_2_id_comp_struct.
  End total_wild_cat.
End disp_wild_cat.

Arguments disp_wild_cat_1_id_comp_cells _ : clear implicits.
Arguments disp_wild_cat _ : clear implicits.

Module Notations.
  Export Bicat.Notations.

  Notation "f' ==>[ x ] g'" := (disp_2cells x f' g') (at level 60).
  Notation "f' <==[ x ] g'" := (disp_2cells x g' f') (at level 60, only parsing).
  Notation "rr •• ss" := (disp_vcomp2 rr ss) (at level 60).
  Notation "ff ◃◃ rr" := (disp_lwhisker ff rr) (at level 60).
  Notation "rr ▹▹ gg" := (disp_rwhisker gg rr) (at level 60).
End Notations.
