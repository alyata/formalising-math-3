import syntax
import typing_relation
import semantics

import category_theory.closed.cartesian
import category_theory.limits.shapes.binary_products

namespace term_equality

open term type typing_relation
open category_theory category_theory.limits

variables {con gnd fv : Type} [fvar fv] [const con gnd]
variables {con_type : con β type gnd}

variables {π : Type} [category π] 
          [limits.has_finite_products π] [cartesian_closed π]

inductive beta_eta_eq (con_type : con β type gnd)
: env gnd fv β term gnd con fv β term gnd con fv β type gnd β Type
| Refl : β {Ξ t A},
(Ξ β© t β· A)
-----------------------
β beta_eta_eq Ξ t t A 

| Symm : β {Ξ t1 t2 A},
beta_eta_eq Ξ t1 t2 A
------------------------
β beta_eta_eq Ξ t2 t1 A 

| Trans : β {Ξ t1 t2 t3 A},
beta_eta_eq Ξ t1 t2 A β beta_eta_eq Ξ t2 t3 A
---------------------------------------------
β beta_eta_eq Ξ t1 t3 A

| Beta_fun : β {Ξ : env gnd fv} {t1 t2 : term gnd con fv} {A B},
(Ξ β© (Ξ A. t1) β· (A β B))
β (Ξ β© t2 β· A)
----------------------------------------------------------
β beta_eta_eq Ξ ((Ξ A. t1) β¬ t2) (open_term t2 0 t1) B

| Beta_prod_fst : β {Ξ t1 t2 A B},
(Ξ β© t1 β· A) β (Ξ β© t2 β· B)
---------------------------------------------------
β beta_eta_eq Ξ (fst βͺt1, t2β«) t1 A

| Beta_prod_snd : β {Ξ t1 t2 A B},
(Ξ β© t1 β· A) β (Ξ β© t2 β· B)
---------------------------------------------------
β beta_eta_eq Ξ (snd βͺt1, t2β«) t2 B

| Eta_fun : β {Ξ t A B},
(Ξ β© t β· (A β B))
-----------------------------------------
β beta_eta_eq Ξ t (Ξ A. (t β¬ β0β)) (A β B) 

| Eta_prod : β {Ξ t A B},
(Ξ β© t β· (A β B))
----------------------------------------
β beta_eta_eq Ξ t βͺfst t, snd tβ« (A β B)  

| Eta_unit : β {Ξ t},
(Ξ β© t β· unit)
--------------------------
β beta_eta_eq Ξ t βͺβ« unit

| Cong_lam : β {Ξ : env gnd fv} {t t' A B},
(β x β free_vars t βͺ Ξ.keys.to_finset, 
  beta_eta_eq (β¨x, Aβ© :: Ξ) (open_var x 0 t) (open_var x 0 t') B)
----------------------------------------------------------------
β beta_eta_eq Ξ (Ξ A. t) (Ξ A. t') (A β B)

| Cong_app : β {Ξ t1 t2 t1' t2' A B},
beta_eta_eq Ξ t1 t1' (A β B) β beta_eta_eq Ξ t2 t2' A
-----------------------------------------------------
β beta_eta_eq Ξ (t1 β¬ t2) (t1' β¬ t2') B

| Cong_fst : β {Ξ t t' A B},
beta_eta_eq Ξ t t' (A β B)
----------------------------------
β beta_eta_eq Ξ (fst t) (fst t') A

| Cong_snd : β {Ξ t t' A B},
beta_eta_eq Ξ t t' (A β B)
----------------------------------
β beta_eta_eq Ξ (snd t) (snd t') B

| Cong_pair : β {Ξ t1 t2 t1' t2' A B},
beta_eta_eq Ξ t1 t1' A β beta_eta_eq Ξ t2 t2' B
-----------------------------------------------
β beta_eta_eq Ξ βͺt1, t2β« βͺt1', t2'β« (A β B)

lemma has_type_of_beta_eta_eq {Ξ : env gnd fv} 
{t1 t2 : term gnd con fv} {A : type gnd} 
(heq : beta_eta_eq con_type Ξ t1 t2 A)
: (Ξ β© t1 β· A) Γ (Ξ β© t2 β· A) :=
begin
  induction' heq generalizing Ξ t1 t2 A,
  case term_equality.beta_eta_eq.Refl : Ξ t A h
  { exact β¨h, hβ© },
  case term_equality.beta_eta_eq.Symm : Ξ t1 t2 A rec ih
  { exact prod.swap ih },
  case term_equality.beta_eta_eq.Trans : Ξ t1 t2 t3 A rec1 rec2 ih1 ih2
  { exact β¨ih1.fst, ih2.sndβ© },
  case term_equality.beta_eta_eq.Beta_fun : Ξ t1 t2 A B h1 h2
  { refine β¨h1.App h2, _β©,
    cases' h1,
    have hfresh := fvar.hfresh (free_vars t βͺ (list.keys Ξ).to_finset),
    set x := fvar.fresh (free_vars t βͺ (list.keys Ξ).to_finset),
    specialize h1 x hfresh,
    simp only [not_or_distrib, finset.mem_union, list.mem_to_finset] at hfresh,
    rw open_term_eq_subst_of_open_var t t2 x 0 hfresh.left,
    exact subst_preserves_type h1 h2
  },
  case term_equality.beta_eta_eq.Beta_prod_fst : Ξ t1 t2 A B h1 h2
  { exact β¨(h1.Pair h2).Fst, h1β© },
  case term_equality.beta_eta_eq.Beta_prod_snd : Ξ t1 t2 A B h1 h2
  { exact β¨(h1.Pair h2).Snd, h2β© },
  case term_equality.beta_eta_eq.Eta_fun : Ξ t A B h
  { refine β¨h, _β©,
    apply has_type.Abs,
    intros x hx,
    simp only [open_var, open_term, eq_self_iff_true, if_true],
    apply has_type.App, rotate 2,
    exact A,
    sorry,
    /- from h we can derive that t is locally closed, so open_term does nothing -/
    /- then, we need weakening... -/
    apply has_type.Fvar,
    apply ok.Cons (ok_of_has_type h),
    simp only [not_or_distrib, finset.mem_union, list.mem_to_finset] at hx,
    exact hx.right
    },
  case term_equality.beta_eta_eq.Eta_prod : Ξ t A1 A2 h
  { exact β¨h, h.Fst.Pair h.Sndβ© },
  case term_equality.beta_eta_eq.Eta_unit : Ξ t1 h
  { exact β¨h, has_type.Unit (ok_of_has_type h)β© },
  case term_equality.beta_eta_eq.Cong_lam : Ξ t1 t2 A1 A2 heq ih
  { let ih1 := Ξ» x hx, (ih x hx).fst,
    -- to make this useable, we need hx to be x β t2, not x β t1
    -- but we need x β t1 to use ih.
    -- I thought I could use free_vars_subset_env, but I realize there's no
    -- proof of Ξ β© open_var x 0 t β· A2 I can use!
    -- this would be doable if I had the cofinite quantification
    -- but that's not possible in lean 3
    let ih2 : Ξ  (x : fv), x β free_vars t2 βͺ (list.keys Ξ).to_finset β
              (β¨x, A1β© :: Ξ β© open_var x 0 t2 β· A2) := Ξ» x hx, by {
      rw finset.not_mem_union at hx,
      sorry
    },
    exact β¨has_type.Abs ih1, has_type.Abs ih2β©
  },
  case term_equality.beta_eta_eq.Cong_app : Ξ t1 t2 t1' t2' A1 A2 heq heq_1 ih1 ih2
  { exact β¨ih1.fst.App ih2.fst, ih1.snd.App ih2.sndβ© },
  case term_equality.beta_eta_eq.Cong_fst : Ξ t1 t2 A B heq ih
  { exact β¨ih.fst.Fst, ih.snd.Fstβ© },
  case term_equality.beta_eta_eq.Cong_snd : Ξ t1 t2 A A_1 heq ih
  { exact β¨ih.fst.Snd, ih.snd.Sndβ© },
  case term_equality.beta_eta_eq.Cong_pair : Ξ t1 t2 t1' t2' A1 A2 heq heq_1 ih1 ih2
  { exact β¨ih1.fst.Pair ih2.fst, ih1.snd.Pair ih2.sndβ© }
end

universes u v
variables {C : Type u} [category.{v} C]
lemma comp_cong {X Y Z : C} {f1 f2 : X βΆ Y} {g : Y βΆ Z} (h : f1 = f2)
: f1 β« g = f2 β« g :=
begin
  rw h
end

theorem soundness {M : model gnd con π} 
{Ξ : env gnd fv} {t1 t2 : term gnd con fv} {A : type gnd}
(h1 : Ξ β© t1 β· A) (h2 : Ξ β© t2 β· A)
(heq : beta_eta_eq con_type Ξ t1 t2 A)
: (Mβ¦h1β§) = (Mβ¦h2β§) :=
begin
  induction' heq generalizing Ξ t1 t2 A,
  case beta_eta_eq.Refl : Ξ t A { rw deriv_unicity h1 h2 },
  case term_equality.beta_eta_eq.Symm : Ξ t2 t1 A rec ih {
    symmetry, exact ih h2 h1,
  },
  case term_equality.beta_eta_eq.Trans : Ξ t1 t2 t3 A rec1 rec2 ih1 ih2 {
    rename [h2 β h3],
    obtain β¨_, h2β© := has_type_of_beta_eta_eq rec1,
    exact trans (ih1 h1 h2) (ih2 h2 h3)
  },
  case term_equality.beta_eta_eq.Beta_fun : Ξ t1 t2 A A_1 x x_1
  { -- we need to talk about semantics of substitution
    -- not enough time to do that =(
    admit  },
  case term_equality.beta_eta_eq.Beta_prod_fst : Ξ t1 t1_1 A B x x_1
  { cases' h1, cases h1, rw deriv_unicity h2 h1_αΎ°, simp [eval_has_type] },
  case term_equality.beta_eta_eq.Beta_prod_snd : Ξ t1 t2 A1 A2 x x_1
  { cases' h1, cases h1, rw deriv_unicity h2 h1_αΎ°_1, simp [eval_has_type] },
  case term_equality.beta_eta_eq.Eta_fun : Ξ t A A_1 x
  { -- need semantics of weakening...
    admit },
  case term_equality.beta_eta_eq.Eta_prod : Ξ t A1 A2 x
  { -- Idea: Due to deriv unicity, we can say that
    -- Mβ¦h2_left : Ξ β© fst t β· A1β§ = Οβ β Mβ¦h1 : Ξ β© t β· A1 β A2β§ 
    -- Mβ¦h2_right : Ξ β© snd t β· A1β§ = Οβ β Mβ¦h1 : Ξ β© t β· A1 β A2β§
    -- so Mβ¦h2β§ = β¨Οβ β Mβ¦h1β§, Οβ β Mβ¦h1β§β© = Mβ¦h1β§ by the universal 
    -- property of products.
    cases' h2, cases h2, cases h2_1,
    have := type_unicity h1 h2_αΎ°, simp at this, subst this,
    have := type_unicity h1 h2_1_αΎ°, simp at this, subst this,
    rw deriv_unicity h2_αΎ° h1,
    rw deriv_unicity h2_1_αΎ° h1,
    ext; simp [eval_has_type]
  },
  case term_equality.beta_eta_eq.Eta_unit : Ξ t1 x
  { -- Mβ¦h1β§ and Mβ¦h2β§ are both arrows from Mβ¦Ξβ§ to the terminal object,
    -- so they must be equal by the uniqueness condition. 
    have := category_theory.limits.unique_to_terminal (M.Gβ¦Ξβ§),
    exact trans (this.uniq (Mβ¦h1β§)) (symm (this.uniq (Mβ¦h2β§))),
  },
  case term_equality.beta_eta_eq.Cong_lam : Ξ t1 t2 A A_1 heq ih
  { cases h2, cases h1, 
    simp [eval_has_type],
    -- this is the same issue as line 140: one hypothesis is asking for free_vars t1
    -- the other is asking for free_vars t2.
    sorry
  },
  case term_equality.beta_eta_eq.Cong_app : Ξ t1 t2 t1' t2' A1 A2 heq heq' ih ih'
  { -- Idea: 
    -- the goal is essentially to show 
    -- eval β β¨Mβ¦h1.leftβ§, Mβ¦h1.rightβ§β© = eval β β¨Mβ¦h2.leftβ§, Mβ¦h2.rightβ§β©
    -- By congruence, and by the universal property of products,
    -- This is the same as showing Mβ¦h1.leftβ§ = Mβ¦h2.leftβ§ and Mβ¦h1.rightβ§ = Mβ¦h2.rightβ§
    -- But that's exactly what we have with the inductive hypotheses.
    cases' h2, cases' h1,
    obtain β¨h1_1', h2_1'β© := has_type_of_beta_eta_eq heq',
    have := type_unicity h1_1 h1_1', subst this,
    have := type_unicity h2_1 h2_1', subst this,
    specialize ih h1 h2,
    specialize ih' h1_1 h2_1,
    apply comp_cong,
    ext; simp only [prod.lift_fst, prod.lift_snd],
    exact ih',
    exact ih, 
  },
  case term_equality.beta_eta_eq.Cong_fst : Ξ t1 t2 A B heq ih
  { -- showing Οβ β Mβ¦h1β§ = Οβ β Mβ¦h2β§ is the same as showing Mβ¦h1β§ = Mβ¦h2β§
    -- by congruence
    cases' h1, cases' h2,
    obtain β¨h1', h2'β© := has_type_of_beta_eta_eq heq,
    have := type_unicity h1 h1', simp at this, subst this,
    have := type_unicity h2 h2', simp at this, subst this,
    apply comp_cong,
    exact ih h1 h2,
  },
  case term_equality.beta_eta_eq.Cong_snd : Ξ t1 t2 A A_1 heq ih
  { -- similar to Cong_fst
    cases' h1, cases' h2,
    obtain β¨h1', h2'β© := has_type_of_beta_eta_eq heq,
    have := type_unicity h1 h1', simp at this, subst this,
    have := type_unicity h2 h2', simp at this, subst this,
    apply comp_cong,
    exact ih h1 h2,
  },
  case term_equality.beta_eta_eq.Cong_pair : Ξ t1 t2 t1' t2' A1 A2 heq heq' ih ih'
  { -- this uses the universal property of products to decompose equality on
    -- products, as we did in Cong_app.
    cases' h1, cases h2, --sometimes `cases'` just doesn't work even though `cases` does
    ext; simp only [eval_has_type, prod.lift_fst, prod.lift_snd], 
    exact ih h1 h2_αΎ°,
    exact ih' h1_1 h2_αΎ°_1
  }
end


end term_equality