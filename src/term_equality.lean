import syntax
import typing_relation
import semantics

import category_theory.closed.cartesian
import category_theory.limits.shapes.binary_products

namespace term_equality

open term type typing_relation
open category_theory category_theory.limits

variables {con gnd : Type} {con_type : con → type gnd}

variables {𝓒 : Type} [category 𝓒] 
          [limits.has_finite_products 𝓒] [cartesian_closed 𝓒]

inductive beta_eta_eq (con_type : con → type gnd)
: env gnd → term gnd con → term gnd con → type gnd → Type
| Refl : ∀ {Γ t A},
has_type con_type Γ t A
-----------------------
→ beta_eta_eq Γ t t A 

| Symm : ∀ {Γ t1 t2 A},
beta_eta_eq Γ t1 t2 A
------------------------
→ beta_eta_eq Γ t2 t1 A 

| Trans : ∀ {Γ t1 t2 t3 A},
beta_eta_eq Γ t1 t2 A → beta_eta_eq Γ t2 t3 A
---------------------------------------------
→ beta_eta_eq Γ t1 t3 A

| Beta_fun : ∀ {Γ t1 t2 A B},
has_type con_type (A :: Γ) t1 B → has_type con_type Γ t2 A
----------------------------------------------------------
→ beta_eta_eq Γ ((Λ A. t1) ⬝ t2) (substitute t2 0 t1) B

| Beta_prod_fst : ∀ {Γ t1 t2 A B},
has_type con_type Γ t1 A → has_type con_type Γ t2 B
---------------------------------------------------
→ beta_eta_eq Γ (fst ⟪t1, t2⟫) t1 A

| Beta_prod_snd : ∀ {Γ t1 t2 A B},
has_type con_type Γ t1 A → has_type con_type Γ t2 B
---------------------------------------------------
→ beta_eta_eq Γ (snd ⟪t1, t2⟫) t2 B

| Eta_fun : ∀ {Γ t A B},
has_type con_type Γ t (A ⊃ B)
-----------------------------------------
→ beta_eta_eq Γ t (Λ A. (t ⬝ ⌈0⌉)) (A ⊃ B) 

| Eta_prod : ∀ {Γ t A B},
has_type con_type Γ t (A ∏ B)
----------------------------------------
→ beta_eta_eq Γ t ⟪fst t, snd t⟫ (A ∏ B)  

| Eta_unit : ∀ {Γ t},
has_type con_type Γ t unit
--------------------------
→ beta_eta_eq Γ t ⟪⟫ unit

| Cong_lam : ∀ {Γ t t' A B},
beta_eta_eq (A :: Γ) t t' B
------------------------------------------
→ beta_eta_eq Γ (Λ A. t) (Λ A. t') (A ⊃ B)

| Cong_app : ∀ {Γ t1 t2 t1' t2' A B},
beta_eta_eq Γ t1 t1' (A ⊃ B) → beta_eta_eq Γ t2 t2' A
-----------------------------------------------------
→ beta_eta_eq Γ (t1 ⬝ t2) (t1' ⬝ t2') B

| Cong_fst : ∀ {Γ t t' A B},
beta_eta_eq Γ t t' (A ∏ B)
----------------------------------
→ beta_eta_eq Γ (fst t) (fst t') A

| Cong_snd : ∀ {Γ t t' A B},
beta_eta_eq Γ t t' (A ∏ B)
----------------------------------
→ beta_eta_eq Γ (snd t) (snd t') B

| Cong_pair : ∀ {Γ t1 t2 t1' t2' A B},
beta_eta_eq Γ t1 t1' A → beta_eta_eq Γ t2 t2' B
-----------------------------------------------
→ beta_eta_eq Γ ⟪t1, t2⟫ ⟪t1', t2'⟫ (A ∏ B)

lemma has_type_of_beta_eta_eq {Γ : env gnd} 
{t1 t2 : term gnd con} {A : type gnd} (heq : beta_eta_eq con_type Γ t1 t2 A)
: has_type con_type Γ t1 A × has_type con_type Γ t2 A :=
begin
  induction heq,
  case term_equality.beta_eta_eq.Refl : Γ t A h
  { exact ⟨h, h⟩ },
  case term_equality.beta_eta_eq.Symm : Γ t1 t2 A rec ih
  { exact prod.swap ih },
  case term_equality.beta_eta_eq.Trans : Γ t1 t2 t3 A rec1 rec2 ih1 ih2
  { exact ⟨ih1.fst, ih2.snd⟩ },
  case term_equality.beta_eta_eq.Beta_fun : Γ t1 t2 A B h1 h2
  { exact ⟨h1.Lam.App h2, sorry /- need substitution lemma for this -/⟩ },
  case term_equality.beta_eta_eq.Beta_prod_fst : Γ t1 t2 A B h1 h2
  { exact ⟨(h1.Pair h2).Fst, h1⟩ },
  case term_equality.beta_eta_eq.Beta_prod_snd : Γ t1 t2 A B h1 h2
  { exact ⟨(h1.Pair h2).Snd, h2⟩ },
  case term_equality.beta_eta_eq.Eta_fun : Γ t A B h
  { exact ⟨h, by {apply has_type.Lam, apply has_type.App, sorry, sorry,     
    sorry
    /-actually, we need weakining... 
    hard to do with pure de bruijn indices -/ }⟩ },
  case term_equality.beta_eta_eq.Eta_prod : heq_Γ heq_t heq_A heq_B heq_ᾰ
  { admit },
  case term_equality.beta_eta_eq.Eta_unit : heq_Γ heq_t heq_ᾰ
  { admit },
  case term_equality.beta_eta_eq.Cong_lam : heq_Γ heq_t heq_t' heq_A heq_B heq_ᾰ heq_ih
  { admit },
  case term_equality.beta_eta_eq.Cong_app : heq_Γ heq_t1 heq_t2 heq_t1' heq_t2' heq_A heq_B heq_ᾰ heq_ᾰ_1 heq_ih_ᾰ heq_ih_ᾰ_1
  { admit },
  case term_equality.beta_eta_eq.Cong_fst : heq_Γ heq_t heq_t' heq_A heq_B heq_ᾰ heq_ih
  { admit },
  case term_equality.beta_eta_eq.Cong_snd : heq_Γ heq_t heq_t' heq_A heq_B heq_ᾰ heq_ih
  { admit },
  case term_equality.beta_eta_eq.Cong_pair : heq_Γ heq_t1 heq_t2 heq_t1' heq_t2' heq_A heq_B heq_ᾰ heq_ᾰ_1 heq_ih_ᾰ heq_ih_ᾰ_1
  { admit }
end

theorem soundness {M : gnd → 𝓒} {Γ : env gnd} {t1 t2 : term gnd con} 
{A : type gnd} {con_eval : Π c : con, ⊤_𝓒 ⟶ M⟦con_type c⟧} 
(h1 : has_type con_type Γ t1 A) (h2 : has_type con_type Γ t2 A)
(heq : beta_eta_eq con_type Γ t1 t2 A)
: eval_has_type M con_eval h1 = eval_has_type M con_eval h2 :=
begin
  induction heq,
  case beta_eta_eq.Refl : Γ t A _ { rw deriv_unicity h1 h2 },
  case term_equality.beta_eta_eq.Symm : Γ t1 t2 A rec ih {
    symmetry, exact ih h2 h1 
  },
  case term_equality.beta_eta_eq.Trans : Γ t1 t2 t3 A rec1 rec2 ih1 ih2 {
    rename h2 → h3,
    obtain ⟨_, h2⟩ := has_type_of_beta_eta_eq rec1,
    exact trans (ih1 h1 h2) (ih2 h2 h3)
  },
  case term_equality.beta_eta_eq.Beta_fun : heq_Γ heq_t1 heq_t2 heq_A heq_B heq_ᾰ heq_ᾰ_1
  { admit },
  case term_equality.beta_eta_eq.Beta_prod_fst : heq_Γ heq_t1 heq_t2 heq_A heq_B heq_ᾰ heq_ᾰ_1
  { admit },
  case term_equality.beta_eta_eq.Beta_prod_snd : heq_Γ heq_t1 heq_t2 heq_A heq_B heq_ᾰ heq_ᾰ_1
  { admit },
  case term_equality.beta_eta_eq.Eta_fun : heq_Γ heq_t heq_A heq_B heq_ᾰ
  { admit },
  case term_equality.beta_eta_eq.Eta_prod : heq_Γ heq_t heq_A heq_B heq_ᾰ
  { admit },
  case term_equality.beta_eta_eq.Eta_unit : heq_Γ heq_t heq_ᾰ
  { admit },
  case term_equality.beta_eta_eq.Cong_lam : heq_Γ heq_t heq_t' heq_A heq_B heq_ᾰ heq_ih
  { admit },
  case term_equality.beta_eta_eq.Cong_app : heq_Γ heq_t1 heq_t2 heq_t1' heq_t2' heq_A heq_B heq_ᾰ heq_ᾰ_1 heq_ih_ᾰ heq_ih_ᾰ_1
  { admit },
  case term_equality.beta_eta_eq.Cong_fst : heq_Γ heq_t heq_t' heq_A heq_B heq_ᾰ heq_ih
  { admit },
  case term_equality.beta_eta_eq.Cong_snd : heq_Γ heq_t heq_t' heq_A heq_B heq_ᾰ heq_ih
  { admit },
  case term_equality.beta_eta_eq.Cong_pair : heq_Γ heq_t1 heq_t2 heq_t1' heq_t2' heq_A heq_B heq_ᾰ heq_ᾰ_1 heq_ih_ᾰ heq_ih_ᾰ_1
  { admit }
end


end term_equality