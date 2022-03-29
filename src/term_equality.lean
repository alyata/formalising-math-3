import syntax
import typing_relation
import semantics

import category_theory.closed.cartesian
import category_theory.limits.shapes.binary_products

namespace term_equality

open term type typing_relation
open category_theory category_theory.limits

variables {con gnd fv : Type} [fvar fv] [const con gnd]
variables {con_type : con → type gnd}

variables {𝓒 : Type} [category 𝓒] 
          [limits.has_finite_products 𝓒] [cartesian_closed 𝓒]

inductive beta_eta_eq (con_type : con → type gnd)
: env gnd fv → term gnd con fv → term gnd con fv → type gnd → Type
| Refl : ∀ {Γ t A},
(Γ ⊩ t ∷ A)
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

| Beta_fun : ∀ {Γ : env gnd fv} {t1 t2 : term gnd con fv} {A B},
(Γ ⊩ (Λ A. t1) ∷ (A ⊃ B))
→ (Γ ⊩ t2 ∷ A)
----------------------------------------------------------
→ beta_eta_eq Γ ((Λ A. t1) ⬝ t2) (open_term t2 0 t1) B

| Beta_prod_fst : ∀ {Γ t1 t2 A B},
(Γ ⊩ t1 ∷ A) → (Γ ⊩ t2 ∷ B)
---------------------------------------------------
→ beta_eta_eq Γ (fst ⟪t1, t2⟫) t1 A

| Beta_prod_snd : ∀ {Γ t1 t2 A B},
(Γ ⊩ t1 ∷ A) → (Γ ⊩ t2 ∷ B)
---------------------------------------------------
→ beta_eta_eq Γ (snd ⟪t1, t2⟫) t2 B

| Eta_fun : ∀ {Γ t A B},
(Γ ⊩ t ∷ (A ⊃ B))
-----------------------------------------
→ beta_eta_eq Γ t (Λ A. (t ⬝ ⌈0⌉)) (A ⊃ B) 

| Eta_prod : ∀ {Γ t A B},
(Γ ⊩ t ∷ (A ∏ B))
----------------------------------------
→ beta_eta_eq Γ t ⟪fst t, snd t⟫ (A ∏ B)  

| Eta_unit : ∀ {Γ t},
(Γ ⊩ t ∷ unit)
--------------------------
→ beta_eta_eq Γ t ⟪⟫ unit

| Cong_lam : ∀ {Γ : env gnd fv} {t t' A B},
∀ x ∉ free_vars t ∪ Γ.keys.to_finset, 
  beta_eta_eq (⟨x, A⟩ :: Γ) (open_var x 0 t) (open_var x 0 t') B
----------------------------------------------------------------
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

lemma has_type_of_beta_eta_eq {Γ : env gnd fv} 
{t1 t2 : lc_term gnd con fv} {A : type gnd} 
(heq : beta_eta_eq con_type Γ t1.val t2.val A)
: (Γ ⊩ t1.val ∷ A) × (Γ ⊩ t2.val ∷ A) :=
begin
  cases t1,
  cases t2,
  induction heq,
  case term_equality.beta_eta_eq.Refl : Γ t A h
  { exact ⟨h, h⟩ },
  case term_equality.beta_eta_eq.Symm : Γ t1 t2 A rec ih
  { exact prod.swap ih },
  case term_equality.beta_eta_eq.Trans : Γ t1 t2 t3 A rec1 rec2 ih1 ih2
  { exact ⟨ih1.fst, ih2.snd⟩ },
  case term_equality.beta_eta_eq.Beta_fun : Γ t1 t2 A B h1 h2
  { exact ⟨h1.App h2, sorry /- need substitution lemma for this -/⟩ },
  case term_equality.beta_eta_eq.Beta_prod_fst : Γ t1 t2 A B h1 h2
  { exact ⟨(h1.Pair h2).Fst, h1⟩ },
  case term_equality.beta_eta_eq.Beta_prod_snd : Γ t1 t2 A B h1 h2
  { exact ⟨(h1.Pair h2).Snd, h2⟩ },
  case term_equality.beta_eta_eq.Eta_fun : Γ t A B h
  { exact ⟨h, by {apply has_type.Lam, 
    intros x hx,
    simp only [open_var, open_term, eq_self_iff_true, if_true],
    apply has_type.App,
    sorry, sorry, sorry
    /-actually, we need weakining... 
    should be easuer now with locally nameless representation -/ }⟩ },
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

theorem soundness {M : model gnd con 𝓒} 
{Γ : env gnd fv} {t1 t2 : lc_term gnd con fv} {A : type gnd}
(h1 : Γ ⊩ t1.val ∷ A) (h2 : Γ ⊩ t2.val ∷ A)
(heq : beta_eta_eq con_type Γ t1.val t2.val A)
: (M⟦h1⟧) = (M⟦h2⟧) :=
begin
  cases t1,
  cases t2,
  simp at heq,
  induction heq,
  case beta_eta_eq.Refl : Γ t A { rw deriv_unicity ⟨t, t1_property⟩ h1 h2 },
  case term_equality.beta_eta_eq.Symm : Γ t2 t1 A rec ih {
    symmetry, exact ih t2_property h2 t1_property h1, 
  },
  case term_equality.beta_eta_eq.Trans : Γ t1 t2 t3 A rec1 rec2 ih1 ih2 {
    rename [h2 → h3, t2_property → t3_property],
    obtain ⟨_, h2⟩ := has_type_of_beta_eta_eq rec1,
    -- we need to prove reduction preserves local closure here to prove lc t2
    -- exact trans (ih1 t1_property h1 t2_property h2) (ih2 t2_property h2 t3_property h3)
    sorry
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